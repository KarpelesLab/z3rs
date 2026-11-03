//! `(simplify t)` through z3's theory rewriter ([`crate::rewriter::th_simp`]):
//! the term is rebuilt in the rewriter's own arena with the source's
//! operators (no lowering), simplified with z3's default rules and printed
//! with z3's layout. Terms outside the supported fragment (Boolean,
//! arithmetic and uninterpreted symbols over those and declared sorts) are
//! left to the general `simplify` path.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::{String, ToString};
use alloc::vec::Vec;

use super::super::smt2_pp::{PpNode, pp_term};
use super::{Context, SExpr, parse_bv_literal, parse_numeral};
use crate::ast::AstId;
use crate::rewriter::th_simp::{BvOp, Op, Simp, Sort, T};
use crate::util::symbol::smt2_symbol;
use puremp::Int;

/// The front end's state while building one term.
struct Builder {
    s: Simp,
    /// `let` scopes, innermost last.
    scopes: Vec<BTreeMap<String, T>>,
}

impl Context {
    /// `(simplify t)` in z3's spelling when `t` lies in the fragment the
    /// theory rewriter port covers; `None` otherwise.
    pub(super) fn simplify_th(&self, t: &SExpr) -> Option<String> {
        if self
            .params
            .keys()
            .any(|k| k.starts_with("pp.") || k.starts_with("rewriter."))
        {
            return None;
        }
        let mut b = Builder {
            s: Simp::new(),
            scopes: Vec::new(),
        };
        let root = self.th_term(&mut b, t)?;
        let r = b.s.simplify(root);
        Some(render(&b.s, r))
    }

    /// The rewriter sort of the z3rs sort `s`, if supported.
    fn th_sort(&self, s: AstId) -> Option<Sort> {
        if self.m.is_bool_sort(s) {
            return Some(Sort::Bool);
        }
        if self.m.is_arith_sort(s) {
            return Some(if self.m.is_int_sort(s) {
                Sort::Int
            } else {
                Sort::Real
            });
        }
        if let Some(w) = self.m.bv_sort_width(s) {
            return Some(Sort::Bv(w));
        }
        if self.declared_sorts.contains(&s) {
            return Some(Sort::User(alloc::format!("{}", self.m.sort(s)?.name)));
        }
        None
    }

    /// Build `e` in the rewriter's arena.
    fn th_term(&self, b: &mut Builder, e: &SExpr) -> Option<T> {
        match e {
            SExpr::Atom(a) => self.th_atom(b, a),
            SExpr::List(l) if !l.is_empty() => {
                // `(_ bvN w)`: a bit-vector literal.
                if let [SExpr::Atom(u), SExpr::Atom(bvn), SExpr::Atom(w)] = l.as_slice()
                    && u == "_"
                    && let Some(digits) = bvn.strip_prefix("bv")
                {
                    let v = Int::from_str_radix(digits, 10).ok()?;
                    let w: u32 = w.parse().ok()?;
                    if w == 0 {
                        return None;
                    }
                    return Some(b.s.mk_bv_num(&v, w));
                }
                // `((_ extract h l) x)` and the other indexed operators.
                if let SExpr::List(idx) = &l[0] {
                    let op = th_indexed(idx)?;
                    if l.len() != 2 {
                        return None;
                    }
                    let x = self.th_term(b, &l[1])?;
                    let Sort::Bv(w) = *b.s.sort(x) else {
                        return None;
                    };
                    if let Op::Extract(h, lo) = op
                        && (h < lo || h >= w)
                    {
                        return None;
                    }
                    if matches!(op, Op::Repeat(0)) {
                        return None;
                    }
                    return Some(b.s.mk(op, alloc::vec![x]));
                }
                let SExpr::Atom(head) = &l[0] else {
                    return None;
                };
                if head == "let" {
                    return self.th_let(b, l);
                }
                if l.len() < 2 {
                    return None;
                }
                let mut args = Vec::with_capacity(l.len() - 1);
                for x in &l[1..] {
                    args.push(self.th_term(b, x)?);
                }
                self.th_app(b, head, args)
            }
            _ => None,
        }
    }

    /// `(let ((x t) …) body)`.
    fn th_let(&self, b: &mut Builder, l: &[SExpr]) -> Option<T> {
        if l.len() != 3 {
            return None;
        }
        let SExpr::List(binds) = &l[1] else {
            return None;
        };
        let mut scope = BTreeMap::new();
        for bind in binds {
            let SExpr::List(p) = bind else {
                return None;
            };
            let [SExpr::Atom(name), t] = p.as_slice() else {
                return None;
            };
            let v = self.th_term(b, t)?;
            scope.insert(name.clone(), v);
        }
        b.scopes.push(scope);
        let r = self.th_term(b, &l[2]);
        b.scopes.pop();
        r
    }

    fn th_atom(&self, b: &mut Builder, a: &str) -> Option<T> {
        for sc in b.scopes.iter().rev() {
            if let Some(&t) = sc.get(a) {
                return Some(t);
            }
        }
        match a {
            "true" => return Some(b.s.mk_true()),
            "false" => return Some(b.s.mk_false()),
            _ => {}
        }
        if let Some((v, w)) = parse_bv_literal(a) {
            return Some(b.s.mk_bv_num(&v, w));
        }
        if let Some((r, is_int)) = parse_numeral(a) {
            if r.is_negative() {
                return None;
            }
            return Some(b.s.mk_num(r, is_int));
        }
        if self.macros.contains_key(a) || self.named_terms.iter().any(|(n, _, _)| n == a) {
            return None;
        }
        let d = *self.funcs.get(a)?;
        let fd = self.m.func_decl(d)?;
        if !fd.domain.is_empty() || fd.info.family_id != crate::ast::NULL_FAMILY_ID {
            return None;
        }
        let s = self.th_sort(fd.range)?;
        Some(b.s.mk_sorted(Op::Uf(a.to_string()), Vec::new(), s))
    }

    /// An application of `head` to the built `args`.
    fn th_app(&self, b: &mut Builder, head: &str, args: Vec<T>) -> Option<T> {
        let s = &mut b.s;
        let n = args.len();
        let all = |s: &Simp, p: &dyn Fn(&Sort) -> bool| args.iter().all(|&a| p(s.sort(a)));
        let bools = all(s, &|x| *x == Sort::Bool);
        let arith = all(s, &|x| x.is_arith_sort());
        // Mixed Int/Real arithmetic: z3 coerces the integer arguments.
        let coerce = |s: &mut Simp, args: Vec<T>| -> Vec<T> {
            if args.iter().any(|&a| *s.sort(a) == Sort::Real) {
                args.into_iter()
                    .map(|a| {
                        if *s.sort(a) == Sort::Int {
                            s.mk(Op::ToReal, alloc::vec![a])
                        } else {
                            a
                        }
                    })
                    .collect()
            } else {
                args
            }
        };
        let chain = |s: &mut Simp, op: Op, args: &[T]| -> T {
            if args.len() == 2 {
                return s.mk(op, args.to_vec());
            }
            let parts: Vec<T> = args
                .windows(2)
                .map(|w| s.mk(op.clone(), w.to_vec()))
                .collect();
            s.mk(Op::And, parts)
        };
        let t = match head {
            "not" if n == 1 && bools => s.mk(Op::Not, args),
            "and" | "or" if n >= 2 && bools => {
                let op = if head == "and" { Op::And } else { Op::Or };
                s.mk(op, args)
            }
            "=>" if n >= 2 && bools => {
                let mut acc = args[n - 1];
                for &a in args[..n - 1].iter().rev() {
                    acc = s.mk(Op::Implies, alloc::vec![a, acc]);
                }
                acc
            }
            "xor" if n >= 2 && bools => {
                let mut acc = args[0];
                for &a in &args[1..] {
                    acc = s.mk(Op::Xor, alloc::vec![acc, a]);
                }
                acc
            }
            "ite" if n == 3 && *s.sort(args[0]) == Sort::Bool => {
                let (t, e) = (s.sort(args[1]).clone(), s.sort(args[2]).clone());
                if t == e {
                    s.mk(Op::Ite, args)
                } else if t.is_arith_sort() && e.is_arith_sort() {
                    let te = coerce(s, args[1..].to_vec());
                    s.mk(Op::Ite, alloc::vec![args[0], te[0], te[1]])
                } else {
                    return None;
                }
            }
            "=" | "distinct" if n >= 2 => {
                let args = if arith {
                    coerce(s, args)
                } else if args.iter().all(|&a| s.sort(a) == s.sort(args[0])) {
                    args
                } else {
                    return None;
                };
                if head == "distinct" {
                    s.mk(Op::Distinct, args)
                } else {
                    chain(s, Op::Eq, &args)
                }
            }
            "<=" | ">=" | "<" | ">" if n >= 2 && arith => {
                let op = match head {
                    "<=" => Op::Le,
                    ">=" => Op::Ge,
                    "<" => Op::Lt,
                    _ => Op::Gt,
                };
                let args = coerce(s, args);
                chain(s, op, &args)
            }
            "+" | "*" if n >= 2 && arith => {
                let op = if head == "+" { Op::Add } else { Op::Mul };
                let args = coerce(s, args);
                s.mk(op, args)
            }
            "-" if arith => {
                if n == 1 {
                    s.mk(Op::Uminus, args)
                } else {
                    let args = coerce(s, args);
                    s.mk(Op::Sub, args)
                }
            }
            "/" if n == 2 && arith => {
                let args = args
                    .into_iter()
                    .map(|a| {
                        if *s.sort(a) == Sort::Int {
                            s.mk(Op::ToReal, alloc::vec![a])
                        } else {
                            a
                        }
                    })
                    .collect();
                s.mk(Op::Div, args)
            }
            "div" | "mod" | "rem" if n == 2 && all(s, &|x| *x == Sort::Int) => {
                let op = match head {
                    "div" => Op::Idiv,
                    "mod" => Op::Mod,
                    _ => Op::Rem,
                };
                s.mk(op, args)
            }
            "abs" if n == 1 && arith => s.mk(Op::Abs, args),
            "to_real" if n == 1 && *s.sort(args[0]) == Sort::Int => s.mk(Op::ToReal, args),
            "to_int" if n == 1 && *s.sort(args[0]) == Sort::Real => s.mk(Op::ToInt, args),
            "is_int" if n == 1 && *s.sort(args[0]) == Sort::Real => s.mk(Op::IsInt, args),
            _ if bv_op(head).is_some() => {
                let op = bv_op(head)?;
                let Sort::Bv(w) = *s.sort(args[0]) else {
                    return None;
                };
                if op == BvOp::Concat {
                    if args.iter().any(|&a| !matches!(s.sort(a), Sort::Bv(_))) {
                        return None;
                    }
                } else if args.iter().any(|&a| *s.sort(a) != Sort::Bv(w)) {
                    return None;
                }
                let unary = matches!(op, BvOp::Not | BvOp::Neg);
                let nary = matches!(
                    op,
                    BvOp::Add | BvOp::Mul | BvOp::And | BvOp::Or | BvOp::Xor | BvOp::Concat
                );
                if (unary && n != 1) || (!unary && !nary && n != 2) || (nary && n < 2) {
                    return None;
                }
                s.mk(Op::Bv(op), args)
            }
            name => {
                if self.macros.contains_key(name) {
                    return None;
                }
                let d = *self.funcs.get(name)?;
                let fd = self.m.func_decl(d)?;
                if fd.info.family_id != crate::ast::NULL_FAMILY_ID || fd.domain.len() != n {
                    return None;
                }
                for (i, &ds) in fd.domain.iter().enumerate() {
                    if self.th_sort(ds)? != *s.sort(args[i]) {
                        return None;
                    }
                }
                let r = self.th_sort(fd.range)?;
                s.mk_sorted(Op::Uf(name.to_string()), args, r)
            }
        };
        Some(t)
    }
}

/// The bit-vector operator named `h` (not lowered: `bvugt` stays `bvugt`).
fn bv_op(h: &str) -> Option<BvOp> {
    Some(match h {
        "bvadd" => BvOp::Add,
        "bvsub" => BvOp::Sub,
        "bvmul" => BvOp::Mul,
        "bvneg" => BvOp::Neg,
        "bvudiv" => BvOp::Udiv,
        "bvurem" => BvOp::Urem,
        "bvsdiv" => BvOp::Sdiv,
        "bvsrem" => BvOp::Srem,
        "bvsmod" => BvOp::Smod,
        "bvand" => BvOp::And,
        "bvor" => BvOp::Or,
        "bvxor" => BvOp::Xor,
        "bvnot" => BvOp::Not,
        "bvnand" => BvOp::Nand,
        "bvnor" => BvOp::Nor,
        "bvxnor" => BvOp::Xnor,
        "bvshl" => BvOp::Shl,
        "bvlshr" => BvOp::Lshr,
        "bvashr" => BvOp::Ashr,
        "concat" => BvOp::Concat,
        "bvule" => BvOp::Ule,
        "bvult" => BvOp::Ult,
        "bvuge" => BvOp::Uge,
        "bvugt" => BvOp::Ugt,
        "bvsle" => BvOp::Sle,
        "bvslt" => BvOp::Slt,
        "bvsge" => BvOp::Sge,
        "bvsgt" => BvOp::Sgt,
        "bvcomp" => BvOp::Comp,
        _ => return None,
    })
}

/// The indexed operator `(_ name k…)`.
fn th_indexed(idx: &[SExpr]) -> Option<Op> {
    let SExpr::Atom(u) = idx.first()? else {
        return None;
    };
    if u != "_" {
        return None;
    }
    let SExpr::Atom(name) = idx.get(1)? else {
        return None;
    };
    let mut ks = Vec::new();
    for x in &idx[2..] {
        let SExpr::Atom(k) = x else {
            return None;
        };
        ks.push(k.parse::<u32>().ok()?);
    }
    Some(match (name.as_str(), ks.as_slice()) {
        ("extract", [h, l]) => Op::Extract(*h, *l),
        ("zero_extend", [k]) => Op::ZeroExt(*k),
        ("sign_extend", [k]) => Op::SignExt(*k),
        ("repeat", [k]) => Op::Repeat(*k),
        ("rotate_left", [k]) => Op::RotL(*k),
        ("rotate_right", [k]) => Op::RotR(*k),
        _ => return None,
    })
}

/// z3's rendering of a bit-vector numeral: `#x…` for widths divisible by
/// four, else `#b…`.
fn bv_text(v: &Int, w: u32) -> String {
    let mut out = String::new();
    if w.is_multiple_of(4) {
        out.push_str("#x");
        for nib in (0..w / 4).rev() {
            let mut d = 0u32;
            for b in 0..4 {
                if v.bit(u64::from(nib * 4 + b)) {
                    d |= 1 << b;
                }
            }
            out.push(char::from_digit(d, 16).unwrap());
        }
    } else {
        out.push_str("#b");
        for i in (0..w).rev() {
            out.push(if v.bit(u64::from(i)) { '1' } else { '0' });
        }
    }
    out
}

/// z3's rendering of a rational numeral of the given sort (a single leaf, as
/// z3's printer treats numerals).
fn num_text(r: &puremp::Rational, is_int: bool) -> String {
    let a = r.abs();
    let body = if is_int {
        alloc::format!("{}", a.numerator())
    } else if a.is_integer() {
        alloc::format!("{}.0", a.numerator())
    } else {
        alloc::format!("(/ {}.0 {}.0)", a.numerator(), a.denominator())
    };
    if r.is_negative() {
        alloc::format!("(- {body})")
    } else {
        body
    }
}

/// Print `t` as z3's `simplify` does.
fn render(s: &Simp, t: T) -> String {
    let mut arena = Vec::new();
    let mut map = BTreeMap::new();
    let root = to_pp(s, t, &mut arena, &mut map);
    pp_term(&arena, root, &|h| {
        matches!(
            h,
            "and"
                | "or"
                | "xor"
                | "+"
                | "*"
                | "bvadd"
                | "bvmul"
                | "bvand"
                | "bvor"
                | "bvxor"
                | "concat"
        )
    })
}

fn to_pp(s: &Simp, t: T, arena: &mut Vec<PpNode>, map: &mut BTreeMap<T, usize>) -> usize {
    if let Some(&i) = map.get(&t) {
        return i;
    }
    let i = match s.op(t) {
        Op::Num(r) => {
            arena.push(PpNode {
                head: num_text(r, *s.sort(t) == Sort::Int),
                args: Vec::new(),
                indexed: false,
            });
            arena.len() - 1
        }
        Op::BvNum(v) => {
            let Sort::Bv(w) = *s.sort(t) else {
                unreachable!()
            };
            arena.push(PpNode {
                head: bv_text(v, w),
                args: Vec::new(),
                indexed: false,
            });
            arena.len() - 1
        }
        op => {
            let indexed = matches!(
                op,
                Op::Extract(..)
                    | Op::ZeroExt(_)
                    | Op::SignExt(_)
                    | Op::Repeat(_)
                    | Op::RotL(_)
                    | Op::RotR(_)
            );
            let head = match op {
                Op::Extract(h, l) => alloc::format!("(_ extract {h} {l})"),
                Op::ZeroExt(k) => alloc::format!("(_ zero_extend {k})"),
                Op::SignExt(k) => alloc::format!("(_ sign_extend {k})"),
                Op::Repeat(k) => alloc::format!("(_ repeat {k})"),
                Op::RotL(k) => alloc::format!("(_ rotate_left {k})"),
                Op::RotR(k) => alloc::format!("(_ rotate_right {k})"),
                Op::Bv(b) => Simp::op_name(&Op::Bv(*b)).unwrap().to_string(),
                Op::Ite => "ite".to_string(),
                Op::Uf(n) => smt2_symbol(n).into_owned(),
                Op::Uminus => "-".to_string(),
                _ => op_name(op),
            };
            let args: Vec<usize> = s
                .args(t)
                .to_vec()
                .into_iter()
                .map(|a| to_pp(s, a, arena, map))
                .collect();
            arena.push(PpNode {
                head,
                args,
                indexed,
            });
            arena.len() - 1
        }
    };
    map.insert(t, i);
    i
}

/// The printed name of an operator.
fn op_name(op: &Op) -> String {
    let n = match op {
        Op::True => "true",
        Op::False => "false",
        Op::Not => "not",
        Op::And => "and",
        Op::Or => "or",
        Op::Implies => "=>",
        Op::Xor => "xor",
        Op::Eq => "=",
        Op::Distinct => "distinct",
        Op::Add => "+",
        Op::Sub => "-",
        Op::Mul => "*",
        Op::Div => "/",
        Op::Idiv => "div",
        Op::Mod => "mod",
        Op::Rem => "rem",
        Op::Le => "<=",
        Op::Ge => ">=",
        Op::Lt => "<",
        Op::Gt => ">",
        Op::ToReal => "to_real",
        Op::ToInt => "to_int",
        Op::IsInt => "is_int",
        Op::Abs => "abs",
        _ => "?",
    };
    n.to_string()
}

/// The outcome of [`Context::opt_preprocess`].
pub(super) struct OptPre {
    /// The hard constraints simplified to `false`.
    pub inconsistent: bool,
    /// Each objective's terms (one for `minimize`/`maximize`, one per soft
    /// constraint of a soft group) as preprocessing left them.
    pub terms: Vec<Vec<PreTerm>>,
}

/// An objective term after [`Context::opt_preprocess`].
pub(super) enum PreTerm {
    /// A numeral (`(value, is_int)`).
    Num(puremp::Rational, bool),
    /// `true` or `false`.
    Bool(bool),
    /// An integer term over `lia2card`'s Boolean-encoded constants only,
    /// with its range `(lo, hi)`.
    Range(puremp::Rational, puremp::Rational),
    /// Anything else.
    Other,
}

impl Context {
    /// Build the z3rs term `t` in the rewriter's arena: numerals, Boolean
    /// and arithmetic operators, and uninterpreted symbols; `None` outside
    /// that fragment.
    fn th_ast(&self, b: &mut Builder, t: AstId, memo: &mut BTreeMap<AstId, T>) -> Option<T> {
        // Post-order with an explicit stack: assertions may nest deeply.
        let mut stack = alloc::vec![(t, false)];
        while let Some((x, done)) = stack.pop() {
            if memo.contains_key(&x) {
                continue;
            }
            if let Some(r) = self.m.as_numeral(x) {
                let is_int = self.m.is_int_sort(self.m.get_sort(x));
                let n = b.s.mk_num(r, is_int);
                memo.insert(x, n);
                continue;
            }
            if let Some(v) = self.m.bv_numeral_value(x) {
                let w = self.m.bv_sort_width(self.m.get_sort(x))?;
                let n = b.s.mk_bv_num(&v, w);
                memo.insert(x, n);
                continue;
            }
            if self.m.is_true(x) || self.m.is_false(x) {
                let n = if self.m.is_true(x) {
                    b.s.mk_true()
                } else {
                    b.s.mk_false()
                };
                memo.insert(x, n);
                continue;
            }
            let app = self.m.app(x)?;
            if !done {
                stack.push((x, true));
                stack.extend(app.args.iter().map(|&a| (a, false)));
                continue;
            }
            let args: Vec<T> = app.args.iter().map(|a| memo[a]).collect();
            let fd = self.m.func_decl(app.decl)?;
            let name = alloc::format!("{}", fd.name);
            let r = if fd.info.family_id == crate::ast::NULL_FAMILY_ID && args.is_empty() {
                let s = self.th_sort(fd.range)?;
                b.s.mk_sorted(Op::Uf(name), Vec::new(), s)
            } else if self.m.is_ite(x) {
                self.th_app(b, "ite", args)?
            } else if self.m.arith_op(x) == Some(crate::ast::arith::ArithOp::Uminus) {
                self.th_app(b, "-", args)?
            } else {
                self.th_app(b, &name, args)?
            };
            memo.insert(x, r);
        }
        memo.get(&t).copied()
    }

    /// The part of z3's optimization preprocessing (`opt::context::
    /// simplify_fmls`: `simplify`, `propagate-values`, `solve-eqs`,
    /// `simplify` over the hard constraints and the objectives together)
    /// that decides what `get-objectives` reports when the hard constraints
    /// are unsatisfiable: whether they simplify to `false` (z3 then never
    /// reaches its optimizer and reports 0), which objectives become
    /// numerals, and which soft constraints become `true` or `false`. `objs`
    /// holds each objective's terms; `elim_01` adds the `lia2card` step that
    /// runs without a logic, assumptions or `opt.incremental`. `None` when a
    /// term lies outside the supported fragment.
    pub(super) fn opt_preprocess(
        &self,
        fmls: &[AstId],
        objs: &[Vec<AstId>],
        elim_01: bool,
    ) -> Option<OptPre> {
        let mut b = Builder {
            s: Simp::new(),
            scopes: Vec::new(),
        };
        let mut memo = BTreeMap::new();
        let mut goal = Vec::new();
        for &f in fmls {
            let t = self.th_ast(&mut b, f, &mut memo)?;
            goal.push(t);
        }
        let mut obj = Vec::new();
        for &o in objs.iter().flatten() {
            obj.push(self.th_ast(&mut b, o, &mut memo)?);
        }
        let s = &mut b.s;
        let mut goal: Vec<T> = goal.into_iter().map(|t| s.simplify(t)).collect();
        let mut obj: Vec<T> = obj.into_iter().map(|t| s.simplify(t)).collect();
        let mut inconsistent = !normalize_goal(s, &mut goal);
        // propagate-values: a forward and a backward pass per round, each
        // formula rewritten with the unit facts of those before it.
        for _ in 0..4 {
            if inconsistent {
                break;
            }
            let mut changed = false;
            for backward in [false, true] {
                let shared = shared_occs(s, goal.iter().chain(obj.iter()).copied());
                let mut map: BTreeMap<T, T> = BTreeMap::new();
                let n = goal.len() + obj.len();
                for k in 0..n {
                    // Objectives follow the hard constraints.
                    let i = if backward { n - 1 - k } else { k };
                    let slot = if i < goal.len() {
                        &mut goal[i]
                    } else {
                        &mut obj[i - goal.len()]
                    };
                    if !map.is_empty() {
                        let r = substitute(s, *slot, &map);
                        let r = s.simplify(r);
                        if r != *slot {
                            *slot = r;
                            changed = true;
                        }
                    }
                    if i < goal.len() {
                        add_unit(s, goal[i], &shared, &mut map);
                    }
                }
                if !normalize_goal(s, &mut goal) {
                    inconsistent = true;
                    break;
                }
            }
            if !changed {
                break;
            }
        }
        // solve-eqs: eliminate a variable a top-level equation defines.
        // Its `bound_manager` reads the bounds once, before the first round.
        let lower = goal_lower_bounds(s, &goal);
        let mut rounds = 0;
        while !inconsistent && rounds < 64 {
            rounds += 1;
            let solved = (0..goal.len()).find_map(|i| {
                let f = goal[i];
                solve_eq(s, f).map(|(x, d)| (i, x, d))
            });
            let Some((i, x, def)) = solved.or_else(|| bound_eq(s, &goal, &lower)) else {
                break;
            };
            goal.remove(i);
            let map = BTreeMap::from([(x, def)]);
            for slot in goal.iter_mut().chain(obj.iter_mut()) {
                let r = substitute(s, *slot, &map);
                *slot = s.simplify(r);
            }
            inconsistent = !normalize_goal(s, &mut goal);
        }
        // The closing `simplify`.
        if !inconsistent {
            for slot in goal.iter_mut().chain(obj.iter_mut()) {
                *slot = s.simplify(*slot);
            }
            inconsistent = !normalize_goal(s, &mut goal);
        }
        // `opt.elim_01`: `lia2card` and the `simplify` after it.
        let mut boxes = BTreeMap::new();
        if elim_01 && !inconsistent {
            boxes = lia2card(s, &mut goal, &mut obj);
            // Only a formula rewritten to `false` refutes the goal: an atom
            // it left open is a pseudo-Boolean constraint now, so a literal
            // and its negation no longer face each other syntactically.
            inconsistent = goal.iter().any(|&g| *s.op(g) == Op::False);
        }
        let mut flat = obj.into_iter().map(|o| match s.op(o) {
            Op::Num(r) => PreTerm::Num(r.clone(), *s.sort(o) == Sort::Int),
            Op::True => PreTerm::Bool(true),
            Op::False => PreTerm::Bool(false),
            _ => match pb_range(s, o).or_else(|| box_range(s, o, &boxes)) {
                Some((lo, hi)) => PreTerm::Range(lo, hi),
                None => PreTerm::Other,
            },
        });
        let terms = objs
            .iter()
            .map(|o| flat.by_ref().take(o.len()).collect())
            .collect();
        Some(OptPre {
            inconsistent,
            terms,
        })
    }
}

/// Is `t` a value (`m.is_value`): a numeral or a Boolean constant?
fn is_value(s: &Simp, t: T) -> bool {
    matches!(s.op(t), Op::Num(_) | Op::BvNum(_) | Op::True | Op::False)
}

/// Record the substitution the unit formula `f` justifies (z3's
/// `propagate_values::add_sub`): `¬a` maps `a` to false, an atom to true,
/// and `t = v` with `v` a value maps `t` to `v` — each only for a term that
/// occurs more than once (`shared`), the only ones worth rewriting.
fn add_unit(s: &mut Simp, f: T, shared: &BTreeSet<T>, map: &mut BTreeMap<T, T>) {
    if *s.op(f) == Op::Not && shared.contains(&s.args(f)[0]) {
        let a = s.args(f)[0];
        let ff = s.mk_false();
        map.insert(a, ff);
    }
    if shared.contains(&f) {
        let tt = s.mk_true();
        map.insert(f, tt);
    }
    if *s.op(f) == Op::Eq && s.args(f).len() == 2 {
        let (x, y) = (s.args(f)[0], s.args(f)[1]);
        if is_value(s, x) && shared.contains(&y) {
            map.insert(y, x);
        } else if is_value(s, y) && shared.contains(&x) {
            map.insert(x, y);
        }
    }
}

/// The terms reached more than once from the roots `fmls` (z3's
/// `shared_occs`, tracking constants too); values are never shared.
fn shared_occs(s: &Simp, fmls: impl Iterator<Item = T>) -> BTreeSet<T> {
    let mut seen = BTreeSet::new();
    let mut shared = BTreeSet::new();
    let mut stack: Vec<T> = fmls.collect();
    stack.reverse();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            if !is_value(s, t) {
                shared.insert(t);
            }
            continue;
        }
        stack.extend(s.args(t).iter().copied());
    }
    shared
}

/// Flatten the goal's top-level conjunctions (and negated disjunctions),
/// drop `true`, and detect `false` or a literal next to its negation as
/// z3's `goal` does: `false` when the goal is inconsistent.
fn normalize_goal(s: &mut Simp, goal: &mut Vec<T>) -> bool {
    let mut out: Vec<T> = Vec::new();
    let mut pos: BTreeSet<T> = BTreeSet::new();
    let mut neg: BTreeSet<T> = BTreeSet::new();
    let mut todo: Vec<T> = goal.iter().rev().copied().collect();
    while let Some(f) = todo.pop() {
        match s.op(f) {
            Op::True => continue,
            Op::False => return false,
            Op::And => {
                todo.extend(s.args(f).iter().rev().copied());
                continue;
            }
            Op::Not if *s.op(s.args(f)[0]) == Op::Or => {
                let args = s.args(s.args(f)[0]).to_vec();
                for &a in args.iter().rev() {
                    let n = s.mk(Op::Not, alloc::vec![a]);
                    let n = s.simplify(n);
                    todo.push(n);
                }
                continue;
            }
            _ => {}
        }
        let fresh = if *s.op(f) == Op::Not {
            let a = s.args(f)[0];
            if pos.contains(&a) {
                return false;
            }
            neg.insert(a)
        } else {
            if neg.contains(&f) {
                return false;
            }
            pos.insert(f)
        };
        if fresh {
            out.push(f);
        }
    }
    *goal = out;
    true
}

/// `t` with every subterm in `map` replaced (not simplified).
fn substitute(s: &mut Simp, t: T, map: &BTreeMap<T, T>) -> T {
    let mut done: BTreeMap<T, T> = BTreeMap::new();
    let mut stack = alloc::vec![(t, false)];
    while let Some((x, expanded)) = stack.pop() {
        if done.contains_key(&x) {
            continue;
        }
        if let Some(&r) = map.get(&x) {
            done.insert(x, r);
            continue;
        }
        let args = s.args(x).to_vec();
        if args.is_empty() {
            done.insert(x, x);
            continue;
        }
        if !expanded {
            stack.push((x, true));
            stack.extend(args.iter().map(|&a| (a, false)));
            continue;
        }
        let new: Vec<T> = args.iter().map(|a| done[a]).collect();
        let r = if new == args {
            x
        } else {
            let (op, sort) = (s.op(x).clone(), s.sort(x).clone());
            s.mk_sorted(op, new, sort)
        };
        done.insert(x, r);
    }
    done[&t]
}

/// Does `x` occur in `t`?
fn occurs(s: &Simp, x: T, t: T) -> bool {
    let mut stack = alloc::vec![t];
    let mut seen = BTreeSet::new();
    while let Some(u) = stack.pop() {
        if u == x {
            return true;
        }
        if seen.insert(u) {
            stack.extend(s.args(u).iter().copied());
        }
    }
    false
}

/// Is `t` an uninterpreted constant?
fn is_uconst(s: &Simp, t: T) -> bool {
    matches!(s.op(t), Op::Uf(_)) && s.args(t).is_empty()
}

/// A variable the top-level formula `f` defines, with its definition (z3's
/// `basic_extract_eq` and the linear cases of `arith_extract_eq`): `x = t`,
/// `x + r = t` (a real `x` may carry any nonzero coefficient, an integer one
/// only -1) and, over the reals, `x·c = t` for nonzero numerals `c`; `x`
/// must not occur in its definition. A Boolean constant `p` or `¬p` is
/// `p := true` / `p := false`.
fn solve_eq(s: &mut Simp, f: T) -> Option<(T, T)> {
    // A Boolean constant asserted (`p := true`) or negated (`p := false`).
    if is_uconst(s, f) && *s.sort(f) == Sort::Bool {
        return Some((f, s.mk_true()));
    }
    if *s.op(f) == Op::Not && is_uconst(s, s.args(f)[0]) {
        let x = s.args(f)[0];
        return Some((x, s.mk_false()));
    }
    if *s.op(f) != Op::Eq || s.args(f).len() != 2 {
        return None;
    }
    let (a, b) = (s.args(f)[0], s.args(f)[1]);
    for (lhs, rhs) in [(a, b), (b, a)] {
        if is_uconst(s, lhs) && !occurs(s, lhs, rhs) {
            return Some((lhs, rhs));
        }
    }
    if !s.sort(a).is_arith_sort() {
        return None;
    }
    for (lhs, rhs) in [(a, b), (b, a)] {
        if let Some(r) = solve_add(s, lhs, rhs) {
            return Some(r);
        }
    }
    for (lhs, rhs) in [(a, b), (b, a)] {
        if let Some(r) = solve_mul(s, lhs, rhs) {
            return Some(r);
        }
    }
    None
}

/// The best lower bound `(value, strict)` of each constant among the
/// goal's atoms that compare a constant with a numeral (z3's
/// `bound_manager`, normalizing strict integer bounds).
fn goal_lower_bounds(s: &Simp, goal: &[T]) -> BTreeMap<T, (puremp::Rational, bool)> {
    use puremp::Rational as Q;
    let mut lower: BTreeMap<T, (Q, bool)> = BTreeMap::new();
    for &f in goal {
        let (mut atom, mut pos) = (f, true);
        while *s.op(atom) == Op::Not {
            atom = s.args(atom)[0];
            pos = !pos;
        }
        let op = s.op(atom).clone();
        if !matches!(op, Op::Le | Op::Ge | Op::Lt | Op::Gt) || s.args(atom).len() != 2 {
            continue;
        }
        let (l, r) = (s.args(atom)[0], s.args(atom)[1]);
        // `x ⋈ n` as (is_lower, strict, n).
        let (v, n, mut lower_kind, mut strict) = match (s.op(l), s.op(r)) {
            (Op::Uf(_), Op::Num(n)) if s.args(l).is_empty() => (
                l,
                n.clone(),
                matches!(op, Op::Ge | Op::Gt),
                matches!(op, Op::Lt | Op::Gt),
            ),
            (Op::Num(n), Op::Uf(_)) if s.args(r).is_empty() => (
                r,
                n.clone(),
                matches!(op, Op::Le | Op::Lt),
                matches!(op, Op::Lt | Op::Gt),
            ),
            _ => continue,
        };
        if !pos {
            lower_kind = !lower_kind;
            strict = !strict;
        }
        if !lower_kind {
            continue;
        }
        let mut n = n;
        if strict && *s.sort(v) == Sort::Int {
            n = Q::from_integer(n.floor()).add(&Q::from_integer(puremp::Int::from(1)));
            strict = false;
        }
        let better = lower
            .get(&v)
            .is_none_or(|(m, st)| n > *m || (n == *m && strict && !*st));
        if better {
            lower.insert(v, (n, strict));
        }
    }
    lower
}

/// A formula `x ≤ c` of the goal where `lower` (the bounds `solve-eqs` read
/// before its first round, [`goal_lower_bounds`]) bounds `x ≥ c`
/// non-strictly, with its index: `x = c` (`arith_extract_eq::get_eqs`).
fn bound_eq(
    s: &mut Simp,
    goal: &[T],
    lower: &BTreeMap<T, (puremp::Rational, bool)>,
) -> Option<(usize, T, T)> {
    goal.iter().enumerate().find_map(|(i, &f)| {
        if *s.op(f) != Op::Le || s.args(f).len() != 2 {
            return None;
        }
        let (x, c) = (s.args(f)[0], s.args(f)[1]);
        let Op::Num(hi) = s.op(c) else {
            return None;
        };
        (is_uconst(s, x) && lower.get(&x).is_some_and(|(lo, st)| !st && lo == hi))
            .then_some((i, x, c))
    })
}

/// The integer bounds z3's `bound_manager` reads off the goal's literals:
/// `x ⋈ n` / `n ⋈ x` (negations flipped, strict ones rounded), `x = n`, and
/// a disjunction `x = n₁ ∨ … ∨ x = nₖ` (bounded by the least and largest
/// `nᵢ`). Each constant's tightest `(lower, upper)`.
fn goal_int_bounds(s: &Simp, goal: &[T]) -> BTreeMap<T, (Option<Int>, Option<Int>)> {
    use puremp::Rational as Q;
    let mut out: BTreeMap<T, (Option<Int>, Option<Int>)> = BTreeMap::new();
    let int_const = |t: T| is_uconst(s, t) && *s.sort(t) == Sort::Int;
    let num = |t: T| match s.op(t) {
        Op::Num(n) if n.is_integer() => Some(n.numerator().clone()),
        _ => None,
    };
    let mut add = |v: T, lo: Option<Int>, hi: Option<Int>| {
        let e = out.entry(v).or_insert((None, None));
        if let Some(l) = lo {
            e.0 = Some(e.0.take().map_or(l.clone(), |o| if l > o { l } else { o }));
        }
        if let Some(h) = hi {
            e.1 = Some(e.1.take().map_or(h.clone(), |o| if h < o { h } else { o }));
        }
    };
    // `x = n` with `x` an integer constant (either side).
    let eq_bound = |f: T| -> Option<(T, Int)> {
        if *s.op(f) != Op::Eq || s.args(f).len() != 2 {
            return None;
        }
        let (a, b) = (s.args(f)[0], s.args(f)[1]);
        if int_const(a) {
            Some((a, num(b)?))
        } else if int_const(b) {
            Some((b, num(a)?))
        } else {
            None
        }
    };
    for &f in goal {
        if *s.op(f) == Op::Or && !s.args(f).is_empty() {
            let eqs: Option<Vec<(T, Int)>> = s.args(f).iter().map(|&e| eq_bound(e)).collect();
            if let Some(eqs) = eqs
                && eqs.iter().all(|(v, _)| *v == eqs[0].0)
            {
                let lo = eqs.iter().map(|(_, n)| n.clone()).min();
                let hi = eqs.iter().map(|(_, n)| n.clone()).max();
                add(eqs[0].0, lo, hi);
            }
            continue;
        }
        if let Some((v, n)) = eq_bound(f) {
            add(v, Some(n.clone()), Some(n));
            continue;
        }
        let (mut atom, mut pos) = (f, true);
        while *s.op(atom) == Op::Not {
            atom = s.args(atom)[0];
            pos = !pos;
        }
        let op = s.op(atom).clone();
        if !matches!(op, Op::Le | Op::Ge | Op::Lt | Op::Gt) || s.args(atom).len() != 2 {
            continue;
        }
        let (l, r) = (s.args(atom)[0], s.args(atom)[1]);
        // `v ⋈ n` as (is_lower, strict).
        let (v, n, mut lower, mut strict) = match (s.op(l), s.op(r)) {
            (_, Op::Num(n)) if int_const(l) => (
                l,
                n.clone(),
                matches!(op, Op::Ge | Op::Gt),
                matches!(op, Op::Lt | Op::Gt),
            ),
            (Op::Num(n), _) if int_const(r) => (
                r,
                n.clone(),
                matches!(op, Op::Le | Op::Lt),
                matches!(op, Op::Lt | Op::Gt),
            ),
            _ => continue,
        };
        if !pos {
            lower = !lower;
            strict = !strict;
        }
        let one = Q::from_integer(Int::from(1));
        let n = match (lower, strict) {
            (true, false) => n.ceil(),
            (true, true) => n.add(&one).ceil(),
            (false, false) => n.floor(),
            (false, true) => n.sub(&one).floor(),
        };
        if lower {
            add(v, Some(n), None);
        } else {
            add(v, None, Some(n));
        }
    }
    out
}

/// `t` as a linear form over integer constants (`None` outside `+`, `-`,
/// numeral products and numerals).
fn int_lin(s: &Simp, t: T) -> Option<(BTreeMap<T, puremp::Rational>, puremp::Rational)> {
    use puremp::Rational as Q;
    let mut coeffs: BTreeMap<T, Q> = BTreeMap::new();
    let mut k = Q::from_integer(Int::from(0));
    let mut stack = alloc::vec![(t, Q::from_integer(Int::from(1)))];
    while let Some((u, c)) = stack.pop() {
        match s.op(u) {
            Op::Num(n) => k = k.add(&c.mul(n)),
            Op::Uf(_) if s.args(u).is_empty() && *s.sort(u) == Sort::Int => {
                let e = coeffs
                    .entry(u)
                    .or_insert_with(|| Q::from_integer(Int::from(0)));
                *e = e.add(&c);
            }
            Op::Add => stack.extend(s.args(u).iter().map(|&a| (a, c.clone()))),
            Op::Sub => {
                let a = s.args(u);
                stack.push((a[0], c.clone()));
                stack.extend(a[1..].iter().map(|&b| (b, c.neg())));
            }
            Op::Uminus => stack.push((s.args(u)[0], c.neg())),
            Op::Mul => {
                let a = s.args(u);
                let mut c = c;
                let mut rest = None;
                for &x in a {
                    match s.op(x) {
                        Op::Num(n) => c = c.mul(n),
                        _ if rest.is_none() => rest = Some(x),
                        _ => return None,
                    }
                }
                match rest {
                    Some(x) => stack.push((x, c)),
                    None => k = k.add(&c),
                }
            }
            _ => return None,
        }
    }
    Some((coeffs, k))
}

/// z3's `lia2card` step of the optimizer preprocessing: every integer
/// constant the goal bounds by `0 ≤ lo ≤ x ≤ hi` with `hi − lo ≤ 100`
/// becomes a sum of Booleans, so a comparison of a linear term over such
/// constants only is decided as soon as their ranges decide it. Rewrites
/// the goal and the objective terms with those decisions; returns the
/// converted constants' ranges.
fn lia2card(
    s: &mut Simp,
    goal: &mut [T],
    obj: &mut [T],
) -> BTreeMap<T, (puremp::Rational, puremp::Rational)> {
    use puremp::Rational as Q;
    let boxes: BTreeMap<T, (Q, Q)> = goal_int_bounds(s, goal)
        .into_iter()
        .filter_map(|(v, (lo, hi))| {
            let (lo, hi) = (lo?, hi?);
            (lo >= Int::from(0) && hi >= lo && hi.clone().sub(&lo) <= Int::from(100))
                .then(|| (v, (Q::from_integer(lo), Q::from_integer(hi))))
        })
        .collect();
    // Every comparison of pseudo-Boolean sums (numerals, numeral `ite`s
    // and boxed constants), decided by its range.
    let mut map: BTreeMap<T, T> = BTreeMap::new();
    let mut seen = BTreeSet::new();
    let mut stack: Vec<T> = goal.iter().chain(obj.iter()).copied().collect();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        stack.extend(s.args(t).iter().copied());
        let op = s.op(t).clone();
        if !matches!(op, Op::Le | Op::Ge | Op::Lt | Op::Gt | Op::Eq) || s.args(t).len() != 2 {
            continue;
        }
        let (a, b) = (s.args(t)[0], s.args(t)[1]);
        if !s.sort(a).is_arith_sort() {
            continue;
        }
        // The range of a − b.
        let one = Q::from_integer(Int::from(1));
        let Some((lo, hi, _)) = pb_bounds(s, &[(a, one.clone()), (b, one.neg())], &boxes, true)
        else {
            continue;
        };
        let zero = Q::from_integer(Int::from(0));
        let value = match op {
            Op::Eq if lo > zero || hi < zero => Some(false),
            Op::Eq if lo == zero && hi == zero => Some(true),
            Op::Le if lo > zero => Some(false),
            Op::Le if hi <= zero => Some(true),
            Op::Lt if lo >= zero => Some(false),
            Op::Lt if hi < zero => Some(true),
            Op::Ge if hi < zero => Some(false),
            Op::Ge if lo >= zero => Some(true),
            Op::Gt if hi <= zero => Some(false),
            Op::Gt if lo > zero => Some(true),
            _ => None,
        };
        if let Some(v) = value {
            let c = if v { s.mk_true() } else { s.mk_false() };
            map.insert(t, c);
        }
    }
    if !map.is_empty() {
        for slot in goal.iter_mut().chain(obj.iter_mut()) {
            let r = substitute(s, *slot, &map);
            *slot = s.simplify(r);
        }
    }
    boxes
}

/// The bounds `(c, c + Σ wᵢ)` of `Σ mᵢ·tᵢ` over `roots` as `lia2card`'s
/// `get_pb_sum` reads it: a sum of numerals, `ite`s with numeral branches (one level deep)
/// and the `boxes`' constants (each `lo + Σ [bitᵢ]`), i.e.
/// `c + Σ wᵢ·[condᵢ]` with every `wᵢ > 0` (a negative `w·[d]` is
/// `w + |w|·[¬d]`); the conditions are taken independently. The flag
/// tells whether `t` has a condition or boxed constant at all. `None`
/// outside that form.
fn pb_bounds(
    s: &Simp,
    roots: &[(T, puremp::Rational)],
    boxes: &BTreeMap<T, (puremp::Rational, puremp::Rational)>,
    merge: bool,
) -> Option<(puremp::Rational, puremp::Rational, bool)> {
    use puremp::Rational as Q;
    let zero = || Q::from_integer(Int::from(0));
    let (mut coeff, mut total) = (zero(), zero());
    let mut any = false;
    // With `merge`, the weights of each condition and of its negation, as
    // the pseudo-Boolean rewriter combines `x·[c] + y·[¬c]`.
    let mut by_cond: BTreeMap<T, (Q, Q)> = BTreeMap::new();
    // One weight `p` under a condition.
    let weigh = |p: Q, coeff: &mut Q, total: &mut Q| {
        if p.is_negative() {
            *coeff = coeff.add(&p);
            *total = total.sub(&p);
        } else {
            *total = total.add(&p);
        }
    };
    // (term, multiplier, ite nesting, under a condition)
    let mut stack: Vec<(T, Q, u32, bool)> = roots
        .iter()
        .map(|(t, m)| (*t, m.clone(), 0u32, false))
        .collect();
    while let Some((u, mul, nesting, cond)) = stack.pop() {
        if let Op::Num(r) = s.op(u) {
            let p = mul.mul(r);
            if cond {
                weigh(p, &mut coeff, &mut total);
            } else {
                coeff = coeff.add(&p);
            }
            continue;
        }
        if nesting > 1 {
            return None;
        }
        if let Some((lo, hi)) = boxes.get(&u) {
            // `lo + Σ ite(bᵢ, 1, 0)`: its bits sit one level deeper.
            if nesting > 0 {
                return None;
            }
            any = true;
            coeff = coeff.add(&mul.mul(lo));
            let bits = hi.sub(lo);
            weigh(mul.mul(&bits), &mut coeff, &mut total);
            continue;
        }
        let a = s.args(u);
        match s.op(u) {
            Op::Add => stack.extend(a.iter().map(|&x| (x, mul.clone(), nesting, cond))),
            Op::Sub => {
                stack.push((a[0], mul.clone(), nesting, cond));
                stack.extend(a[1..].iter().map(|&x| (x, mul.neg(), nesting, cond)));
            }
            Op::Uminus => stack.push((a[0], mul.neg(), nesting, cond)),
            Op::ToReal => stack.push((a[0], mul, nesting, cond)),
            Op::Mul if a.len() == 2 => match (s.op(a[0]), s.op(a[1])) {
                (Op::Num(r), _) => stack.push((a[1], mul.mul(r), nesting, cond)),
                (_, Op::Num(r)) => stack.push((a[0], mul.mul(r), nesting, cond)),
                _ => return None,
            },
            Op::Ite => {
                any = true;
                let numeral = |x: T| match s.op(x) {
                    Op::Num(r) => Some(r.clone()),
                    _ => None,
                };
                if let (true, Some(th), Some(el)) = (merge, numeral(a[1]), numeral(a[2])) {
                    let e = by_cond.entry(a[0]).or_insert_with(|| (zero(), zero()));
                    e.0 = e.0.add(&mul.mul(&th));
                    e.1 = e.1.add(&mul.mul(&el));
                    continue;
                }
                stack.push((a[1], mul.clone(), nesting + 1, true));
                stack.push((a[2], mul, nesting + 1, true));
            }
            _ => return None,
        }
    }
    for (_, (th, el)) in by_cond {
        // `el + (th − el)·[c]`.
        coeff = coeff.add(&el);
        weigh(th.sub(&el), &mut coeff, &mut total);
    }
    let hi = coeff.add(&total);
    Some((coeff, hi, any))
}

/// An objective z3's optimizer turns into a MaxSAT problem
/// (`opt::context::is_maxsat` over `get_pb_sum`, see [`pb_bounds`]): its
/// bounds before any search.
fn pb_range(s: &Simp, t: T) -> Option<(puremp::Rational, puremp::Rational)> {
    let one = puremp::Rational::from_integer(Int::from(1));
    let (lo, hi, any) = pb_bounds(s, &[(t, one)], &BTreeMap::new(), false)?;
    any.then_some((lo, hi))
}

/// The range of the integer term `t` over `boxes` when it is linear in
/// boxed constants only (at least one).
fn box_range(
    s: &Simp,
    t: T,
    boxes: &BTreeMap<T, (puremp::Rational, puremp::Rational)>,
) -> Option<(puremp::Rational, puremp::Rational)> {
    if *s.sort(t) != Sort::Int {
        return None;
    }
    let (coeffs, k) = int_lin(s, t)?;
    if coeffs.is_empty() {
        return None;
    }
    let (mut lo, mut hi) = (k.clone(), k);
    for (v, c) in coeffs {
        let (l, h) = boxes.get(&v)?;
        let (x, y) = (c.mul(l), c.mul(h));
        let (x, y) = if x <= y { (x, y) } else { (y, x) };
        lo = lo.add(&x);
        hi = hi.add(&y);
    }
    Some((lo, hi))
}

/// `x + r = y` (`arith_extract_eq::solve_add`).
fn solve_add(s: &mut Simp, lhs: T, rhs: T) -> Option<(T, T)> {
    if *s.op(lhs) != Op::Add {
        return None;
    }
    let args = s.args(lhs).to_vec();
    for (i, &arg) in args.iter().enumerate() {
        let (x, coef) = if is_uconst(s, arg) {
            (arg, None)
        } else if *s.op(arg) == Op::Mul
            && s.args(arg).len() == 2
            && let Op::Num(r) = s.op(s.args(arg)[0]).clone()
            && is_uconst(s, s.args(arg)[1])
        {
            let real = *s.sort(arg) == Sort::Real;
            if r.is_zero() || (!real && r != puremp::Rational::from(-1i64)) {
                continue;
            }
            (s.args(arg)[1], Some(s.args(arg)[0]))
        } else {
            continue;
        };
        let mut term = rhs;
        for (j, &other) in args.iter().enumerate() {
            if j != i {
                term = s.mk(Op::Sub, alloc::vec![term, other]);
            }
        }
        if let Some(c) = coef {
            term = if *s.sort(arg) == Sort::Real {
                s.mk(Op::Div, alloc::vec![term, c])
            } else {
                s.mk(Op::Uminus, alloc::vec![term])
            };
        }
        let term = s.simplify(term);
        if !occurs(s, x, term) {
            return Some((x, term));
        }
    }
    None
}

/// `x·c₁·… = y` over the reals with nonzero numerals `cᵢ`
/// (`arith_extract_eq::solve_mul`).
fn solve_mul(s: &mut Simp, lhs: T, rhs: T) -> Option<(T, T)> {
    if *s.op(lhs) != Op::Mul || *s.sort(lhs) != Sort::Real {
        return None;
    }
    let args = s.args(lhs).to_vec();
    for (i, &x) in args.iter().enumerate() {
        if !is_uconst(s, x) {
            continue;
        }
        let nonzero = args
            .iter()
            .enumerate()
            .all(|(j, &a)| j == i || matches!(s.op(a), Op::Num(r) if !r.is_zero()));
        if !nonzero {
            continue;
        }
        let rest: Vec<T> = args
            .iter()
            .enumerate()
            .filter(|&(j, _)| j != i)
            .map(|(_, &a)| a)
            .collect();
        let d = if rest.len() == 1 {
            rest[0]
        } else {
            s.mk(Op::Mul, rest)
        };
        let term = s.mk(Op::Div, alloc::vec![rhs, d]);
        let term = s.simplify(term);
        if !occurs(s, x, term) {
            return Some((x, term));
        }
    }
    None
}
