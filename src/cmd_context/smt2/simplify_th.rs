//! `(simplify t)` through z3's theory rewriter ([`crate::rewriter::th_simp`]):
//! the term is rebuilt in the rewriter's own arena with the source's
//! operators (no lowering), simplified with z3's default rules and printed
//! with z3's layout. Terms outside the supported fragment (Boolean,
//! arithmetic and uninterpreted symbols over those and declared sorts) are
//! left to the general `simplify` path.

use alloc::collections::BTreeMap;
use alloc::string::{String, ToString};
use alloc::vec::Vec;

use super::super::smt2_pp::{PpNode, pp_term};
use super::{Context, SExpr, parse_numeral};
use crate::ast::AstId;
use crate::rewriter::th_simp::{Op, Simp, Sort, T};
use crate::util::symbol::smt2_symbol;

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
            "and" | "or" | "xor" | "+" | "*" | "bvadd" | "bvmul" | "bvand" | "bvor" | "bvxor"
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
        op => {
            let head = match op {
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
                indexed: false,
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
