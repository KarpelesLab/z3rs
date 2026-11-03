//! z3's `elim-uncnstr` tactic (`tactic/core/elim_uncnstr_tactic.cpp`) over
//! the goal exactly as z3's SMT-LIB parser builds it, for `(apply …)` and
//! `(check-sat-using …)` pipelines that start with it.
//!
//! The command context's terms are simplified as they are parsed, while the
//! tactic's output (and the model its converter builds) depends on the raw
//! shape: n-ary `bvadd`/`bvmul`, `(to_real 3)` coercions, quantifiers kept
//! as written. So the asserted s-expressions are rebuilt here into a small
//! hash-consed arena of z3-shaped terms ([`Raw`]); the tactic rewrites that
//! goal round by round, replacing an application whose unconstrained
//! arguments let it take any value by a fresh constant `k!n`, and records the
//! generic model converter that recovers the eliminated constants.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::{String, ToString};
use alloc::vec;
use alloc::vec::Vec;

use puremp::{Int, Rational};

use super::{Context, SExpr, parse_bv_literal, parse_numeral, render_bv_field, render_int};
use crate::ast::AstId;
use crate::cmd_context::smt2_pp::{PpBinder, PpNode, pp_term_with};
use crate::util::symbol::smt2_symbol;

/// A node of the [`Raw`] arena.
pub(super) type RId = usize;

/// The head of a raw term.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(super) enum ROp {
    True,
    False,
    /// A declared constant.
    Const(String),
    /// A fresh constant `k!n` (`mk_fresh_const`).
    Fresh(u32),
    /// A bound variable, by its (printed) name.
    Var(String),
    /// An arithmetic numeral; `true` when it is an integer.
    Num(Rational, bool),
    /// A bit-vector numeral: value and width.
    Bv(Int, u32),
    /// A built-in operator by its SMT-LIB name, with its indices.
    Op(String, Vec<u32>),
    /// An application of a declared function.
    Uf(String),
    /// A quantifier (`true`: `forall`) over the `(name, sort)` binders; its
    /// one argument is the body.
    Quant(bool, Vec<(String, AstId)>),
}

/// A raw term: head, arguments and sort.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub(super) struct RNode {
    pub op: ROp,
    pub args: Vec<RId>,
    pub sort: AstId,
}

/// A hash-consed arena of raw terms (equal terms are one node, as z3's
/// `ast_manager` shares them).
pub(super) struct Raw {
    pub nodes: Vec<RNode>,
    index: BTreeMap<RNode, RId>,
    /// The bound variables occurring free in each node.
    free: Vec<Vec<String>>,
    pub bool_sort: AstId,
}

impl Raw {
    pub fn new(bool_sort: AstId) -> Raw {
        Raw {
            nodes: Vec::new(),
            index: BTreeMap::new(),
            free: Vec::new(),
            bool_sort,
        }
    }

    /// The node `op(args) : sort`.
    pub fn mk(&mut self, op: ROp, args: Vec<RId>, sort: AstId) -> RId {
        let n = RNode { op, args, sort };
        if let Some(&id) = self.index.get(&n) {
            return id;
        }
        let mut free: Vec<String> = Vec::new();
        match &n.op {
            ROp::Var(v) => free.push(v.clone()),
            ROp::Quant(_, vars) => {
                for v in &self.free[n.args[0]] {
                    if !vars.iter().any(|(b, _)| b == v) {
                        free.push(v.clone());
                    }
                }
            }
            _ => {
                for &a in &n.args {
                    for v in &self.free[a] {
                        if !free.contains(v) {
                            free.push(v.clone());
                        }
                    }
                }
            }
        }
        let id = self.nodes.len();
        self.nodes.push(n.clone());
        self.index.insert(n, id);
        self.free.push(free);
        id
    }

    fn op(&self, t: RId) -> &ROp {
        &self.nodes[t].op
    }

    fn args(&self, t: RId) -> &[RId] {
        &self.nodes[t].args
    }

    fn sort(&self, t: RId) -> AstId {
        self.nodes[t].sort
    }

    /// z3's `is_ground`: no free bound variable.
    fn is_ground(&self, t: RId) -> bool {
        self.free[t].is_empty()
    }

    /// z3's `is_uninterp_const`: a declared or fresh constant.
    fn is_uninterp_const(&self, t: RId) -> bool {
        matches!(self.op(t), ROp::Const(_) | ROp::Fresh(_))
    }

    fn is_op(&self, t: RId, name: &str) -> bool {
        matches!(self.op(t), ROp::Op(n, _) if n == name)
    }

    pub fn mk_true(&mut self) -> RId {
        self.mk(ROp::True, vec![], self.bool_sort)
    }

    pub fn mk_false(&mut self) -> RId {
        self.mk(ROp::False, vec![], self.bool_sort)
    }

    /// A built-in application without indices.
    pub fn app(&mut self, name: &str, args: Vec<RId>, sort: AstId) -> RId {
        self.mk(ROp::Op(name.to_string(), vec![]), args, sort)
    }

    pub fn mk_not(&mut self, a: RId) -> RId {
        let b = self.bool_sort;
        self.app("not", vec![a], b)
    }

    pub fn mk_eq(&mut self, a: RId, b: RId) -> RId {
        let s = self.bool_sort;
        self.app("=", vec![a, b], s)
    }

    pub fn mk_ite(&mut self, c: RId, t: RId, e: RId) -> RId {
        let s = self.sort(t);
        self.app("ite", vec![c, t, e], s)
    }
}

/// A binding of the raw parser's environment.
#[derive(Clone)]
enum Bind {
    /// A quantified variable: its sort and printed name.
    Var(AstId, String),
    /// A `let`-bound term (or a macro parameter).
    Term(RId),
}

/// The z3 operators whose application to more than two arguments stays
/// n-ary (`flat_associative`).
const FLAT: &[&str] = &[
    "and", "or", "+", "*", "bvadd", "bvmul", "bvand", "bvor", "bvxor", "bvxnor",
];

/// The associative operators the printer flattens (`is_associative`).
fn is_assoc(head: &str) -> bool {
    FLAT.contains(&head) || head == "xor"
}

/// One entry of the generic model converter, in creation order.
#[derive(Clone, Debug)]
pub(super) enum McEntry {
    /// `hide`: the fresh constant is dropped from the model.
    Hide(RId),
    /// `add`: the constant's value is its definition evaluated in the model.
    Add(RId, RId),
}

/// The result of running the tactic on a goal.
pub(super) struct ElimResult {
    /// The residual goal (`[false]` when inconsistent).
    pub goal: Vec<RId>,
    /// Whether the tactic ran (the goal's depth grew).
    pub depth: u32,
    pub mc: Vec<McEntry>,
}

impl Context {
    /// The current assertions as z3's parser builds them, split into the
    /// goal's formulas as `goal::assert_expr` does; `None` when some
    /// assertion uses a construct the raw parser does not model.
    pub(super) fn raw_goal(&mut self, raw: &mut Raw) -> Option<Vec<RId>> {
        let forms: Vec<SExpr> = self.raw_asserts.iter().map(|(_, e)| e.clone()).collect();
        let mut goal: Vec<RId> = Vec::new();
        let mut inconsistent = false;
        for f in &forms {
            let t = self.raw_term(raw, f, &mut Vec::new(), 0)?;
            if raw.sort(t) != raw.bool_sort {
                return None;
            }
            quick_process(raw, &mut goal, &mut inconsistent, None, t);
        }
        if inconsistent {
            let f = raw.mk_false();
            return Some(vec![f]);
        }
        Some(goal)
    }

    /// Build the raw term of `e` in the environment `env` (innermost binding
    /// last).
    fn raw_term(
        &mut self,
        raw: &mut Raw,
        e: &SExpr,
        env: &mut Vec<(String, Bind)>,
        depth: u32,
    ) -> Option<RId> {
        if depth > 500 {
            return None;
        }
        let bool_s = raw.bool_sort;
        match e {
            SExpr::Atom(a) => {
                if let Some((_, b)) = env.iter().rev().find(|(n, _)| n == a) {
                    return Some(match b.clone() {
                        Bind::Var(s, name) => raw.mk(ROp::Var(name), vec![], s),
                        Bind::Term(t) => t,
                    });
                }
                match a.as_str() {
                    "true" => return Some(raw.mk_true()),
                    "false" => return Some(raw.mk_false()),
                    _ => {}
                }
                if let Some((v, w)) = parse_bv_literal(a) {
                    let s = self.m.mk_bv_sort(w);
                    return Some(raw.mk(ROp::Bv(v, w), vec![], s));
                }
                if a.starts_with(|c: char| c.is_ascii_digit()) {
                    let (r, is_int) = parse_numeral(a)?;
                    let s = if is_int {
                        self.m.mk_int_sort()
                    } else {
                        self.m.mk_real_sort()
                    };
                    return Some(raw.mk(ROp::Num(r, is_int), vec![], s));
                }
                if let Some((ps, body)) = self.macros.get(a).cloned() {
                    if !ps.is_empty() {
                        return None;
                    }
                    return self.raw_term(raw, &body, &mut Vec::new(), depth + 1);
                }
                let d = *self.funcs.get(a)?;
                let fd = self.m.func_decl(d)?;
                if !fd.domain.is_empty() {
                    return None;
                }
                let s = fd.range;
                Some(raw.mk(ROp::Const(a.clone()), vec![], s))
            }
            SExpr::List(l) if l.is_empty() => None,
            SExpr::List(l) => {
                if let SExpr::List(h) = &l[0] {
                    // An indexed operator `((_ extract 7 0) x)`.
                    let [SExpr::Atom(u), SExpr::Atom(name), idx @ ..] = h.as_slice() else {
                        return None;
                    };
                    if u != "_" {
                        return None;
                    }
                    let idx: Vec<u32> = idx
                        .iter()
                        .map(|i| match i {
                            SExpr::Atom(i) => i.parse().ok(),
                            SExpr::List(_) => None,
                        })
                        .collect::<Option<_>>()?;
                    let mut args = Vec::with_capacity(l.len() - 1);
                    for a in &l[1..] {
                        args.push(self.raw_term(raw, a, env, depth + 1)?);
                    }
                    return self.raw_indexed(raw, name, idx, args);
                }
                let SExpr::Atom(head) = &l[0] else {
                    return None;
                };
                match head.as_str() {
                    "_" => {
                        // `(_ bvN w)`.
                        let [_, SExpr::Atom(v), SExpr::Atom(w)] = l.as_slice() else {
                            return None;
                        };
                        let v = Int::from_str_radix(v.strip_prefix("bv")?, 10).ok()?;
                        let w: u32 = w.parse().ok()?;
                        if w == 0 {
                            return None;
                        }
                        let s = self.m.mk_bv_sort(w);
                        let v = v.mod_2k(u64::from(w));
                        return Some(raw.mk(ROp::Bv(v, w), vec![], s));
                    }
                    "let" => {
                        let SExpr::List(binds) = l.get(1)? else {
                            return None;
                        };
                        if l.len() != 3 {
                            return None;
                        }
                        let mut bound = Vec::with_capacity(binds.len());
                        for b in binds {
                            let SExpr::List(p) = b else { return None };
                            let [SExpr::Atom(n), t] = p.as_slice() else {
                                return None;
                            };
                            bound.push((n.clone(), self.raw_term(raw, t, env, depth + 1)?));
                        }
                        let n = env.len();
                        for (name, t) in bound {
                            env.push((name, Bind::Term(t)));
                        }
                        let r = self.raw_term(raw, &l[2], env, depth + 1);
                        env.truncate(n);
                        return r;
                    }
                    "forall" | "exists" => {
                        let SExpr::List(binds) = l.get(1)? else {
                            return None;
                        };
                        if l.len() != 3 || binds.is_empty() {
                            return None;
                        }
                        let mut vars = Vec::with_capacity(binds.len());
                        for b in binds {
                            let SExpr::List(p) = b else { return None };
                            let [SExpr::Atom(n), srt] = p.as_slice() else {
                                return None;
                            };
                            // Shadowing and names the printer would rename
                            // are not modelled.
                            if env.iter().any(|(m, _)| m == n)
                                || vars.iter().any(|(m, _)| m == n)
                                || self.funcs.contains_key(n)
                                || self.macros.contains_key(n)
                            {
                                return None;
                            }
                            let s = self.resolve_sort(srt).ok()?;
                            vars.push((n.clone(), s));
                        }
                        let n = env.len();
                        for (name, s) in &vars {
                            env.push((name.clone(), Bind::Var(*s, name.clone())));
                        }
                        let body = self.raw_term(raw, &l[2], env, depth + 1);
                        env.truncate(n);
                        let body = body?;
                        if raw.sort(body) != bool_s {
                            return None;
                        }
                        return Some(raw.mk(
                            ROp::Quant(head == "forall", vars),
                            vec![body],
                            bool_s,
                        ));
                    }
                    "!" => {
                        // Only `:named` annotations (patterns are not modelled).
                        let attrs = &l[2..];
                        if attrs.len() != 2 || !matches!(&attrs[0], SExpr::Atom(k) if k == ":named")
                        {
                            return None;
                        }
                        return self.raw_term(raw, l.get(1)?, env, depth + 1);
                    }
                    _ => {}
                }
                let mut args = Vec::with_capacity(l.len() - 1);
                for a in &l[1..] {
                    args.push(self.raw_term(raw, a, env, depth + 1)?);
                }
                if let Some((ps, body)) = self.macros.get(head.as_str()).cloned() {
                    if ps.len() != args.len() || ps.is_empty() {
                        return None;
                    }
                    let mut menv: Vec<(String, Bind)> = ps
                        .into_iter()
                        .zip(args)
                        .map(|(p, a)| (p, Bind::Term(a)))
                        .collect();
                    return self.raw_term(raw, &body, &mut menv, depth + 1);
                }
                if let Some(t) = self.raw_builtin(raw, head, args.clone()) {
                    return Some(t);
                }
                if is_builtin_name(head) {
                    return None;
                }
                let d = *self.funcs.get(head.as_str())?;
                let fd = self.m.func_decl(d)?;
                if fd.domain.len() != args.len()
                    || fd.domain.iter().zip(&args).any(|(&s, &a)| s != raw.sort(a))
                {
                    return None;
                }
                let s = fd.range;
                Some(raw.mk(ROp::Uf(head.clone()), args, s))
            }
        }
    }

    /// An indexed bit-vector operator application.
    fn raw_indexed(
        &mut self,
        raw: &mut Raw,
        name: &str,
        idx: Vec<u32>,
        args: Vec<RId>,
    ) -> Option<RId> {
        if args.len() != 1 {
            return None;
        }
        let w = self.m.bv_sort_width(raw.sort(args[0]))?;
        let rw = match (name, idx.as_slice()) {
            ("extract", &[h, lo]) if lo <= h && h < w => h - lo + 1,
            ("zero_extend" | "sign_extend", &[k]) => w + k,
            ("repeat", &[k]) if k >= 1 => w * k,
            ("rotate_left" | "rotate_right", &[_]) => w,
            _ => return None,
        };
        let s = self.m.mk_bv_sort(rw);
        Some(raw.mk(ROp::Op(name.to_string(), idx), args, s))
    }

    /// A core, arithmetic or bit-vector application as z3's `mk_app` builds
    /// it (with its Int-to-Real coercions); `None` for anything else.
    fn raw_builtin(&mut self, raw: &mut Raw, head: &str, mut args: Vec<RId>) -> Option<RId> {
        let b = raw.bool_sort;
        let n = args.len();
        let all_bool = |raw: &Raw, args: &[RId]| args.iter().all(|&a| raw.sort(a) == b);
        match head {
            "not" if n == 1 && all_bool(raw, &args) => return Some(raw.app("not", args, b)),
            "and" | "or" if all_bool(raw, &args) => {
                return Some(match n {
                    // `mk_app` of a 0-ary `and`/`or` is the unit.
                    0 if head == "and" => raw.mk_true(),
                    0 => raw.mk_false(),
                    _ => raw.app(head, args, b),
                });
            }
            "=>" | "xor" if n >= 2 && all_bool(raw, &args) => {
                // `=>` is right-, `xor` left-associative.
                return Some(if head == "=>" {
                    let mut r = args[n - 1];
                    for &a in args[..n - 1].iter().rev() {
                        r = raw.app("=>", vec![a, r], b);
                    }
                    r
                } else {
                    let mut r = args[0];
                    for &a in &args[1..] {
                        r = raw.app("xor", vec![r, a], b);
                    }
                    r
                });
            }
            "ite" if n == 3 && raw.sort(args[0]) == b => {
                self.coerce(raw, &mut args[1..])?;
                let s = raw.sort(args[1]);
                return Some(raw.app("ite", args, s));
            }
            "=" | "distinct" if n >= 2 => {
                self.coerce(raw, &mut args)?;
                if head == "distinct" {
                    return Some(raw.app("distinct", args, b));
                }
                if n == 2 {
                    return Some(raw.mk_eq(args[0], args[1]));
                }
                // Chainable: the conjunction of the adjacent equalities.
                let eqs: Vec<RId> = args.windows(2).map(|w| raw.mk_eq(w[0], w[1])).collect();
                return Some(raw.app("and", eqs, b));
            }
            _ => {}
        }
        if n == 0 {
            return None;
        }
        let int_s = self.m.mk_int_sort();
        let real_s = self.m.mk_real_sort();
        let is_arith = |raw: &Raw, a: RId| raw.sort(a) == int_s || raw.sort(a) == real_s;
        match head {
            "+" | "*" | "-" | "/" | "<=" | "<" | ">=" | ">" | "div" | "mod" | "rem" | "abs"
            | "to_real" | "to_int" | "is_int" => {
                if !args.iter().all(|&a| is_arith(raw, a)) {
                    return None;
                }
                let one = n == 1;
                match head {
                    "-" if one => {
                        let s = raw.sort(args[0]);
                        return Some(raw.app("-", args, s));
                    }
                    "abs" if one => {
                        let s = raw.sort(args[0]);
                        return Some(raw.app("abs", args, s));
                    }
                    "to_real" if one && raw.sort(args[0]) == int_s => {
                        return Some(raw.app("to_real", args, real_s));
                    }
                    "to_int" if one && raw.sort(args[0]) == real_s => {
                        return Some(raw.app("to_int", args, int_s));
                    }
                    "is_int" if one && raw.sort(args[0]) == real_s => {
                        return Some(raw.app("is_int", args, b));
                    }
                    "+" | "*" if !one => {
                        self.coerce(raw, &mut args)?;
                        let s = raw.sort(args[0]);
                        return Some(raw.app(head, args, s));
                    }
                    "-" | "/" => {
                        if head == "/" {
                            for a in args.iter_mut() {
                                if raw.sort(*a) == int_s {
                                    *a = raw.app("to_real", vec![*a], real_s);
                                }
                            }
                        } else {
                            self.coerce(raw, &mut args)?;
                        }
                        let s = raw.sort(args[0]);
                        let mut r = args[0];
                        for &a in &args[1..] {
                            r = raw.app(head, vec![r, a], s);
                        }
                        return Some(r);
                    }
                    "div" | "mod" | "rem" if args.iter().all(|&a| raw.sort(a) == int_s) => {
                        if head != "div" && n != 2 {
                            return None;
                        }
                        let mut r = args[0];
                        for &a in &args[1..] {
                            r = raw.app(head, vec![r, a], int_s);
                        }
                        return Some(r);
                    }
                    "<=" | "<" | ">=" | ">" if n == 2 => {
                        self.coerce(raw, &mut args)?;
                        return Some(raw.app(head, args, b));
                    }
                    _ => return None,
                }
            }
            _ => {}
        }
        // Bit-vector operators: every argument of one width.
        let w = self.m.bv_sort_width(raw.sort(args[0]))?;
        if head == "concat" {
            let mut total = 0;
            for &a in &args {
                total += self.m.bv_sort_width(raw.sort(a))?;
            }
            let s = self.m.mk_bv_sort(total);
            return Some(raw.app("concat", args, s));
        }
        let s = raw.sort(args[0]);
        if args.iter().any(|&a| raw.sort(a) != s) {
            return None;
        }
        match head {
            "bvneg" | "bvnot" if n == 1 => Some(raw.app(head, args, s)),
            h if FLAT.contains(&h) && h.starts_with("bv") && n >= 2 => Some(raw.app(head, args, s)),
            "bvsub" | "bvudiv" | "bvsdiv" | "bvurem" | "bvsrem" | "bvsmod" | "bvshl" | "bvlshr"
            | "bvashr" | "bvnand" | "bvnor"
                if n == 2 =>
            {
                Some(raw.app(head, args, s))
            }
            "bvcomp" if n == 2 => {
                let s1 = self.m.mk_bv_sort(1);
                Some(raw.app(head, args, s1))
            }
            "bvule" | "bvult" | "bvuge" | "bvugt" | "bvsle" | "bvslt" | "bvsge" | "bvsgt"
                if n == 2 =>
            {
                let _ = w;
                Some(raw.app(head, args, b))
            }
            _ => None,
        }
    }

    /// z3's Int-to-Real coercion of mixed arithmetic arguments: when one is
    /// Real, the Int ones are wrapped in `to_real`. `None` on a sort clash.
    fn coerce(&mut self, raw: &mut Raw, args: &mut [RId]) -> Option<()> {
        let int_s = self.m.mk_int_sort();
        let real_s = self.m.mk_real_sort();
        let has_real = args.iter().any(|&a| raw.sort(a) == real_s);
        if has_real {
            for a in args.iter_mut() {
                if raw.sort(*a) == int_s {
                    *a = raw.app("to_real", vec![*a], real_s);
                }
            }
        }
        let s = raw.sort(args[0]);
        args.iter().all(|&a| raw.sort(a) == s).then_some(())
    }

    /// Render the goal `forms` as z3's `goal::display` does, with `depth`.
    pub(super) fn raw_goal_display(&self, raw: &Raw, forms: &[RId], depth: u32) -> String {
        let mut out = String::from("(goals\n(goal");
        for &f in forms {
            out.push_str("\n  ");
            out.push_str(&self.raw_pp(raw, f, 2));
        }
        out.push_str(&alloc::format!("\n  :precision precise :depth {depth})\n)"));
        out
    }

    /// Pretty-print raw term `t` as `ast_smt2_pp` at indentation `ind`.
    pub(super) fn raw_pp(&self, raw: &Raw, t: RId, ind: usize) -> String {
        let mut nodes: Vec<PpNode> = Vec::new();
        let mut binders: BTreeMap<usize, PpBinder> = BTreeMap::new();
        let mut map: BTreeMap<RId, usize> = BTreeMap::new();
        // Post-order over the reachable nodes.
        let mut stack: Vec<(RId, bool)> = vec![(t, false)];
        while let Some((n, done)) = stack.pop() {
            if map.contains_key(&n) {
                continue;
            }
            if !done {
                stack.push((n, true));
                for &a in raw.args(n).iter().rev() {
                    stack.push((a, false));
                }
                continue;
            }
            let node = &raw.nodes[n];
            let (head, indexed) = match &node.op {
                ROp::True => ("true".to_string(), false),
                ROp::False => ("false".to_string(), false),
                ROp::Const(c) | ROp::Uf(c) => (smt2_symbol(c).into_owned(), false),
                ROp::Fresh(k) => (alloc::format!("k!{k}"), false),
                ROp::Var(v) => (smt2_symbol(v).into_owned(), false),
                ROp::Num(r, is_int) => (render_raw_num(r, *is_int), false),
                ROp::Bv(v, w) => (render_raw_bv(v, *w), false),
                ROp::Op(name, idx) if idx.is_empty() => (name.clone(), false),
                ROp::Op(name, idx) => {
                    let mut h = alloc::format!("(_ {name}");
                    for i in idx {
                        h.push_str(&alloc::format!(" {i}"));
                    }
                    h.push(')');
                    (h, true)
                }
                ROp::Quant(forall, vars) => {
                    let vs = vars
                        .iter()
                        .map(|(v, s)| (smt2_symbol(v).into_owned(), self.sort_display(*s)))
                        .collect();
                    binders.insert(
                        nodes.len(),
                        PpBinder {
                            header: if *forall { "forall" } else { "exists" }.to_string(),
                            vars: vs,
                        },
                    );
                    (String::new(), false)
                }
            };
            let args = node.args.iter().map(|a| map[a]).collect();
            map.insert(n, nodes.len());
            nodes.push(PpNode {
                head,
                args,
                indexed,
            });
        }
        pp_term_with(&nodes, map[&t], &is_assoc, &binders, ind)
    }
}

/// A raw arithmetic numeral as z3 prints it.
fn render_raw_num(r: &Rational, is_int: bool) -> String {
    if is_int {
        return render_int(r.numerator());
    }
    let neg = r.is_negative();
    let a = r.abs();
    let body = if a.is_integer() {
        alloc::format!("{}.0", a.numerator())
    } else {
        alloc::format!("(/ {}.0 {}.0)", a.numerator(), a.denominator())
    };
    if neg {
        alloc::format!("(- {body})")
    } else {
        body
    }
}

/// A raw bit-vector numeral as z3 prints it (`#x…` / `#b…`).
fn render_raw_bv(v: &Int, w: u32) -> String {
    if w <= 64 {
        return render_bv_field(v.to_u64().unwrap_or(0), w);
    }
    let (radix, digits, prefix) = if w.is_multiple_of(4) {
        (16, w as usize / 4, "#x")
    } else {
        (2, w as usize, "#b")
    };
    let mut s = String::new();
    let _ = v.write_radix(&mut s, radix);
    alloc::format!("{prefix}{}{s}", "0".repeat(digits.saturating_sub(s.len())))
}

/// Whether `name` is an operator the raw parser would have to build itself
/// (so an unmodelled use of it must not be taken for a declared function).
fn is_builtin_name(name: &str) -> bool {
    matches!(
        name,
        "not" | "and" | "or" | "=>" | "xor" | "ite" | "=" | "distinct" | "+" | "-" | "*" | "/"
    ) || name.starts_with("bv")
        || name.starts_with("fp")
        || name.starts_with("str.")
        || name.starts_with("seq.")
        || name.starts_with("re.")
        || matches!(
            name,
            "div"
                | "mod"
                | "rem"
                | "abs"
                | "to_real"
                | "to_int"
                | "is_int"
                | "<="
                | "<"
                | ">="
                | ">"
                | "concat"
                | "select"
                | "store"
                | "as"
                | "^"
                | "root-obj"
        )
}

/// `goal::quick_process`: add formula `f` to the goal, splitting
/// conjunctions and negated disjunctions; with `slot`, the first piece
/// replaces that formula (`goal::update`) and the others are appended.
fn quick_process(
    raw: &mut Raw,
    goal: &mut Vec<RId>,
    inconsistent: &mut bool,
    slot: Option<usize>,
    f: RId,
) {
    if *inconsistent {
        return;
    }
    let is_not_or = |raw: &Raw, f: RId| raw.is_op(f, "not") && raw.is_op(raw.args(f)[0], "or");
    let push = |raw: &mut Raw, goal: &mut Vec<RId>, inc: &mut bool, f: RId| match raw.op(f) {
        ROp::True => {}
        ROp::False => {
            *inc = true;
            goal.clear();
            let ff = raw.mk_false();
            goal.push(ff);
        }
        _ => goal.push(f),
    };
    if !raw.is_op(f, "and") && !is_not_or(raw, f) {
        match slot {
            None => push(raw, goal, inconsistent, f),
            Some(i) if matches!(raw.op(f), ROp::False) => {
                let _ = i;
                push(raw, goal, inconsistent, f);
            }
            Some(i) => goal[i] = f,
        }
        return;
    }
    let mut save = slot;
    let mut todo: Vec<(RId, bool)> = vec![(f, true)];
    while let Some((curr, pol)) = todo.pop() {
        if *inconsistent {
            return;
        }
        if pol && raw.is_op(curr, "and") {
            for &a in raw.args(curr).to_vec().iter().rev() {
                todo.push((a, true));
            }
        } else if !pol && raw.is_op(curr, "or") {
            for &a in raw.args(curr).to_vec().iter().rev() {
                todo.push((a, false));
            }
        } else if raw.is_op(curr, "not") {
            todo.push((raw.args(curr)[0], !pol));
        } else {
            let c = if pol { curr } else { raw.mk_not(curr) };
            match save.take() {
                Some(i) => {
                    if matches!(raw.op(c), ROp::False) {
                        push(raw, goal, inconsistent, c);
                    } else {
                        goal[i] = c;
                    }
                }
                None => push(raw, goal, inconsistent, c),
            }
        }
    }
}

/// The rewriter configuration and state of one tactic run (`rw_cfg`).
struct Elim<'a> {
    ctx: &'a mut Context,
    raw: &'a mut Raw,
    vars: BTreeSet<RId>,
    disabled: BTreeSet<RId>,
    /// Applications already abstracted, and their fresh constants.
    cache: BTreeMap<RId, RId>,
    /// This round's rewriting results.
    memo: BTreeMap<RId, RId>,
    mc: Vec<McEntry>,
}

impl Elim<'_> {
    fn uncnstr(&self, t: RId) -> bool {
        self.vars.contains(&t) && !self.disabled.contains(&t)
    }

    fn all_uncnstr(&self, ts: &[RId]) -> bool {
        ts.iter().all(|&t| self.uncnstr(t))
    }

    /// `mk_fresh_uncnstr_var_for`: the fresh constant abstracting `t`, and
    /// whether it is new.
    fn fresh_for(&mut self, t: RId) -> (RId, bool) {
        if let Some(&v) = self.cache.get(&t) {
            return (v, false);
        }
        let k = self.ctx.uncnstr_fresh;
        self.ctx.uncnstr_fresh += 1;
        let s = self.raw.sort(t);
        let v = self.raw.mk(ROp::Fresh(k), vec![], s);
        self.mc.push(McEntry::Hide(v));
        self.cache.insert(t, v);
        (v, true)
    }

    fn add_def(&mut self, v: RId, def: RId) {
        self.mc.push(McEntry::Add(v, def));
    }

    fn add_defs(&mut self, args: &[RId], u: RId, identity: RId) {
        self.add_def(args[0], u);
        for &a in &args[1..] {
            self.add_def(a, identity);
        }
    }

    fn arith_num(&mut self, v: Rational, sort: AstId) -> RId {
        let is_int = self.ctx.m.is_int_sort(sort);
        self.raw.mk(ROp::Num(v, is_int), vec![], sort)
    }

    fn bv_num(&mut self, v: Int, w: u32) -> RId {
        let s = self.ctx.m.mk_bv_sort(w);
        let v = v.mod_2k(u64::from(w));
        self.raw.mk(ROp::Bv(v, w), vec![], s)
    }

    fn bv_width(&self, t: RId) -> u32 {
        self.ctx.m.bv_sort_width(self.raw.sort(t)).unwrap_or(0)
    }

    /// `mk_diff`: a term different from `t`.
    fn mk_diff(&mut self, t: RId) -> Option<RId> {
        let s = self.raw.sort(t);
        if s == self.raw.bool_sort {
            return Some(self.raw.mk_not(t));
        }
        if self.ctx.m.is_arith_sort(s) {
            let one = self.arith_num(Rational::from(1), s);
            return Some(self.raw.app("+", vec![t, one], s));
        }
        if self.ctx.m.bv_sort_width(s).is_some() {
            return Some(self.raw.app("bvnot", vec![t], s));
        }
        None
    }

    /// The tactic's rewriting of formula `t` (post-order, memoized).
    fn rewrite(&mut self, t: RId) -> RId {
        let mut stack: Vec<(RId, bool)> = vec![(t, false)];
        while let Some((n, done)) = stack.pop() {
            if self.memo.contains_key(&n) {
                continue;
            }
            let args = self.raw.args(n).to_vec();
            // Quantified bodies are disabled: nothing below changes.
            if args.is_empty() || matches!(self.raw.op(n), ROp::Quant(..)) {
                self.memo.insert(n, n);
                continue;
            }
            if !done {
                stack.push((n, true));
                for &a in args.iter().rev() {
                    stack.push((a, false));
                }
                continue;
            }
            let new_args: Vec<RId> = args.iter().map(|a| self.memo[a]).collect();
            let r = match self.reduce_app(n, &new_args) {
                Some(r) => r,
                None if new_args == args => n,
                None => {
                    let node = &self.raw.nodes[n];
                    let (op, s) = (node.op.clone(), node.sort);
                    self.raw.mk(op, new_args, s)
                }
            };
            self.memo.insert(n, r);
        }
        self.memo[&t]
    }

    /// `reduce_app` of node `n`'s head over the rewritten `args`.
    fn reduce_app(&mut self, n: RId, args: &[RId]) -> Option<RId> {
        let ROp::Op(name, idx) = self.raw.op(n).clone() else {
            return None;
        };
        if args.iter().any(|&a| !self.raw.is_ground(a)) {
            return None;
        }
        let sort = self.raw.sort(n);
        let app = |s: &mut Self| {
            s.raw
                .mk(ROp::Op(name.clone(), idx.clone()), args.to_vec(), sort)
        };
        let num = args.len();
        match name.as_str() {
            "ite" => {
                let pick = if self.uncnstr(args[1]) && self.uncnstr(args[2]) {
                    0
                } else if self.uncnstr(args[0]) && self.uncnstr(args[1]) {
                    1
                } else if self.uncnstr(args[0]) && self.uncnstr(args[2]) {
                    2
                } else {
                    return None;
                };
                let t = app(self);
                let (r, new) = self.fresh_for(t);
                if !new {
                    return Some(r);
                }
                match pick {
                    0 => {
                        self.add_def(args[1], r);
                        self.add_def(args[2], r);
                    }
                    1 => {
                        let tt = self.raw.mk_true();
                        self.add_def(args[0], tt);
                        self.add_def(args[1], r);
                    }
                    _ => {
                        let ff = self.raw.mk_false();
                        self.add_def(args[0], ff);
                        self.add_def(args[2], r);
                    }
                }
                Some(r)
            }
            "not" if sort == self.raw.bool_sort => {
                if !self.uncnstr(args[0]) {
                    return None;
                }
                let t = app(self);
                let (r, new) = self.fresh_for(t);
                if new {
                    let d = self.raw.mk_not(r);
                    self.add_def(args[0], d);
                }
                Some(r)
            }
            "and" | "or" => {
                if !self.all_uncnstr(args) {
                    return None;
                }
                let t = app(self);
                let (r, new) = self.fresh_for(t);
                if new {
                    let id = if name == "and" {
                        self.raw.mk_true()
                    } else {
                        self.raw.mk_false()
                    };
                    self.add_defs(args, r, id);
                }
                Some(r)
            }
            "=" => self.process_eq(args[0], args[1]),
            "+" => self.process_add("+", "-", args, sort),
            "bvadd" => self.process_add("bvadd", "bvsub", args, sort),
            "*" => {
                if self.all_uncnstr(args) {
                    let t = app(self);
                    let (r, new) = self.fresh_for(t);
                    if new {
                        let one = self.arith_num(Rational::from(1), sort);
                        self.add_defs(args, r, one);
                    }
                    return Some(r);
                }
                // c * v for reals.
                let ROp::Num(val, false) = self.raw.op(args[0]).clone() else {
                    return None;
                };
                if num != 2 || !self.uncnstr(args[1]) || val.is_zero() {
                    return None;
                }
                let t = app(self);
                let (r, new) = self.fresh_for(t);
                if new {
                    let inv = self.arith_num(val.recip(), sort);
                    let d = self.raw.app("*", vec![inv, r], sort);
                    self.add_def(args[1], d);
                }
                Some(r)
            }
            "<=" | ">=" if self.ctx.m.is_arith_sort(self.raw.sort(args[0])) => {
                let mut le = name == "<=";
                let (v, t) = if self.uncnstr(args[0]) {
                    (args[0], args[1])
                } else if self.uncnstr(args[1]) {
                    le = !le;
                    (args[1], args[0])
                } else {
                    return None;
                };
                let a = app(self);
                let (u, new) = self.fresh_for(a);
                if new {
                    let s = self.raw.sort(args[0]);
                    let k = self.arith_num(Rational::from(if le { 1 } else { -1 }), s);
                    let tk = self.raw.app("+", vec![t, k], s);
                    let d = self.raw.mk_ite(u, t, tk);
                    self.add_def(v, d);
                }
                Some(u)
            }
            "bvmul" => {
                if self.all_uncnstr(args) {
                    let t = app(self);
                    let (r, new) = self.fresh_for(t);
                    if new {
                        let w = self.bv_width(args[0]);
                        let one = self.bv_num(Int::from(1), w);
                        self.add_defs(args, r, one);
                    }
                    return Some(r);
                }
                let ROp::Bv(val, w) = self.raw.op(args[0]).clone() else {
                    return None;
                };
                if num != 2 || !self.uncnstr(args[1]) || !val.is_odd() {
                    return None;
                }
                let inv = val.modinv(&Int::from(1).mul_2k(u64::from(w)))?;
                let t = app(self);
                let (r, new) = self.fresh_for(t);
                if new {
                    let c = self.bv_num(inv, w);
                    let d = self.raw.app("bvmul", vec![c, r], sort);
                    self.add_def(args[1], d);
                }
                Some(r)
            }
            "bvsdiv" | "bvudiv" => {
                if !(self.uncnstr(args[0]) && self.uncnstr(args[1])) {
                    return None;
                }
                let t = app(self);
                let (r, new) = self.fresh_for(t);
                if new {
                    let w = self.bv_width(args[0]);
                    let one = self.bv_num(Int::from(1), w);
                    self.add_def(args[0], r);
                    self.add_def(args[1], one);
                }
                Some(r)
            }
            "bvsle" | "bvule" => {
                let signed = name == "bvsle";
                let w = self.bv_width(args[0]);
                let (v, t, upper) = if self.uncnstr(args[0]) {
                    (args[0], args[1], true)
                } else if self.uncnstr(args[1]) {
                    (args[1], args[0], false)
                } else {
                    return None;
                };
                // v <= t  ->  u or t = MAX;  t <= v  ->  u or t = MIN.
                let bound = match (upper, signed) {
                    (true, true) => Int::from(1).mul_2k(u64::from(w - 1)) - Int::from(1),
                    (true, false) => Int::from(1).mul_2k(u64::from(w)) - Int::from(1),
                    (false, true) => Int::from(1).mul_2k(u64::from(w - 1)),
                    (false, false) => Int::from(0),
                };
                let a = app(self);
                let (u, new) = self.fresh_for(a);
                let bnd = self.bv_num(bound, w);
                let eq = self.raw.mk_eq(t, bnd);
                let b = self.raw.bool_sort;
                let r = self.raw.app("or", vec![u, eq], b);
                if new {
                    let s = self.raw.sort(t);
                    let one = self.bv_num(Int::from(1), w);
                    let step = self
                        .raw
                        .app(if upper { "bvadd" } else { "bvsub" }, vec![t, one], s);
                    let d = self.raw.mk_ite(r, t, step);
                    self.add_def(v, d);
                }
                Some(r)
            }
            "concat" => {
                if !self.all_uncnstr(args) {
                    return None;
                }
                let t = app(self);
                let (r, new) = self.fresh_for(t);
                if new {
                    let mut low = 0;
                    for &a in args.iter().rev() {
                        let sz = self.bv_width(a);
                        let s = self.raw.sort(a);
                        let d = self.raw.mk(
                            ROp::Op("extract".to_string(), vec![low + sz - 1, low]),
                            vec![r],
                            s,
                        );
                        self.add_def(a, d);
                        low += sz;
                    }
                }
                Some(r)
            }
            "extract" => {
                if !self.uncnstr(args[0]) {
                    return None;
                }
                let t = app(self);
                let (r, new) = self.fresh_for(t);
                if new {
                    let (high, low) = (idx[0], idx[1]);
                    let w = self.bv_width(args[0]);
                    if w == high - low + 1 {
                        self.add_def(args[0], r);
                    } else {
                        let mut parts = Vec::new();
                        if high < w - 1 {
                            parts.push(self.bv_num(Int::from(0), w - high - 1));
                        }
                        parts.push(r);
                        if low > 0 {
                            parts.push(self.bv_num(Int::from(0), low));
                        }
                        let s = self.raw.sort(args[0]);
                        let d = self.raw.app("concat", parts, s);
                        self.add_def(args[0], d);
                    }
                }
                Some(r)
            }
            "bvnot" => {
                if !self.uncnstr(args[0]) {
                    return None;
                }
                let t = app(self);
                let (r, new) = self.fresh_for(t);
                if new {
                    let d = self.raw.app("bvnot", vec![r], sort);
                    self.add_def(args[0], d);
                }
                Some(r)
            }
            "bvor" => {
                if !self.all_uncnstr(args) {
                    return None;
                }
                let t = app(self);
                let (r, new) = self.fresh_for(t);
                if new {
                    let w = self.bv_width(args[0]);
                    let zero = self.bv_num(Int::from(0), w);
                    self.add_defs(args, r, zero);
                }
                Some(r)
            }
            _ => None,
        }
    }

    /// `process_eq`.
    fn process_eq(&mut self, a1: RId, a2: RId) -> Option<RId> {
        let (v, t) = if self.uncnstr(a1) {
            (a1, a2)
        } else if self.uncnstr(a2) {
            (a2, a1)
        } else {
            return None;
        };
        let s = self.raw.sort(a1);
        // Only fully interpreted sorts with more than one element.
        let m = &self.ctx.m;
        if !(s == self.raw.bool_sort || m.is_arith_sort(s) || m.bv_sort_width(s).is_some()) {
            return None;
        }
        let d = self.mk_diff(t)?;
        let e = self.raw.mk_eq(a1, a2);
        let (u, new) = self.fresh_for(e);
        if new {
            let def = self.raw.mk_ite(u, t, d);
            self.add_def(v, def);
        }
        Some(u)
    }

    /// `process_add`.
    fn process_add(&mut self, add: &str, sub: &str, args: &[RId], sort: AstId) -> Option<RId> {
        let i = args.iter().position(|&a| self.uncnstr(a))?;
        let v = args[i];
        let t = self.raw.app(add, args.to_vec(), sort);
        let (u, new) = self.fresh_for(t);
        if !new {
            return Some(u);
        }
        let rest: Vec<RId> = args
            .iter()
            .enumerate()
            .filter(|&(j, _)| j != i)
            .map(|(_, &a)| a)
            .collect();
        let def = match rest.len() {
            0 => u,
            1 => self.raw.app(sub, vec![u, rest[0]], sort),
            _ => {
                let r = self.raw.app(add, rest, sort);
                self.raw.app(sub, vec![u, r], sort)
            }
        };
        self.add_def(v, def);
        Some(u)
    }
}

/// `collect_occs`: the uninterpreted constants occurring exactly once in the
/// goal (a shared subterm's children are visited once).
fn collect_occs(raw: &Raw, goal: &[RId]) -> BTreeSet<RId> {
    let mut visited: BTreeSet<RId> = BTreeSet::new();
    let mut more: BTreeSet<RId> = BTreeSet::new();
    let mut vars: Vec<RId> = Vec::new();
    for &f in goal {
        let mut stack = vec![f];
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                if raw.is_uninterp_const(t) {
                    more.insert(t);
                }
                continue;
            }
            if raw.is_uninterp_const(t) {
                vars.push(t);
                continue;
            }
            stack.extend(raw.args(t).iter().rev());
        }
    }
    vars.into_iter().filter(|v| !more.contains(v)).collect()
}

/// `disable_quantified`: every subterm of a quantifier's body.
fn disable_quantified(raw: &Raw, goal: &[RId]) -> BTreeSet<RId> {
    let mut seen: BTreeSet<RId> = BTreeSet::new();
    let mut disabled: BTreeSet<RId> = BTreeSet::new();
    let mut stack: Vec<RId> = goal.to_vec();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        if matches!(raw.op(t), ROp::Quant(..)) {
            let mut todo = vec![raw.args(t)[0]];
            while let Some(e) = todo.pop() {
                if disabled.insert(e) {
                    todo.extend(raw.args(e).iter().copied());
                }
            }
        }
        stack.extend(raw.args(t).iter().copied());
    }
    disabled
}

impl Context {
    /// Run z3's `elim-uncnstr` on `goal` (`elim_uncnstr_tactic::run`).
    pub(super) fn elim_uncnstr(&mut self, raw: &mut Raw, mut goal: Vec<RId>) -> ElimResult {
        let mut vars = collect_occs(raw, &goal);
        let disabled = disable_quantified(raw, &goal);
        if vars.is_empty() {
            return ElimResult {
                goal,
                depth: 0,
                mc: Vec::new(),
            };
        }
        let mut el = Elim {
            ctx: self,
            raw,
            vars: BTreeSet::new(),
            disabled,
            cache: BTreeMap::new(),
            memo: BTreeMap::new(),
            mc: Vec::new(),
        };
        el.vars = core::mem::take(&mut vars);
        let mut modified = true;
        let mut size = goal.len();
        let mut idx = 0;
        let mut inconsistent = false;
        loop {
            while idx < size {
                if inconsistent {
                    break;
                }
                let f = goal[idx];
                let nf = el.rewrite(f);
                if nf != f {
                    modified = true;
                    quick_process(el.raw, &mut goal, &mut inconsistent, Some(idx), nf);
                }
                idx += 1;
            }
            if !modified || inconsistent {
                break;
            }
            modified = false;
            size = goal.len();
            el.memo.clear();
            el.disabled = disable_quantified(el.raw, &goal);
            el.vars = collect_occs(el.raw, &goal);
            idx = if el.vars.is_empty() { size } else { 0 };
        }
        ElimResult {
            goal,
            depth: 1,
            mc: el.mc,
        }
    }
}

/// z3's `simplify` tactic on `goal` (rewrite each formula, then
/// `elim_redundancies`), for the fragment where its rewriting is modelled
/// here: Boolean constants and literals, and quantifiers over equalities of
/// atoms, which `th_rewriter` decides by destructive equality resolution and
/// unused-variable elimination. `None` outside that fragment.
pub(super) fn raw_simplify_goal(raw: &mut Raw, goal: &[RId]) -> Option<Vec<RId>> {
    let mut out: Vec<RId> = Vec::new();
    let mut pos: BTreeSet<RId> = BTreeSet::new();
    let mut neg: BTreeSet<RId> = BTreeSet::new();
    for &f in goal {
        let f = simp(raw, f, true)?;
        match raw.op(f) {
            ROp::True => continue,
            ROp::False => return Some(vec![f]),
            _ => {}
        }
        let (atom, positive) = if raw.is_op(f, "not") {
            (raw.args(f)[0], false)
        } else {
            (f, true)
        };
        let (same, other) = if positive {
            (&mut pos, &neg)
        } else {
            (&mut neg, &pos)
        };
        if other.contains(&atom) {
            let ff = raw.mk_false();
            return Some(vec![ff]);
        }
        if same.insert(atom) {
            out.push(f);
        }
    }
    Some(out)
}

/// One formula of [`raw_simplify_goal`]; `top`: not under a quantifier.
fn simp(raw: &mut Raw, t: RId, top: bool) -> Option<RId> {
    let atom = |raw: &Raw, a: RId| {
        matches!(
            raw.op(a),
            ROp::Const(_) | ROp::Fresh(_) | ROp::Var(_) | ROp::True | ROp::False
        )
    };
    match raw.op(t).clone() {
        ROp::Quant(forall, vars) => {
            let body = simp(raw, raw.args(t)[0], false)?;
            Some(reduce_quantifier(raw, forall, vars, body))
        }
        _ if atom(raw, t) => Some(t),
        ROp::Op(n, _) if n == "not" && top && atom(raw, raw.args(t)[0]) => Some(t),
        ROp::Op(n, _) if n == "=" && !top => {
            let (a, b) = (raw.args(t)[0], raw.args(t)[1]);
            if raw.sort(a) == raw.bool_sort || !atom(raw, a) || !atom(raw, b) {
                return None;
            }
            Some(if a == b { raw.mk_true() } else { t })
        }
        _ => None,
    }
}

/// `th_rewriter::reduce_quantifier` on the simplified `body`: merge a nested
/// quantifier of the same kind, drop the unused variables, and apply `der`
/// to an existential equality of a bound variable.
fn reduce_quantifier(
    raw: &mut Raw,
    forall: bool,
    mut vars: Vec<(String, AstId)>,
    body: RId,
) -> RId {
    let mut body = body;
    if let ROp::Quant(f2, inner) = raw.op(body).clone()
        && f2 == forall
    {
        vars.extend(inner);
        body = raw.args(body)[0];
    }
    let free = raw.free[body].clone();
    vars.retain(|(v, _)| free.contains(v));
    if vars.is_empty() {
        return body;
    }
    if !forall && raw.is_op(body, "=") {
        let (a, b) = (raw.args(body)[0], raw.args(body)[1]);
        let bound = |x: RId| matches!(raw.op(x), ROp::Var(v) if vars.iter().any(|(n, _)| n == v));
        if (bound(a) || bound(b)) && a != b {
            return raw.mk_true();
        }
    }
    let b = raw.bool_sort;
    raw.mk(ROp::Quant(forall, vars), vec![body], b)
}

/// The leaf tactics of a `then` / `and-then` chain, in order; `None` for any
/// other combinator or a tactic with parameters.
pub(super) fn tactic_chain(t: &SExpr) -> Option<Vec<String>> {
    match t {
        SExpr::Atom(a) => Some(vec![a.clone()]),
        SExpr::List(l) => {
            let SExpr::Atom(h) = l.first()? else {
                return None;
            };
            if h != "then" && h != "and-then" {
                return None;
            }
            let mut out = Vec::new();
            for s in &l[1..] {
                out.extend(tactic_chain(s)?);
            }
            Some(out)
        }
    }
}

impl Context {
    /// `(apply t)` for a chain of `elim-uncnstr`, `simplify` and `skip` that
    /// runs `elim-uncnstr`: the goals z3 prints, or `None` to take the
    /// general path.
    pub(super) fn apply_elim_uncnstr(&mut self, t: &SExpr) -> Option<String> {
        let leaves = tactic_chain(t)?;
        if !leaves.iter().any(|l| l == "elim-uncnstr")
            || !leaves
                .iter()
                .all(|l| matches!(l.as_str(), "elim-uncnstr" | "simplify" | "skip"))
        {
            return None;
        }
        let bs = self.m.mk_bool_sort();
        let mut raw = Raw::new(bs);
        let mut goal = self.raw_goal(&mut raw)?;
        let fresh = self.uncnstr_fresh;
        let mut depth = 0;
        for leaf in &leaves {
            match leaf.as_str() {
                "elim-uncnstr" => {
                    let r = self.elim_uncnstr(&mut raw, goal);
                    goal = r.goal;
                    depth += r.depth;
                }
                "simplify" => {
                    let Some(g) = raw_simplify_goal(&mut raw, &goal) else {
                        self.uncnstr_fresh = fresh;
                        return None;
                    };
                    goal = g;
                    depth += 1;
                }
                _ => {}
            }
        }
        Some(self.raw_goal_display(&raw, &goal, depth))
    }
}
