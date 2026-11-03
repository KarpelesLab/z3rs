//! z3's regular-expression rewriting for `(simplify …)`.
//!
//! A port of the regex part of `seq_rewriter` (`z3/src/ast/rewriter/
//! seq_rewriter.cpp`): `mk_str_in_regexp`, `mk_re_concat`, `mk_re_union` /
//! `mk_re_inter` with `mk_regex_union_normalize` / `mk_regex_inter_normalize`
//! and `merge_regex_sets`, `mk_re_star`, `mk_re_plus`, `mk_re_opt`,
//! `mk_re_complement`, `mk_re_diff`, `mk_re_loop`, `mk_re_range`; the subset
//! check of `seq_subset.cpp`; the character-class collapse of
//! `seq_range_collapse.cpp`; and the regex `info` (nullable / minimum length)
//! of `seq_decl_plugin.cpp`. Terms live in a hash-consed arena whose node
//! indices play the role of z3's expression ids (creation order), which the
//! union/intersection normal forms sort by. Results print through
//! [`super::smt2_pp`].

use super::len_abs::LenAbs;
use super::smt2_pp::{PpNode, pp_term};
use alloc::collections::BTreeMap;
use alloc::string::{String, ToString};
use alloc::vec;
use alloc::vec::Vec;

/// A node index (z3's expression id: smaller is older).
pub type Id = usize;

/// The sorts the regex simplifier distinguishes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Srt {
    Bool,
    Str,
    Re,
    Int,
}

/// The operators of the fragment.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Op {
    Not,
    Eq,
    And,
    Or,
    Ite,
    InRe,
    ToRe,
    ReNone,
    ReAll,
    ReAllChar,
    Range,
    Concat,
    Union,
    Inter,
    Star,
    Plus,
    Opt,
    Comp,
    Diff,
    /// `(_ re.loop lo hi)`; `hi = None` for `(_ re.loop lo)`.
    Loop(u32, Option<u32>),
    Prefix,
    Suffix,
    StrLen,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Node {
    Var(String, Srt),
    Lit(Vec<u32>),
    Num(i64),
    True,
    False,
    App(Op, Vec<Id>),
}

/// A declaration parameter, as z3's `ast_lt` compares them (a numeral's
/// value, a loop bound, a string literal's characters).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum DeclParam {
    Num(i64),
    Str(Vec<u32>),
}

/// The name of a sort, which z3's `ast_lt` orders sorts by.
fn srt_name(s: Srt) -> &'static str {
    match s {
        Srt::Bool => "Bool",
        Srt::Str => "String",
        Srt::Re => "RegEx",
        Srt::Int => "Int",
    }
}

/// The regex `info` of z3's `seq_util::rex` (the parts the rewriter uses).
#[derive(Clone, Copy, Debug)]
struct Info {
    known: bool,
    interpreted: bool,
    /// `Some(b)`: the empty word is (not) accepted; `None`: unknown.
    nullable: Option<bool>,
    /// The least length of an accepted word (`len.lo()`).
    min_length: u32,
    /// The abstraction of the accepted lengths (bounds, period, residues).
    len: LenAbs,
}

const UNKNOWN_INFO: Info = Info {
    known: false,
    interpreted: false,
    nullable: None,
    min_length: 0,
    len: LenAbs::TOP,
};

/// z3's nullability of a conjunction (`l_true` iff both, `l_false` if
/// either).
fn nullable_and(a: Option<bool>, b: Option<bool>) -> Option<bool> {
    match (a, b) {
        (Some(true), Some(true)) => Some(true),
        (Some(false), _) | (_, Some(false)) => Some(false),
        _ => None,
    }
}

/// z3's nullability of a disjunction (`l_true` if either, `l_false` iff
/// both).
fn nullable_or(a: Option<bool>, b: Option<bool>) -> Option<bool> {
    match (a, b) {
        (Some(true), _) | (_, Some(true)) => Some(true),
        (Some(false), Some(false)) => Some(false),
        _ => None,
    }
}

/// z3's `zstring::max_char()` (unicode encoding).
const MAX_CHAR: u32 = 196607;

/// A sorted, disjoint, non-adjacent set of character ranges (z3's
/// `seq::range_predicate`).
type Ranges = Vec<(u32, u32)>;

fn ranges_union(a: &Ranges, b: &Ranges) -> Ranges {
    let mut all: Vec<(u32, u32)> = a.iter().chain(b).copied().collect();
    all.sort();
    let mut out: Ranges = Vec::new();
    for (lo, hi) in all {
        match out.last_mut() {
            Some(last) if last.1.saturating_add(1) >= lo => last.1 = last.1.max(hi),
            _ => out.push((lo, hi)),
        }
    }
    out
}

fn ranges_inter(a: &Ranges, b: &Ranges) -> Ranges {
    let mut out = Vec::new();
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        let lo = a[i].0.max(b[j].0);
        let hi = a[i].1.min(b[j].1);
        if lo <= hi {
            out.push((lo, hi));
        }
        if a[i].1 < b[j].1 {
            i += 1;
        } else if b[j].1 < a[i].1 {
            j += 1;
        } else {
            i += 1;
            j += 1;
        }
    }
    out
}

fn ranges_complement(a: &Ranges) -> Ranges {
    let mut out = Vec::new();
    let mut cursor: u64 = 0;
    for &(lo, hi) in a {
        if cursor < u64::from(lo) {
            out.push((cursor as u32, lo - 1));
        }
        cursor = u64::from(hi) + 1;
    }
    if cursor <= u64::from(MAX_CHAR) {
        out.push((cursor as u32, MAX_CHAR));
    }
    out
}

fn ranges_diff(a: &Ranges, b: &Ranges) -> Ranges {
    ranges_inter(a, &ranges_complement(b))
}

/// The hash-consed term arena and the rewriter over it.
#[derive(Default)]
pub struct ReSimp {
    nodes: Vec<Node>,
    index: BTreeMap<Node, Id>,
    memo: BTreeMap<Id, Id>,
}

impl ReSimp {
    fn mk_node(&mut self, n: Node) -> Id {
        if let Some(&id) = self.index.get(&n) {
            return id;
        }
        let id = self.nodes.len();
        self.nodes.push(n.clone());
        self.index.insert(n, id);
        id
    }

    /// A declared constant `name` of sort `srt`.
    pub fn var(&mut self, name: &str, srt: Srt) -> Id {
        self.mk_node(Node::Var(name.to_string(), srt))
    }

    /// A string literal.
    pub fn lit(&mut self, cps: &[u32]) -> Id {
        self.mk_node(Node::Lit(cps.to_vec()))
    }

    /// An integer numeral.
    pub fn num(&mut self, n: i64) -> Id {
        self.mk_node(Node::Num(n))
    }

    /// `true` / `false`.
    pub fn boolean(&mut self, b: bool) -> Id {
        self.mk_node(if b { Node::True } else { Node::False })
    }

    /// The (unsimplified) application `op(args)`, as the parser builds it:
    /// the n-ary regex operators associate to the left, as z3's declarations do.
    pub fn app(&mut self, op: Op, args: &[Id]) -> Id {
        if matches!(op, Op::Concat | Op::Union | Op::Inter | Op::Diff) && args.len() > 2 {
            let mut acc = self.raw(op.clone(), &args[..2]);
            for &a in &args[2..] {
                acc = self.raw(op.clone(), &[acc, a]);
            }
            return acc;
        }
        self.raw(op, args)
    }

    fn raw(&mut self, op: Op, args: &[Id]) -> Id {
        self.mk_node(Node::App(op, args.to_vec()))
    }

    // ----- inspection -------------------------------------------------------

    fn op_of(&self, t: Id) -> Option<(&Op, &[Id])> {
        match &self.nodes[t] {
            Node::App(op, args) => Some((op, args)),
            _ => None,
        }
    }

    fn is_op(&self, t: Id, o: &Op) -> bool {
        matches!(&self.nodes[t], Node::App(op, _) if op == o)
    }

    fn arg(&self, t: Id, i: usize) -> Id {
        match &self.nodes[t] {
            Node::App(_, args) => args[i],
            _ => unreachable!(),
        }
    }

    fn un(&self, t: Id, o: &Op) -> Option<Id> {
        match &self.nodes[t] {
            Node::App(op, args) if op == o && args.len() == 1 => Some(args[0]),
            _ => None,
        }
    }

    fn bin(&self, t: Id, o: &Op) -> Option<(Id, Id)> {
        match &self.nodes[t] {
            Node::App(op, args) if op == o && args.len() == 2 => Some((args[0], args[1])),
            _ => None,
        }
    }

    fn str_lit(&self, t: Id) -> Option<&[u32]> {
        match &self.nodes[t] {
            Node::Lit(l) => Some(l),
            _ => None,
        }
    }

    fn is_empty(&self, t: Id) -> bool {
        self.is_op(t, &Op::ReNone)
    }

    fn is_full_char(&self, t: Id) -> bool {
        self.is_op(t, &Op::ReAllChar)
    }

    fn is_full_seq(&self, t: Id) -> bool {
        self.is_op(t, &Op::ReAll) || self.un(t, &Op::Star).is_some_and(|s| self.is_full_char(s))
    }

    fn is_epsilon(&self, t: Id) -> bool {
        self.un(t, &Op::ToRe)
            .is_some_and(|s| self.str_lit(s).is_some_and(<[u32]>::is_empty))
    }

    fn is_dot_plus(&self, t: Id) -> bool {
        if self.un(t, &Op::Plus).is_some_and(|s| self.is_full_char(s)) {
            return true;
        }
        if let Some((s, u)) = self.bin(t, &Op::Concat) {
            return (self.is_full_char(s) && self.is_full_seq(u))
                || (self.is_full_char(u) && self.is_full_seq(s));
        }
        false
    }

    /// A range with single-character literal bounds.
    fn char_range(&self, t: Id) -> Option<(u32, u32)> {
        let (lo, hi) = self.bin(t, &Op::Range)?;
        match (self.str_lit(lo), self.str_lit(hi)) {
            (Some([a]), Some([b])) => Some((*a, *b)),
            _ => None,
        }
    }

    fn loop_of(&self, t: Id) -> Option<(Id, u32, Option<u32>)> {
        match &self.nodes[t] {
            Node::App(Op::Loop(lo, hi), args) if args.len() == 1 => Some((args[0], *lo, *hi)),
            _ => None,
        }
    }

    /// z3's `rex::mk_info_rec` with the `info` operations of
    /// `seq_decl_plugin.cpp`: nullability, interpretation and the length
    /// abstraction of `t`.
    fn info(&self, t: Id) -> Info {
        let known = |interpreted, nullable, len: LenAbs| Info {
            known: true,
            interpreted,
            nullable,
            min_length: len.lo(),
            len,
        };
        let Some((op, args)) = self.op_of(t) else {
            return UNKNOWN_INFO;
        };
        match op {
            Op::ReNone => known(true, Some(false), LenAbs::bounds(u32::MAX, 0)),
            Op::ReAll => known(true, Some(true), LenAbs::bounds(0, u32::MAX)),
            Op::Star => {
                let i = self.info(args[0]);
                known(i.interpreted, Some(true), i.len.star())
            }
            Op::Opt => {
                let i = self.info(args[0]);
                known(i.interpreted, Some(true), i.len.opt())
            }
            Op::Range => known(
                self.char_range(t).is_some(),
                Some(false),
                LenAbs::bounds(1, 1),
            ),
            Op::ReAllChar => known(true, Some(false), LenAbs::bounds(1, 1)),
            Op::Concat => {
                let (a, b) = (self.info(args[0]), self.info(args[1]));
                if !a.known {
                    return a;
                }
                if !b.known {
                    return b;
                }
                let nullable = if a.nullable == Some(false) || b.nullable == Some(false) {
                    Some(false)
                } else if a.nullable == Some(true) && b.nullable == Some(true) {
                    Some(true)
                } else {
                    None
                };
                known(
                    a.interpreted && b.interpreted,
                    nullable,
                    a.len.concat(&b.len),
                )
            }
            Op::Union => {
                let (a, b) = (self.info(args[0]), self.info(args[1]));
                if !a.known && !b.known {
                    return b;
                }
                known(
                    a.interpreted && b.interpreted,
                    nullable_or(a.nullable, b.nullable),
                    a.len.unite(&b.len),
                )
            }
            Op::Inter => {
                let (a, b) = (self.info(args[0]), self.info(args[1]));
                if !a.known {
                    return a;
                }
                if !b.known {
                    return b;
                }
                known(
                    a.interpreted && b.interpreted,
                    nullable_and(a.nullable, b.nullable),
                    a.len.meet(&b.len),
                )
            }
            Op::ToRe => {
                let s = args[0];
                match self.str_lit(s) {
                    Some(l) => {
                        let n = l.len() as u32;
                        known(true, Some(l.is_empty()), LenAbs::bounds(n, n))
                    }
                    None => known(false, None, LenAbs::bounds(0, u32::MAX)),
                }
            }
            Op::Plus => {
                let a = self.info(args[0]);
                if !a.known {
                    return a;
                }
                known(a.interpreted, a.nullable, a.len.plus())
            }
            Op::Comp => {
                let a = self.info(args[0]);
                if !a.known {
                    return a;
                }
                // The complement's lengths are not determined by the
                // argument's: top.
                let n = a.nullable.map(|b| !b);
                let lo = if n == Some(false) { 1 } else { 0 };
                known(a.interpreted, n, LenAbs::bounds(lo, u32::MAX))
            }
            Op::Loop(lo, hi) => {
                let a = self.info(args[0]);
                if !a.known {
                    return a;
                }
                let nullable = if *lo == 0 { Some(true) } else { a.nullable };
                let len = a.len.repeat_range(*lo, hi.unwrap_or(u32::MAX));
                known(a.interpreted, nullable, len)
            }
            Op::Diff => {
                let (a, b) = (self.info(args[0]), self.info(args[1]));
                if !a.known {
                    return a;
                }
                if !b.known {
                    return b;
                }
                let nullable = if a.nullable == Some(false) {
                    Some(false)
                } else if a.nullable == Some(true) && b.nullable == Some(false) {
                    Some(true)
                } else {
                    None
                };
                known(a.interpreted && b.interpreted, nullable, a.len)
            }
            Op::Ite => {
                // `orelse`: one of the two branches.
                let (a, b) = (self.info(args[1]), self.info(args[2]));
                if !a.known {
                    return a;
                }
                if !b.known {
                    return b;
                }
                let nullable = match (a.nullable, b.nullable) {
                    (Some(true), Some(true)) => Some(true),
                    (Some(false), Some(false)) => Some(false),
                    _ => None,
                };
                known(false, nullable, a.len.unite(&b.len))
            }
            _ => UNKNOWN_INFO,
        }
    }

    /// z3's `seq_util::can_be_member`: can a word of `a`'s length shape be in
    /// `r`, by the residues of `r`'s length abstraction?
    fn can_be_member(&self, a: Id, r: Id) -> bool {
        let info = self.info(r);
        if !info.known || info.len.period() <= 1 {
            return true;
        }
        // `str::length_shape`: a literal is its length, anything else is a
        // term of unknown length.
        let (cst, g) = match self.str_lit(a) {
            Some(l) => (l.len() as u32, 0),
            None => (0, 1),
        };
        info.len.residue_reachable(cst, g)
    }

    /// No variables below `t`.
    fn is_ground(&self, t: Id) -> bool {
        match &self.nodes[t] {
            Node::Var(..) => false,
            Node::App(_, args) => args.iter().all(|&a| self.is_ground(a)),
            _ => true,
        }
    }

    // ----- the rewriter -------------------------------------------------------

    /// Simplify `t` bottom-up, as z3's `th_rewriter`.
    pub fn simplify(&mut self, t: Id) -> Id {
        if let Some(&r) = self.memo.get(&t) {
            return r;
        }
        let r = match self.nodes[t].clone() {
            Node::App(op, args) => {
                let args: Vec<Id> = args.iter().map(|&a| self.simplify(a)).collect();
                self.mk(op, &args)
            }
            _ => t,
        };
        self.memo.insert(t, r);
        r
    }

    /// The rewriting constructor of `op(args)` (z3's `mk_app_core` dispatch,
    /// falling back to the plain application).
    fn mk(&mut self, op: Op, args: &[Id]) -> Id {
        match op {
            Op::Not => self.mk_not(args[0]),
            Op::Eq => self.mk_eq(args[0], args[1]),
            Op::And => self.mk_and(args),
            Op::Or => self.mk_or(args),
            Op::Ite => self.mk_ite(args[0], args[1], args[2]),
            Op::InRe => self.mk_in_re(args[0], args[1]),
            Op::Concat => self.mk_re_append(args[0], args[1]),
            Op::Union => self.mk_union(args[0], args[1]),
            Op::Inter => self.mk_inter(args[0], args[1]),
            Op::Star => self.mk_star(args[0]),
            Op::Plus => self.mk_plus(args[0]),
            Op::Opt => self.mk_opt(args[0]),
            Op::Comp => self.mk_complement(args[0]),
            Op::Diff => self.mk_diff(args[0], args[1]),
            Op::Loop(lo, hi) => self.mk_loop(args[0], lo, hi),
            Op::Range => self.mk_range(args[0], args[1]),
            op => self.raw(op, args),
        }
    }

    // Boolean layer (z3's `bool_rewriter`, the cases the fragment meets).

    fn mk_not(&mut self, a: Id) -> Id {
        match &self.nodes[a] {
            Node::True => self.boolean(false),
            Node::False => self.boolean(true),
            Node::App(Op::Not, args) => args[0],
            _ => self.raw(Op::Not, &[a]),
        }
    }

    fn mk_eq(&mut self, a: Id, b: Id) -> Id {
        if a == b {
            return self.boolean(true);
        }
        match (&self.nodes[a], &self.nodes[b]) {
            (Node::Lit(x), Node::Lit(y)) => return self.boolean(x == y),
            // `reduce_eq` re-forms `x = ""` as `"" = x`.
            (Node::Var(..), Node::Lit(y)) if y.is_empty() => return self.raw(Op::Eq, &[b, a]),
            (Node::Num(x), Node::Num(y)) => return self.boolean(x == y),
            (Node::True, _) => return b,
            (_, Node::True) => return a,
            (Node::False, _) => return self.mk_not(b),
            (_, Node::False) => return self.mk_not(a),
            _ => {}
        }
        if self.is_re(a) {
            return self.reduce_re_eq(a, b);
        }
        self.raw(Op::Eq, &[a, b])
    }

    /// The sort of `t`.
    fn sort_of(&self, t: Id) -> Srt {
        match &self.nodes[t] {
            Node::Var(_, srt) => *srt,
            Node::Lit(_) => Srt::Str,
            Node::Num(_) => Srt::Int,
            Node::True | Node::False => Srt::Bool,
            Node::App(op, args) => match op {
                Op::Not | Op::Eq | Op::And | Op::Or | Op::InRe | Op::Prefix | Op::Suffix => {
                    Srt::Bool
                }
                Op::StrLen => Srt::Int,
                Op::Ite => self.sort_of(args[1]),
                _ => Srt::Re,
            },
        }
    }

    /// The depth of `t` (z3's `get_depth`: 1 for a constant).
    fn depth(&self, t: Id) -> u32 {
        match &self.nodes[t] {
            Node::App(_, args) => 1 + args.iter().map(|&a| self.depth(a)).max().unwrap_or(0),
            _ => 1,
        }
    }

    /// The declaration of `t` as z3's `ast_lt` compares it: its name, its
    /// parameters, its domain and its range.
    fn decl_key(&self, t: Id) -> (&str, Vec<DeclParam>, Vec<Srt>, Srt) {
        let range = self.sort_of(t);
        match &self.nodes[t] {
            Node::Var(n, _) => (n.as_str(), Vec::new(), Vec::new(), range),
            Node::Lit(l) => ("String", vec![DeclParam::Str(l.clone())], Vec::new(), range),
            Node::Num(n) => (
                "Int",
                vec![DeclParam::Num(*n), DeclParam::Num(1)],
                Vec::new(),
                range,
            ),
            Node::True => ("true", Vec::new(), Vec::new(), range),
            Node::False => ("false", Vec::new(), Vec::new(), range),
            Node::App(op, args) => {
                let name = match op {
                    Op::Not => "not",
                    Op::Eq => "=",
                    Op::And => "and",
                    Op::Or => "or",
                    Op::Ite => "if",
                    Op::InRe => "str.in_re",
                    Op::ToRe => "str.to_re",
                    Op::ReNone => "re.empty",
                    Op::ReAll => "re.all",
                    Op::ReAllChar => "re.allchar",
                    Op::Range => "re.range",
                    Op::Concat => "re.++",
                    Op::Union => "re.union",
                    Op::Inter => "re.inter",
                    Op::Star => "re.*",
                    Op::Plus => "re.+",
                    Op::Opt => "re.opt",
                    Op::Comp => "re.comp",
                    Op::Diff => "re.diff",
                    Op::Loop(..) => "re.loop",
                    Op::Prefix => "str.prefixof",
                    Op::Suffix => "str.suffixof",
                    Op::StrLen => "str.len",
                };
                let params = match op {
                    Op::Loop(lo, hi) => core::iter::once(*lo)
                        .chain(*hi)
                        .map(|k| DeclParam::Num(i64::from(k)))
                        .collect(),
                    _ => Vec::new(),
                };
                let domain = args.iter().map(|&a| self.sort_of(a)).collect();
                (name, params, domain, range)
            }
        }
    }

    /// z3's `ast_lt`: a total order on terms independent of their ids
    /// (argument count, depth, declaration, then the arguments in turn).
    fn ast_lt(&self, mut a: Id, mut b: Id) -> bool {
        loop {
            if a == b {
                return false;
            }
            let (na, nb) = (self.arity(a), self.arity(b));
            if na != nb {
                return na < nb;
            }
            let (da, db) = (self.depth(a), self.depth(b));
            if da != db {
                return da < db;
            }
            let (ka, kb) = (self.decl_key(a), self.decl_key(b));
            if ka.0 != kb.0 {
                return ka.0.as_bytes() < kb.0.as_bytes();
            }
            if ka.1.len() != kb.1.len() {
                return ka.1.len() < kb.1.len();
            }
            if let Some((x, y)) = ka.1.iter().zip(&kb.1).find(|(x, y)| x != y) {
                return x < y;
            }
            if let Some((x, y)) = ka.2.iter().zip(&kb.2).find(|(x, y)| x != y) {
                return srt_name(*x) < srt_name(*y);
            }
            if ka.3 != kb.3 {
                return srt_name(ka.3) < srt_name(kb.3);
            }
            let (xs, ys) = match (&self.nodes[a], &self.nodes[b]) {
                (Node::App(_, xs), Node::App(_, ys)) => (xs, ys),
                _ => return false,
            };
            match xs.iter().zip(ys).find(|(x, y)| x != y) {
                Some((&x, &y)) => (a, b) = (x, y),
                None => return false,
            }
        }
    }

    /// The number of arguments of `t`.
    fn arity(&self, t: Id) -> usize {
        match &self.nodes[t] {
            Node::App(_, args) => args.len(),
            _ => 0,
        }
    }

    /// Is `t` a regular expression?
    fn is_re(&self, t: Id) -> bool {
        match &self.nodes[t] {
            Node::Var(_, srt) => *srt == Srt::Re,
            Node::App(op, args) => match op {
                Op::ToRe
                | Op::ReNone
                | Op::ReAll
                | Op::ReAllChar
                | Op::Range
                | Op::Concat
                | Op::Union
                | Op::Inter
                | Op::Star
                | Op::Plus
                | Op::Opt
                | Op::Comp
                | Op::Diff
                | Op::Loop(..) => true,
                Op::Ite => self.is_re(args[1]),
                _ => false,
            },
            _ => false,
        }
    }

    /// z3's `seq_rewriter::reduce_re_eq`.
    fn reduce_re_eq(&mut self, a: Id, b: Id) -> Id {
        let (mut l, mut r) = (a, b);
        if self.is_empty(l) {
            core::mem::swap(&mut l, &mut r);
        }
        if self.is_empty(r) {
            return self
                .reduce_re_is_empty(l)
                .unwrap_or_else(|| self.raw(Op::Eq, &[a, b]));
        }
        if l == r {
            return self.boolean(true);
        }
        if self.is_ground(l)
            && self.is_ground(r)
            && let Some(b) = self.equivalent(l, r)
        {
            return self.boolean(b);
        }
        self.raw(Op::Eq, &[l, r])
    }

    /// `r = re.none`, rewritten.
    fn eq_empty(&mut self, r: Id) -> Id {
        let none = self.raw(Op::ReNone, &[]);
        self.mk_eq(r, none)
    }

    /// z3's `seq_rewriter::reduce_re_is_empty`.
    fn reduce_re_is_empty(&mut self, r: Id) -> Option<Id> {
        if let Some((r1, r2)) = self.bin(r, &Op::Union) {
            let x = self.eq_empty(r1);
            let y = self.eq_empty(r2);
            return Some(self.mk_and(&[x, y]));
        }
        if self.un(r, &Op::Star).is_some()
            || self.un(r, &Op::ToRe).is_some()
            || self.is_full_char(r)
            || self.is_full_seq(r)
        {
            return Some(self.boolean(false));
        }
        if let Some((r1, r2)) = self.bin(r, &Op::Concat) {
            let x = self.eq_empty(r1);
            let y = self.eq_empty(r2);
            return Some(self.mk_or(&[x, y]));
        }
        if let Some((lo, hi)) = self.bin(r, &Op::Range) {
            match (self.str_lit(lo), self.str_lit(hi)) {
                (Some([a]), Some([b])) => {
                    let e = a > b;
                    return Some(self.boolean(e));
                }
                (Some(l), _) if l.len() != 1 => return Some(self.boolean(true)),
                (_, Some(h)) if h.len() != 1 => return Some(self.boolean(true)),
                _ => {}
            }
        }
        if let Some((r1, lo, hi)) = self.loop_of(r) {
            if lo == 0 {
                return Some(self.boolean(false));
            }
            if hi.is_none_or(|h| lo <= h) {
                return Some(self.eq_empty(r1));
            }
        }
        if let Some((r1, r2)) = self.bin(r, &Op::Inter) {
            let split = if let Some((r3, r4)) = self.bin(r1, &Op::Union) {
                Some((r3, r4, r2))
            } else {
                self.bin(r2, &Op::Union).map(|(r3, r4)| (r3, r4, r1))
            };
            if let Some((r3, r4, other)) = split {
                let a1 = self.mk_inter(r3, other);
                let b1 = self.mk_inter(r4, other);
                let u = self.mk_union(a1, b1);
                return Some(self.eq_empty(u));
            }
        }
        None
    }

    /// Language equivalence of the ground regexes `l` and `r` (z3's
    /// `regex_bisim`): a breadth-first walk over pairs of derivatives by one
    /// representative character per alphabet class, comparing nullability.
    /// `None` when the walk exceeds its budget.
    fn equivalent(&mut self, l: Id, r: Id) -> Option<bool> {
        const MAX_STATES: usize = 2000;
        let mut points: Vec<u32> = vec![0];
        let mut stack = vec![l, r];
        let mut seen: alloc::collections::BTreeSet<Id> = alloc::collections::BTreeSet::new();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match &self.nodes[t] {
                Node::Lit(cs) => {
                    for &c in cs {
                        points.push(c);
                        points.push(c.saturating_add(1));
                    }
                }
                Node::App(_, args) => stack.extend(args.iter().copied()),
                _ => {}
            }
        }
        points.retain(|&p| p <= MAX_CHAR);
        points.sort_unstable();
        points.dedup();
        let mut visited: alloc::collections::BTreeSet<(Id, Id)> =
            alloc::collections::BTreeSet::new();
        let mut todo = alloc::collections::VecDeque::new();
        todo.push_back((l, r));
        let mut deriv_memo: BTreeMap<(Id, u32), Id> = BTreeMap::new();
        while let Some((a, b)) = todo.pop_front() {
            if !visited.insert((a, b)) {
                continue;
            }
            if visited.len() > MAX_STATES {
                return None;
            }
            if self.ground_member(&[], a)? != self.ground_member(&[], b)? {
                return Some(false);
            }
            for &c in &points {
                let da = self.derivative(a, c, &mut deriv_memo)?;
                let db = self.derivative(b, c, &mut deriv_memo)?;
                if da != db {
                    todo.push_back((da, db));
                }
            }
        }
        Some(true)
    }

    /// The Brzozowski derivative of the ground regex `t` by the character `c`,
    /// normalised through the rewriting constructors.
    fn derivative(&mut self, t: Id, c: u32, memo: &mut BTreeMap<(Id, u32), Id>) -> Option<Id> {
        if let Some(&d) = memo.get(&(t, c)) {
            return Some(d);
        }
        let none = self.raw(Op::ReNone, &[]);
        let eps = {
            let e = self.lit(&[]);
            self.raw(Op::ToRe, &[e])
        };
        let (op, args) = match &self.nodes[t] {
            Node::App(op, args) => (op.clone(), args.clone()),
            _ => return None,
        };
        let d = match op {
            Op::ReNone => none,
            Op::ReAll => t,
            Op::ReAllChar => eps,
            Op::Range => match self.char_range(t) {
                Some((lo, hi)) if lo <= c && c <= hi => eps,
                _ => none,
            },
            Op::ToRe => {
                let l = self.str_lit(args[0])?.to_vec();
                if l.first() == Some(&c) {
                    let rest = self.lit(&l[1..]);
                    self.raw(Op::ToRe, &[rest])
                } else {
                    none
                }
            }
            Op::Concat => {
                let da = self.derivative(args[0], c, memo)?;
                let left = self.mk_re_append(da, args[1]);
                if self.ground_member(&[], args[0])? {
                    let db = self.derivative(args[1], c, memo)?;
                    self.mk_union(left, db)
                } else {
                    left
                }
            }
            Op::Union | Op::Inter | Op::Diff => {
                let da = self.derivative(args[0], c, memo)?;
                let db = self.derivative(args[1], c, memo)?;
                match op {
                    Op::Union => self.mk_union(da, db),
                    Op::Inter => self.mk_inter(da, db),
                    _ => self.mk_diff(da, db),
                }
            }
            Op::Comp => {
                let da = self.derivative(args[0], c, memo)?;
                self.mk_complement(da)
            }
            Op::Star | Op::Plus => {
                let da = self.derivative(args[0], c, memo)?;
                let st = self.mk_star(args[0]);
                self.mk_re_append(da, st)
            }
            Op::Opt => self.derivative(args[0], c, memo)?,
            Op::Loop(lo, hi) => {
                if hi == Some(0) {
                    none
                } else {
                    let da = self.derivative(args[0], c, memo)?;
                    let rest = self.mk_loop(args[0], lo.saturating_sub(1), hi.map(|h| h - 1));
                    self.mk_re_append(da, rest)
                }
            }
            _ => return None,
        };
        memo.insert((t, c), d);
        Some(d)
    }

    /// Are `a` and `b` complementary literals (`p` and `(not p)`)?
    fn complementary(&self, a: Id, b: Id) -> bool {
        self.un(a, &Op::Not) == Some(b) || self.un(b, &Op::Not) == Some(a)
    }

    fn mk_and(&mut self, args: &[Id]) -> Id {
        let mut out: Vec<Id> = Vec::new();
        for &a in args {
            match &self.nodes[a] {
                Node::False => return a,
                Node::True => {}
                Node::App(Op::And, xs) => {
                    for &x in xs.clone().iter() {
                        if !out.contains(&x) {
                            out.push(x);
                        }
                    }
                }
                _ => {
                    if !out.contains(&a) {
                        out.push(a);
                    }
                }
            }
        }
        if out
            .iter()
            .any(|&x| out.iter().any(|&y| self.complementary(x, y)))
        {
            return self.boolean(false);
        }
        match out.len() {
            0 => self.boolean(true),
            1 => out[0],
            _ => self.raw(Op::And, &out),
        }
    }

    /// z3's `bool_rewriter::mk_or`: nested disjunctions flattened, `false`
    /// and repeated disjuncts dropped, `p ∨ ¬p` is `true`. When a disjunct was
    /// dropped or two are out of [`Self::ast_lt`] order, the disjuncts are
    /// sorted by id (`sort_disjunctions`, with `ast_lt` comparing ids).
    fn mk_or(&mut self, args: &[Id]) -> Id {
        let mut out: Vec<Id> = Vec::new();
        let mut changed = false;
        for &a in args {
            match &self.nodes[a] {
                Node::True => return a,
                Node::False => changed = true,
                Node::App(Op::Or, xs) => {
                    changed = true;
                    for &x in xs.clone().iter() {
                        if !out.contains(&x) {
                            out.push(x);
                        }
                    }
                }
                _ => {
                    if out.contains(&a) {
                        changed = true;
                    } else {
                        out.push(a);
                    }
                }
            }
        }
        if out
            .iter()
            .any(|&x| out.iter().any(|&y| self.complementary(x, y)))
        {
            return self.boolean(true);
        }
        if changed || out.windows(2).any(|w| self.ast_lt(w[1], w[0])) {
            out.sort();
        }
        match out.len() {
            0 => self.boolean(false),
            1 => out[0],
            _ => self.raw(Op::Or, &out),
        }
    }

    fn mk_ite(&mut self, c: Id, t: Id, e: Id) -> Id {
        match (&self.nodes[c], &self.nodes[t], &self.nodes[e]) {
            (Node::True, _, _) => t,
            (Node::False, _, _) => e,
            _ if t == e => t,
            (_, Node::True, _) => self.mk_or(&[c, e]),
            (_, _, Node::False) => self.mk_and(&[c, t]),
            (_, Node::False, _) => {
                let nc = self.mk_not(c);
                self.mk_and(&[nc, e])
            }
            (_, _, Node::True) => {
                let nc = self.mk_not(c);
                self.mk_or(&[nc, t])
            }
            _ => self.raw(Op::Ite, &[c, t, e]),
        }
    }

    /// `(str.len s)`, folded on a literal.
    fn mk_len(&mut self, s: Id) -> Id {
        if let Some(l) = self.str_lit(s) {
            let n = l.len() as i64;
            return self.num(n);
        }
        self.raw(Op::StrLen, &[s])
    }

    /// z3's `seq_rewriter::mk_str_in_regexp`.
    fn mk_in_re(&mut self, a: Id, b: Id) -> Id {
        if self.is_empty(b) {
            return self.boolean(false);
        }
        if self.is_full_seq(b) {
            return self.boolean(true);
        }
        if let Some(s) = self.str_lit(a).map(<[u32]>::to_vec)
            && self.is_ground(b)
            && let Some(m) = self.ground_member(&s, b)
        {
            return self.boolean(m);
        }
        // lift_str_from_to_re
        if let Some(s) = self.un(b, &Op::ToRe) {
            return self.mk_eq(a, s);
        }
        if let Some((c, d)) = self.bin(b, &Op::Concat) {
            if let Some(e) = self.un(c, &Op::ToRe)
                && self.is_full_seq(d)
            {
                return self.raw(Op::Prefix, &[e, a]);
            }
            if let Some(e) = self.un(d, &Op::ToRe)
                && self.is_full_seq(c)
            {
                return self.raw(Op::Suffix, &[e, a]);
            }
        }
        let b1 = if let Some(b1) = self.un(b, &Op::Opt) {
            Some(b1)
        } else if let Some((x, y)) = self.bin(b, &Op::Union) {
            if self.is_epsilon(y) {
                Some(x)
            } else if self.is_epsilon(x) {
                Some(y)
            } else {
                None
            }
        } else {
            None
        };
        if let Some(b1) = b1 {
            let len_a = self.mk_len(a);
            let zero = self.num(0);
            let is_empty = self.mk_eq(len_a, zero);
            let in_b1 = self.raw(Op::InRe, &[a, b1]);
            let in_b1 = self.simplify(in_b1);
            let t = self.boolean(true);
            return self.mk_ite(is_empty, t, in_b1);
        }
        if !self.can_be_member(a, b) {
            return self.boolean(false);
        }
        self.raw(Op::InRe, &[a, b])
    }

    /// Membership of the literal `s` in the ground regex `r`: the set of
    /// spans `s[i..j]` each subterm matches.
    fn ground_member(&self, s: &[u32], r: Id) -> Option<bool> {
        let mut memo: BTreeMap<Id, Vec<Vec<bool>>> = BTreeMap::new();
        let m = self.spans(s, r, &mut memo)?;
        Some(m[0][s.len()])
    }

    fn spans(
        &self,
        s: &[u32],
        r: Id,
        memo: &mut BTreeMap<Id, Vec<Vec<bool>>>,
    ) -> Option<Vec<Vec<bool>>> {
        if let Some(m) = memo.get(&r) {
            return Some(m.clone());
        }
        let n = s.len();
        let mut m = vec![vec![false; n + 1]; n + 1];
        let (op, args) = self.op_of(r)?;
        let args = args.to_vec();
        match op {
            Op::ReNone => {}
            Op::ReAll => {
                for (i, row) in m.iter_mut().enumerate() {
                    row[i..].fill(true);
                }
            }
            Op::ReAllChar => {
                for i in 0..n {
                    m[i][i + 1] = true;
                }
            }
            Op::Range => {
                if let Some((lo, hi)) = self.char_range(r) {
                    for i in 0..n {
                        m[i][i + 1] = lo <= s[i] && s[i] <= hi;
                    }
                } else {
                    // A range whose bounds are not single characters is empty.
                    let bounds_lit =
                        self.str_lit(args[0]).is_some() && self.str_lit(args[1]).is_some();
                    if !bounds_lit {
                        return None;
                    }
                }
            }
            Op::ToRe => {
                let l = self.str_lit(args[0])?.to_vec();
                for i in 0..=n {
                    if i + l.len() <= n && s[i..i + l.len()] == l[..] {
                        m[i][i + l.len()] = true;
                    }
                }
            }
            Op::Concat => {
                let a = self.spans(s, args[0], memo)?;
                let b = self.spans(s, args[1], memo)?;
                m = compose(&a, &b);
            }
            Op::Union | Op::Inter | Op::Diff => {
                let a = self.spans(s, args[0], memo)?;
                let b = self.spans(s, args[1], memo)?;
                for i in 0..=n {
                    for j in i..=n {
                        m[i][j] = match op {
                            Op::Union => a[i][j] || b[i][j],
                            Op::Inter => a[i][j] && b[i][j],
                            _ => a[i][j] && !b[i][j],
                        };
                    }
                }
            }
            Op::Comp => {
                let a = self.spans(s, args[0], memo)?;
                for i in 0..=n {
                    for j in i..=n {
                        m[i][j] = !a[i][j];
                    }
                }
            }
            Op::Star | Op::Plus | Op::Opt | Op::Loop(..) => {
                let a = self.spans(s, args[0], memo)?;
                let mut id = vec![vec![false; n + 1]; n + 1];
                for (i, row) in id.iter_mut().enumerate() {
                    row[i] = true;
                }
                let (lo, hi) = match op {
                    Op::Star => (0, None),
                    Op::Plus => (1, None),
                    Op::Opt => (0, Some(1)),
                    Op::Loop(lo, hi) => (*lo, *hi),
                    _ => unreachable!(),
                };
                if hi.is_some_and(|h| h < lo) {
                    return Some(m);
                }
                // power[k] = a^k; accumulate k in [lo, hi] (hi = ∞ saturates
                // after n + 1 extra steps since spans are bounded by n).
                let mut pw = id;
                let cap = hi.map_or(lo as usize + n + 1, |h| h as usize);
                for k in 0..=cap {
                    if k >= lo as usize {
                        for i in 0..=n {
                            for j in i..=n {
                                m[i][j] |= pw[i][j];
                            }
                        }
                    }
                    if k < cap {
                        pw = compose(&pw, &a);
                    }
                }
            }
            _ => return None,
        }
        memo.insert(r, m.clone());
        Some(m)
    }

    /// z3's `mk_re_append` (`mk_re_concat`, else the plain concatenation).
    fn mk_re_append(&mut self, a: Id, b: Id) -> Id {
        self.mk_re_concat(a, b)
            .unwrap_or_else(|| self.raw(Op::Concat, &[a, b]))
    }

    fn accepts_empty_word(&self, r: Id) -> bool {
        let i = self.info(r);
        i.interpreted && i.nullable == Some(true) && i.min_length == 0
    }

    fn starts_with_full_seq(&self, r: Id) -> bool {
        self.is_full_seq(r)
            || self
                .bin(r, &Op::Concat)
                .is_some_and(|(r1, _)| self.is_full_seq(r1))
    }

    fn ends_with_full_seq(&self, mut r: Id) -> bool {
        while let Some((_, r2)) = self.bin(r, &Op::Concat) {
            r = r2;
        }
        self.is_full_seq(r)
    }

    fn all_inter_arms_end_with_full_seq(&self, r: Id) -> bool {
        let mut todo = vec![r];
        while let Some(t) = todo.pop() {
            if let Some((r1, r2)) = self.bin(t, &Op::Inter) {
                todo.push(r1);
                todo.push(r2);
            } else if !self.ends_with_full_seq(t) {
                return false;
            }
        }
        true
    }

    /// z3's `seq_rewriter::mk_re_concat`.
    fn mk_re_concat(&mut self, a: Id, b: Id) -> Option<Id> {
        if self.is_full_seq(a) && self.is_full_seq(b) {
            return Some(a);
        }
        if self.is_full_seq(a) && self.accepts_empty_word(b) {
            return Some(a);
        }
        if self.is_full_seq(b) && self.accepts_empty_word(a) {
            return Some(b);
        }
        if self.is_full_seq(b) && self.ends_with_full_seq(a) {
            return Some(a);
        }
        if self.is_full_seq(a) && self.starts_with_full_seq(b) {
            return Some(b);
        }
        if self.is_full_seq(a)
            && let Some((u1, u2)) = self.bin(b, &Op::Union)
            && (self.starts_with_full_seq(u1) || self.starts_with_full_seq(u2))
        {
            let x = self.mk_re_append(a, u1);
            let y = self.mk_re_append(a, u2);
            let u = self.union_normalize(x, y);
            return Some(self.simplify(u));
        }
        if self.bin(a, &Op::Inter).is_some()
            && self.is_full_seq(b)
            && self.all_inter_arms_end_with_full_seq(a)
        {
            return Some(a);
        }
        if self.is_empty(a) {
            return Some(a);
        }
        if self.is_empty(b) {
            return Some(b);
        }
        if self.is_epsilon(a) {
            return Some(b);
        }
        if self.is_epsilon(b) {
            return Some(a);
        }
        if self.is_full_char(a) && self.is_full_seq(b) {
            return Some(self.mk_plus(a));
        }
        if self.is_full_char(b) && self.is_full_seq(a) {
            return Some(self.mk_plus(b));
        }
        if let (Some(x), Some(y)) = (self.un(a, &Op::ToRe), self.un(b, &Op::ToRe))
            && let (Some(sx), Some(sy)) = (self.str_lit(x), self.str_lit(y))
        {
            let mut cat = sx.to_vec();
            cat.extend_from_slice(sy);
            let l = self.lit(&cat);
            return Some(self.raw(Op::ToRe, &[l]));
        }
        if let (Some(a1), Some(b1)) = (self.un(a, &Op::Star), self.un(b, &Op::Star))
            && a1 == b1
        {
            return Some(a);
        }
        if let Some(a1) = self.un(a, &Op::Star)
            && let Some((b1, _)) = self.bin(b, &Op::Concat)
            && self.un(b1, &Op::Star) == Some(a1)
        {
            return Some(b);
        }
        if self.un(a, &Op::Star) == Some(b) {
            return Some(self.mk_re_append(b, a));
        }
        if let (Some((a1, lo1, Some(hi1))), Some((b1, lo2, Some(hi2)))) =
            (self.loop_of(a), self.loop_of(b))
            && lo1 <= hi1
            && lo2 <= hi2
            && a1 == b1
        {
            return Some(self.mk_loop(a1, lo1 + lo2, Some(hi1 + hi2)));
        }
        if let (Some((a1, lo1, None)), Some((b1, lo2, None))) = (self.loop_of(a), self.loop_of(b))
            && a1 == b1
        {
            return Some(self.mk_loop(a1, lo1 + lo2, None));
        }
        let (mut x, mut y) = (a, b);
        for _ in 0..2 {
            match (self.loop_of(x), self.loop_of(y)) {
                (Some((a1, lo1, None)), Some((b1, lo2, Some(hi2)))) if lo2 <= hi2 && a1 == b1 => {
                    return Some(self.mk_loop(a1, lo1 + lo2, None));
                }
                _ => {}
            }
            if let Some((a1, lo1, hi1)) = self.loop_of(x)
                && let Some(b1) = self.un(y, &Op::Star)
                && a1 == b1
            {
                if let Some(hi1) = hi1 {
                    if lo1 <= hi1 {
                        return Some(self.mk_loop(a1, lo1, None));
                    }
                } else {
                    return Some(x);
                }
            }
            if let Some((a1, lo1, Some(hi1))) = self.loop_of(x)
                && lo1 <= hi1
                && a1 == y
            {
                return Some(self.mk_loop(a1, lo1 + 1, Some(hi1 + 1)));
            }
            core::mem::swap(&mut x, &mut y);
        }
        if let Some((a1, a2)) = self.bin(a, &Op::Concat) {
            let inner = self.mk_re_append(a2, b);
            return Some(self.mk_re_append(a1, inner));
        }
        None
    }

    fn are_complements(&self, r1: Id, r2: Id) -> bool {
        self.un(r1, &Op::Comp) == Some(r2) || self.un(r2, &Op::Comp) == Some(r1)
    }

    /// z3's `regex_to_range_predicate`: the character class `r` denotes.
    fn range_pred(&self, r: Id) -> Option<Ranges> {
        if self.is_empty(r) {
            return Some(Vec::new());
        }
        if self.is_full_char(r) {
            return Some(vec![(0, MAX_CHAR)]);
        }
        if self.is_op(r, &Op::Range) {
            let (lo, hi) = self.char_range(r)?;
            return Some(if lo > hi {
                Vec::new()
            } else {
                vec![(lo, hi.min(MAX_CHAR))]
            });
        }
        if let Some((a, b)) = self.bin(r, &Op::Union) {
            return Some(ranges_union(&self.range_pred(a)?, &self.range_pred(b)?));
        }
        if let Some((a, b)) = self.bin(r, &Op::Diff) {
            return Some(ranges_diff(&self.range_pred(a)?, &self.range_pred(b)?));
        }
        if let Some((a, b)) = self.bin(r, &Op::Inter) {
            if let Some(c) = self.un(b, &Op::Comp) {
                return Some(ranges_diff(&self.range_pred(a)?, &self.range_pred(c)?));
            }
            if let Some(c) = self.un(a, &Op::Comp) {
                return Some(ranges_diff(&self.range_pred(b)?, &self.range_pred(c)?));
            }
            return Some(ranges_inter(&self.range_pred(a)?, &self.range_pred(b)?));
        }
        None
    }

    /// z3's `seq_util::rex::mk_range(sort, lo, hi)`.
    fn mk_char_range(&mut self, lo: u32, hi: u32) -> Id {
        if lo > hi {
            return self.raw(Op::ReNone, &[]);
        }
        if lo == 0 && hi == MAX_CHAR {
            return self.raw(Op::ReAllChar, &[]);
        }
        let l = self.lit(&[lo]);
        if lo == hi {
            return self.raw(Op::ToRe, &[l]);
        }
        let h = self.lit(&[hi]);
        self.raw(Op::Range, &[l, h])
    }

    /// z3's `range_predicate_to_regex`.
    fn ranges_to_regex(&mut self, p: &Ranges) -> Id {
        if p.is_empty() {
            return self.raw(Op::ReNone, &[]);
        }
        let mut rs: Vec<Id> = p
            .iter()
            .map(|&(lo, hi)| self.mk_char_range(lo, hi))
            .collect();
        rs.sort();
        let mut acc = rs[rs.len() - 1];
        for i in (0..rs.len() - 1).rev() {
            acc = self.raw(Op::Union, &[rs[i], acc]);
        }
        acc
    }

    /// `try_collapse_re_union` / `try_collapse_re_inter`.
    fn try_collapse(&mut self, a: Id, b: Id, union: bool) -> Option<Id> {
        let pa = self.range_pred(a)?;
        let pb = self.range_pred(b)?;
        let p = if union {
            ranges_union(&pa, &pb)
        } else {
            ranges_inter(&pa, &pb)
        };
        Some(self.ranges_to_regex(&p))
    }

    /// z3's `mk_union` (`mk_re_union`).
    fn mk_union(&mut self, a: Id, b: Id) -> Id {
        if let Some(r) = self.try_collapse(a, b, true) {
            return r;
        }
        self.union_normalize(a, b)
    }

    /// z3's `mk_inter` (`mk_re_inter`).
    fn mk_inter(&mut self, a: Id, b: Id) -> Id {
        if let Some(r) = self.try_collapse(a, b, false) {
            return r;
        }
        self.inter_normalize(a, b)
    }

    /// z3's `mk_regex_union_normalize`.
    fn union_normalize(&mut self, r1: Id, r2: Id) -> Id {
        if r1 == r2 || self.is_empty(r2) || self.is_full_seq(r1) {
            return r1;
        }
        if self.is_empty(r1) || self.is_full_seq(r2) {
            return r2;
        }
        if self.is_dot_plus(r1) && self.info(r2).min_length > 0 {
            return r1;
        }
        if self.is_dot_plus(r2) && self.info(r1).min_length > 0 {
            return r2;
        }
        if let (Some((lo1, hi1)), Some((lo2, hi2))) = (self.char_range(r1), self.char_range(r2))
            && lo2 <= hi1.saturating_add(1)
            && lo1 <= hi2.saturating_add(1)
        {
            return self.mk_char_range(lo1.min(lo2), hi1.max(hi2));
        }
        let full = self.raw(Op::ReAll, &[]);
        self.merge_regex_sets(r1, r2, full, true)
    }

    /// z3's `mk_regex_inter_normalize`.
    fn inter_normalize(&mut self, mut r1: Id, mut r2: Id) -> Id {
        if self.is_epsilon(r2) {
            core::mem::swap(&mut r1, &mut r2);
        }
        if r1 == r2 || self.is_empty(r1) || self.is_full_seq(r2) {
            return r1;
        }
        if self.is_empty(r2) || self.is_full_seq(r1) {
            return r2;
        }
        let none = self.raw(Op::ReNone, &[]);
        if self.is_epsilon(r1) {
            return match self.info(r2).nullable {
                Some(true) => r1,
                Some(false) => none,
                None => self.merge_regex_sets(r1, r2, none, false),
            };
        }
        if self.is_dot_plus(r1) && self.info(r2).min_length > 0 {
            return r2;
        }
        if self.is_dot_plus(r2) && self.info(r1).min_length > 0 {
            return r1;
        }
        if let (Some((lo1, hi1)), Some((lo2, hi2))) = (self.char_range(r1), self.char_range(r2)) {
            return self.mk_char_range(lo1.max(lo2), hi1.min(hi2));
        }
        self.merge_regex_sets(r1, r2, none, false)
    }

    /// The `compose` of the union (`union`) or intersection normal form.
    fn compose_set(&mut self, x: Id, y: Id, union: bool) -> Id {
        if union {
            if self.is_subset(x, y) {
                y
            } else if self.is_subset(y, x) {
                x
            } else {
                self.raw(Op::Union, &[x, y])
            }
        } else if self.is_subset(x, y) {
            x
        } else if self.is_subset(y, x) {
            y
        } else {
            self.raw(Op::Inter, &[x, y])
        }
    }

    /// z3's `merge_regex_sets`: merge two right-nested unions (intersections)
    /// into one sorted by expression id.
    fn merge_regex_sets(&mut self, r1: Id, r2: Id, unit: Id, union: bool) -> Id {
        let set_op = if union { Op::Union } else { Op::Inter };
        let key = |me: &Self, x: Id| me.un(x, &Op::Comp).unwrap_or(x);
        let compare = |me: &Self, x: Id, y: Id| -> i32 {
            if x == y {
                return 0;
            }
            if key(me, x) < key(me, y) { -1 } else { 1 }
        };
        let mut prefix: Vec<Id> = Vec::new();
        let (mut ar, mut br) = (r1, r2);
        let suffix = loop {
            if ar == br {
                break ar;
            }
            if self.are_complements(ar, br) {
                return unit;
            }
            if self.bin(br, &set_op).is_some() && self.bin(ar, &set_op).is_none() {
                core::mem::swap(&mut ar, &mut br);
            }
            if let Some((b, br1)) = self.bin(br, &set_op) {
                let (a, ar1) = self.bin(ar, &set_op).unwrap();
                if self.are_complements(a, b) {
                    return unit;
                }
                match compare(self, a, b) {
                    0 => {
                        prefix.push(a);
                        ar = ar1;
                        br = br1;
                    }
                    -1 => {
                        prefix.push(a);
                        ar = ar1;
                    }
                    _ => {
                        prefix.push(b);
                        br = br1;
                    }
                }
                continue;
            }
            if let Some((a, ar1)) = self.bin(ar, &set_op) {
                if self.are_complements(a, br) {
                    return unit;
                }
                match compare(self, a, br) {
                    0 => break ar,
                    -1 => {
                        prefix.push(a);
                        ar = ar1;
                    }
                    _ => {
                        prefix.push(br);
                        break ar;
                    }
                }
                continue;
            }
            if compare(self, ar, br) == -1 {
                core::mem::swap(&mut ar, &mut br);
            }
            prefix.push(br);
            break ar;
        };
        let mut result = suffix;
        while let Some(p) = prefix.pop() {
            result = self.compose_set(p, result, union);
        }
        result
    }

    /// z3's `seq_subset::is_subset` (heuristic, depth-bounded).
    fn is_subset(&self, a: Id, b: Id) -> bool {
        self.is_subset_rec(a, b, 0)
    }

    fn is_subset_rec(&self, mut a: Id, mut b: Id, depth: u32) -> bool {
        const MAX_DEPTH: u32 = 3;
        loop {
            if a == b || self.is_empty(a) || self.is_full_seq(b) {
                return true;
            }
            if self.is_epsilon(a) && self.info(b).nullable == Some(true) {
                return true;
            }
            if depth >= MAX_DEPTH {
                return false;
            }
            if self.is_dot_plus(b) && self.info(a).nullable == Some(false) {
                return true;
            }
            if self.is_epsilon(a) && self.un(b, &Op::Star).is_some() {
                return true;
            }
            if let Some(b1) = self.un(b, &Op::Star)
                && self.is_subset_rec(a, b1, depth)
            {
                return true;
            }
            if let (Some(a1), Some(b1)) = (self.un(a, &Op::Star), self.un(b, &Op::Star))
                && self.is_subset_rec(a1, b1, depth + 1)
            {
                return true;
            }
            if let (Some(a1), Some(b1)) = (self.un(a, &Op::Plus), self.un(b, &Op::Plus))
                && self.is_subset_rec(a1, b1, depth)
            {
                return true;
            }
            if let Some(b1) = self.un(b, &Op::Plus)
                && self.is_subset_rec(a, b1, depth)
            {
                return true;
            }
            if let (Some(a1), Some(b1)) = (self.un(a, &Op::Plus), self.un(b, &Op::Star))
                && self.is_subset_rec(a1, b1, depth + 1)
            {
                return true;
            }
            if let (Some((la, ua)), Some((lb, ub))) = (self.char_range(a), self.char_range(b))
                && lb <= la
                && ua <= ub
            {
                return true;
            }
            if let Some(a1) = self.un(a, &Op::ToRe)
                && let Some((lb, ub)) = self.char_range(b)
                && let Some([c]) = self.str_lit(a1)
                && lb <= *c
                && *c <= ub
            {
                return true;
            }
            if let Some((b1, b2)) = self.bin(b, &Op::Union)
                && (self.is_subset_rec(a, b1, depth + 1) || self.is_subset_rec(a, b2, depth + 1))
            {
                return true;
            }
            if let Some((a1, a2)) = self.bin(a, &Op::Union)
                && self.is_subset_rec(a1, b, depth + 1)
                && self.is_subset_rec(a2, b, depth + 1)
            {
                return true;
            }
            if let Some((a1, a2)) = self.bin(a, &Op::Inter)
                && (self.is_subset_rec(a1, b, depth + 1) || self.is_subset_rec(a2, b, depth + 1))
            {
                return true;
            }
            if let Some((b1, b2)) = self.bin(b, &Op::Inter)
                && self.is_subset_rec(a, b1, depth + 1)
                && self.is_subset_rec(a, b2, depth + 1)
            {
                return true;
            }
            if let (Some((a1, la, Some(ua))), Some((b1, lb, Some(ub)))) =
                (self.loop_of(a), self.loop_of(b))
                && lb <= la
                && ua <= ub
                && self.is_subset_rec(a1, b1, depth + 1)
            {
                return true;
            }
            if let Some((a1, _)) = self.bin(a, &Op::Diff)
                && self.is_subset_rec(a1, b, depth + 1)
            {
                return true;
            }
            if let Some((b1, b2)) = self.bin(b, &Op::Concat)
                && self.is_full_seq(b1)
                && (self.is_subset_rec(a, b2, depth) || self.ends_with(a, b2))
            {
                return true;
            }
            if let Some((b1, b2)) = self.bin(b, &Op::Concat)
                && self.is_full_seq(b2)
                && self.is_subset_rec(a, b1, depth)
            {
                return true;
            }
            if let Some((a1, a2)) = self.bin(a, &Op::Concat)
                && let Some(b1) = self.un(b, &Op::Star)
            {
                if self.is_subset_rec(a1, b1, depth + 1) && self.is_subset_rec(a2, b, depth + 1) {
                    return true;
                }
                if self.is_subset_rec(a2, b1, depth + 1) && self.is_subset_rec(a1, b, depth + 1) {
                    return true;
                }
            }
            if let (Some((a1, a2)), Some((b1, b2))) =
                (self.bin(a, &Op::Concat), self.bin(b, &Op::Concat))
                && self.is_subset_rec(a1, b1, depth + 1)
            {
                a = a2;
                b = b2;
                continue;
            }
            if let (Some(a1), Some(b1)) = (self.un(a, &Op::Comp), self.un(b, &Op::Comp)) {
                return self.is_subset_rec(b1, a1, depth + 1);
            }
            return false;
        }
    }

    fn flatten_concat(&self, a: Id, out: &mut Vec<Id>) {
        if let Some((a1, a2)) = self.bin(a, &Op::Concat) {
            self.flatten_concat(a1, out);
            self.flatten_concat(a2, out);
        } else {
            out.push(a);
        }
    }

    fn ends_with(&self, a: Id, suf: Id) -> bool {
        if a == suf {
            return true;
        }
        let (mut af, mut sf) = (Vec::new(), Vec::new());
        self.flatten_concat(a, &mut af);
        self.flatten_concat(suf, &mut sf);
        sf.len() <= af.len() && af[af.len() - sf.len()..] == sf[..]
    }

    /// z3's `mk_complement` (`mk_re_complement`).
    fn mk_complement(&mut self, a: Id) -> Id {
        if let Some((e1, e2)) = self.bin(a, &Op::Inter) {
            let x = self.mk_complement(e1);
            let y = self.mk_complement(e2);
            return self.mk_union(x, y);
        }
        if let Some((e1, e2)) = self.bin(a, &Op::Union) {
            let x = self.mk_complement(e1);
            let y = self.mk_complement(e2);
            return self.mk_inter(x, y);
        }
        if self.is_empty(a) {
            return self.raw(Op::ReAll, &[]);
        }
        if self.is_full_seq(a) {
            return self.raw(Op::ReNone, &[]);
        }
        if let Some(e1) = self.un(a, &Op::Comp) {
            return e1;
        }
        if self.is_epsilon(a) {
            let dot = self.raw(Op::ReAllChar, &[]);
            return self.mk_plus(dot);
        }
        if let Some((c, e1, e2)) = self.ite_of(a) {
            let x = self.mk_complement(e1);
            let y = self.mk_complement(e2);
            return self.mk_ite(c, x, y);
        }
        self.raw(Op::Comp, &[a])
    }

    fn ite_of(&self, t: Id) -> Option<(Id, Id, Id)> {
        match &self.nodes[t] {
            Node::App(Op::Ite, args) => Some((args[0], args[1], args[2])),
            _ => None,
        }
    }

    /// z3's `mk_diff` (`mk_re_diff`).
    fn mk_diff(&mut self, a: Id, b: Id) -> Id {
        if let (Some(pa), Some(pb)) = (self.range_pred(a), self.range_pred(b)) {
            return self.ranges_to_regex(&ranges_diff(&pa, &pb));
        }
        let c = self.mk_complement(b);
        self.mk_inter(a, c)
    }

    /// z3's `mk_star` (`mk_re_star`).
    fn mk_star(&mut self, a: Id) -> Id {
        if self.un(a, &Op::Star).is_some() || self.is_full_seq(a) {
            return a;
        }
        if self.is_full_char(a) {
            return self.raw(Op::ReAll, &[]);
        }
        if self.is_empty(a) {
            let e = self.lit(&[]);
            return self.raw(Op::ToRe, &[e]);
        }
        if self.is_epsilon(a) {
            return a;
        }
        if let Some(b) = self.un(a, &Op::Plus) {
            if self.is_full_char(b) {
                return self.raw(Op::ReAll, &[]);
            }
            return self.mk_star(b);
        }
        if let Some((b, c)) = self.bin(a, &Op::Union) {
            if let Some(b1) = self.un(b, &Op::Star) {
                let u = self.mk_union(b1, c);
                return self.mk_star(u);
            }
            if let Some(c1) = self.un(c, &Op::Star) {
                let u = self.mk_union(b, c1);
                return self.mk_star(u);
            }
            if self.is_epsilon(b) {
                return self.mk_star(c);
            }
            if self.is_epsilon(c) {
                return self.mk_star(b);
            }
        }
        if let Some((b, c)) = self.bin(a, &Op::Concat) {
            if let (Some(b1), Some(c1)) = (self.un(b, &Op::Star), self.un(c, &Op::Star)) {
                let u = self.mk_union(b1, c1);
                return self.mk_star(u);
            }
            if self.is_full_seq(b) {
                let e = self.lit(&[]);
                let eps = self.raw(Op::ToRe, &[e]);
                return self.mk_union(eps, a);
            }
        }
        if let Some((c, b1, c1)) = self.ite_of(a) {
            let x = self.mk_star(b1);
            let y = self.mk_star(c1);
            return self.mk_ite(c, x, y);
        }
        self.raw(Op::Star, &[a])
    }

    /// z3's `mk_plus` (`mk_re_plus`).
    fn mk_plus(&mut self, a: Id) -> Id {
        if self.is_full_char(a) {
            return self.raw(Op::Plus, &[a]);
        }
        if self.is_empty(a)
            || self.is_full_seq(a)
            || self.is_epsilon(a)
            || self.un(a, &Op::Plus).is_some()
            || self.un(a, &Op::Star).is_some()
        {
            return a;
        }
        let s = self.mk_star(a);
        self.mk_re_append(a, s)
    }

    /// z3's `mk_opt` (`mk_re_opt`).
    fn mk_opt(&mut self, a: Id) -> Id {
        let e = self.lit(&[]);
        let eps = self.raw(Op::ToRe, &[e]);
        self.mk_union(eps, a)
    }

    /// z3's `mk_loop` (`mk_re_loop` over the indexed form).
    fn mk_loop(&mut self, a: Id, lo: u32, hi: Option<u32>) -> Id {
        match hi {
            Some(hi) if lo > hi => return self.raw(Op::ReNone, &[]),
            Some(0) => {
                let e = self.lit(&[]);
                return self.raw(Op::ToRe, &[e]);
            }
            None if lo == 0 => return self.mk_star(a),
            Some(1) if lo == 1 => return a,
            _ => {}
        }
        if hi.is_none()
            && let Some((inner, lo1, None)) = self.loop_of(a)
        {
            return self.mk_loop(inner, lo * lo1, None);
        }
        if let (Some(hi2), Some((inner, lo1, Some(hi1)))) = (hi, self.loop_of(a))
            && lo1 == hi1
            && lo == hi2
        {
            return self.mk_loop(inner, lo * lo1, Some(hi2 * hi1));
        }
        self.raw(Op::Loop(lo, hi), &[a])
    }

    /// z3's `mk_re_range`.
    fn mk_range(&mut self, lo: Id, hi: Id) -> Id {
        let long = |me: &Self, t: Id| me.str_lit(t).is_some_and(|l| l.len() != 1);
        if long(self, lo) || long(self, hi) {
            return self.raw(Op::ReNone, &[]);
        }
        if let (Some([a]), Some([b])) = (self.str_lit(lo), self.str_lit(hi)) {
            let (a, b) = (*a, *b);
            if a > b {
                return self.raw(Op::ReNone, &[]);
            }
            if a == b {
                let l = self.lit(&[a]);
                return self.raw(Op::ToRe, &[l]);
            }
        }
        self.raw(Op::Range, &[lo, hi])
    }

    // ----- printing -----------------------------------------------------------

    /// Print `t` as z3 does, rendering literals with `lit`.
    pub fn pp(
        &self,
        t: Id,
        lit: &dyn Fn(&[u32]) -> String,
        sym: &dyn Fn(&str) -> String,
    ) -> String {
        let mut arena: Vec<PpNode> = Vec::new();
        let mut map: BTreeMap<Id, usize> = BTreeMap::new();
        let root = self.to_pp(t, &mut arena, &mut map, lit, sym);
        pp_term(&arena, root, &|h| matches!(h, "and" | "or" | "+" | "*"))
    }

    fn to_pp(
        &self,
        t: Id,
        arena: &mut Vec<PpNode>,
        map: &mut BTreeMap<Id, usize>,
        lit: &dyn Fn(&[u32]) -> String,
        sym: &dyn Fn(&str) -> String,
    ) -> usize {
        if let Some(&i) = map.get(&t) {
            return i;
        }
        let (head, args): (String, Vec<usize>) = match &self.nodes[t] {
            Node::Var(n, _) => (sym(n), Vec::new()),
            Node::Lit(l) => (lit(l), Vec::new()),
            Node::Num(n) if *n < 0 => {
                let a = arena.len();
                arena.push(PpNode {
                    head: alloc::format!("{}", -n),
                    args: Vec::new(),
                    indexed: false,
                });
                ("-".to_string(), vec![a])
            }
            Node::Num(n) => (alloc::format!("{n}"), Vec::new()),
            Node::True => ("true".to_string(), Vec::new()),
            Node::False => ("false".to_string(), Vec::new()),
            Node::App(op, xs) => {
                let head = match op {
                    Op::Not => "not".to_string(),
                    Op::Eq => "=".to_string(),
                    Op::And => "and".to_string(),
                    Op::Or => "or".to_string(),
                    Op::Ite => "ite".to_string(),
                    Op::InRe => "str.in_re".to_string(),
                    Op::ToRe => "str.to_re".to_string(),
                    Op::ReNone => "re.none".to_string(),
                    Op::ReAll => "re.all".to_string(),
                    Op::ReAllChar => "re.allchar".to_string(),
                    Op::Range => "re.range".to_string(),
                    Op::Concat => "re.++".to_string(),
                    Op::Union => "re.union".to_string(),
                    Op::Inter => "re.inter".to_string(),
                    Op::Star => "re.*".to_string(),
                    Op::Plus => "re.+".to_string(),
                    Op::Opt => "re.opt".to_string(),
                    Op::Comp => "re.comp".to_string(),
                    Op::Diff => "re.diff".to_string(),
                    Op::Loop(lo, Some(hi)) => alloc::format!("(_ re.loop {lo} {hi})"),
                    Op::Loop(lo, None) => alloc::format!("(_ re.loop {lo})"),
                    Op::Prefix => "str.prefixof".to_string(),
                    Op::Suffix => "str.suffixof".to_string(),
                    Op::StrLen => "str.len".to_string(),
                };
                let args = xs
                    .clone()
                    .iter()
                    .map(|&x| self.to_pp(x, arena, map, lit, sym))
                    .collect();
                (head, args)
            }
        };
        let indexed = matches!(&self.nodes[t], Node::App(Op::Loop(..), _));
        let i = arena.len();
        arena.push(PpNode {
            head,
            args,
            indexed,
        });
        map.insert(t, i);
        i
    }
}

/// Relational composition of span matrices: `s[i..k] ∈ A ∧ s[k..j] ∈ B`.
fn compose(a: &[Vec<bool>], b: &[Vec<bool>]) -> Vec<Vec<bool>> {
    let n = a.len();
    let mut m = vec![vec![false; n]; n];
    for i in 0..n {
        for k in i..n {
            if a[i][k] {
                for j in k..n {
                    if b[k][j] {
                        m[i][j] = true;
                    }
                }
            }
        }
    }
    m
}

#[cfg(test)]
mod tests {
    use super::*;

    fn show(r: &ReSimp, t: Id) -> String {
        r.pp(
            t,
            &|l| {
                let s: String = l.iter().filter_map(|&c| char::from_u32(c)).collect();
                alloc::format!("\"{s}\"")
            },
            &|n| n.to_string(),
        )
    }

    #[test]
    fn plus_of_plus_is_aliased_like_z3() {
        let mut r = ReSimp::default();
        let v = r.var("r", Srt::Re);
        let p = r.app(Op::Plus, &[v]);
        let pp = r.app(Op::Plus, &[p]);
        let eq = r.app(Op::Eq, &[p, pp]);
        let s = r.simplify(eq);
        assert_eq!(
            show(&r, s),
            "(let ((a!1 (re.++ (re.* r) (re.* (re.++ r (re.* r))))))\n  (= (re.++ r (re.* r)) (re.++ r a!1)))"
        );
    }

    #[test]
    fn membership_and_algebra() {
        let mut r = ReSimp::default();
        let a = r.var("a", Srt::Str);
        let none = r.app(Op::ReNone, &[]);
        let st = r.app(Op::Star, &[none]);
        let m = r.app(Op::InRe, &[a, st]);
        let s = r.simplify(m);
        assert_eq!(show(&r, s), "(= \"\" a)");
        let x = r.lit(&['a' as u32]);
        let y = r.lit(&['b' as u32]);
        let rx = r.app(Op::ToRe, &[x]);
        let ry = r.app(Op::ToRe, &[y]);
        let u = r.app(Op::Union, &[rx, ry]);
        let c = r.app(Op::Comp, &[u]);
        let m = r.app(Op::InRe, &[x, c]);
        let s = r.simplify(m);
        assert_eq!(show(&r, s), "false");
    }

    #[test]
    fn length_residues_refute_membership() {
        // `(ab){1,2}` has even lengths, `re.allchar` length 1: their
        // intersection accepts nothing (z3's `can_be_member`).
        let mut r = ReSimp::default();
        let a = r.var("a", Srt::Str);
        let ab = r.lit(&['a' as u32, 'b' as u32]);
        let rab = r.app(Op::ToRe, &[ab]);
        let lp = r.app(Op::Loop(1, Some(2)), &[rab]);
        let any = r.app(Op::ReAllChar, &[]);
        let i = r.app(Op::Inter, &[lp, any]);
        let m = r.app(Op::InRe, &[a, i]);
        let s = r.simplify(m);
        assert_eq!(show(&r, s), "false");
    }

    #[test]
    fn disjunctions_out_of_order_are_sorted_by_id() {
        // `ite(len a = 0, true, a = "ab")` becomes a disjunction whose
        // disjuncts are out of `ast_lt` order, so z3 sorts them by id.
        let mut r = ReSimp::default();
        let a = r.var("a", Srt::Str);
        let e = r.lit(&[]);
        let ab = r.lit(&['a' as u32, 'b' as u32]);
        let re = r.app(Op::ToRe, &[e]);
        let rab = r.app(Op::ToRe, &[ab]);
        let u = r.app(Op::Union, &[re, rab]);
        let m = r.app(Op::InRe, &[a, u]);
        let s = r.simplify(m);
        assert_eq!(show(&r, s), "(or (= (str.len a) 0) (= a \"ab\"))");
    }
}
