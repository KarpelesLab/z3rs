//! z3's `th_rewriter` as the `simplify` command runs it, over a term arena of
//! its own (`z3/src/ast/rewriter/{th_rewriter,rewriter_def.h,bool_rewriter,
//! poly_rewriter_def.h,arith_rewriter}.cpp`, MIT).
//!
//! The rest of z3rs lowers terms while building them (`abs` to an `ite`,
//! `bvugt` to a swapped `bvult`, …), which loses the shape z3's `simplify`
//! prints. This module keeps the source shape: the front end builds the term
//! here operator by operator, and [`Simp::simplify`] rewrites it with z3's
//! default rules — `flat`, `elim_ite`, `sort_disjunctions`, `ite_extra_rules`
//! on; `som`, `sort_sums` (arithmetic), `hoist_mul`, `push_ite_*`,
//! `pull_cheap_ite`, `gcd_rounding`, `arith_lhs` off — so the result prints
//! as z3's does.
//!
//! Terms are hash-consed; each node carries an id in creation order, standing
//! in for z3's expression ids (which order disjunctions). The structural order
//! of `ast_lt.cpp` (`lt`), which orders products, is computed on the terms.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::cmp::Ordering;

use puremp::{Int, Rational};

/// A term: an index into [`Simp`]'s arena.
pub type T = usize;

/// A sort.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Sort {
    Bool,
    Int,
    Real,
    /// `(_ BitVec n)`.
    Bv(u32),
    /// An uninterpreted sort, by name.
    User(String),
}

impl Sort {
    /// z3's sort name (`bv` for bit-vectors).
    fn name(&self) -> &str {
        match self {
            Sort::Bool => "Bool",
            Sort::Int => "Int",
            Sort::Real => "Real",
            Sort::Bv(_) => "bv",
            Sort::User(n) => n,
        }
    }

    /// Is this `Int` or `Real`?
    pub fn is_arith_sort(&self) -> bool {
        matches!(self, Sort::Int | Sort::Real)
    }
}

/// `ast_lt` on sorts: by name, then parameters.
fn sort_cmp(a: &Sort, b: &Sort) -> Ordering {
    if a == b {
        return Ordering::Equal;
    }
    match a.name().as_bytes().cmp(b.name().as_bytes()) {
        Ordering::Equal => match (a, b) {
            (Sort::Bv(x), Sort::Bv(y)) => x.cmp(y),
            _ => Ordering::Equal,
        },
        o => o,
    }
}

/// Bit-vector operators.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum BvOp {
    Add,
    Sub,
    Mul,
    Neg,
    Udiv,
    Urem,
    Sdiv,
    Srem,
    Smod,
    And,
    Or,
    Xor,
    Not,
    Nand,
    Nor,
    Xnor,
    Shl,
    Lshr,
    Ashr,
    Concat,
    Ule,
    Ult,
    Uge,
    Ugt,
    Sle,
    Slt,
    Sge,
    Sgt,
    Comp,
}

impl BvOp {
    fn name(self) -> &'static str {
        match self {
            BvOp::Add => "bvadd",
            BvOp::Sub => "bvsub",
            BvOp::Mul => "bvmul",
            BvOp::Neg => "bvneg",
            BvOp::Udiv => "bvudiv",
            BvOp::Urem => "bvurem",
            BvOp::Sdiv => "bvsdiv",
            BvOp::Srem => "bvsrem",
            BvOp::Smod => "bvsmod",
            BvOp::And => "bvand",
            BvOp::Or => "bvor",
            BvOp::Xor => "bvxor",
            BvOp::Not => "bvnot",
            BvOp::Nand => "bvnand",
            BvOp::Nor => "bvnor",
            BvOp::Xnor => "bvxnor",
            BvOp::Shl => "bvshl",
            BvOp::Lshr => "bvlshr",
            BvOp::Ashr => "bvashr",
            BvOp::Concat => "concat",
            BvOp::Ule => "bvule",
            BvOp::Ult => "bvult",
            BvOp::Uge => "bvuge",
            BvOp::Ugt => "bvugt",
            BvOp::Sle => "bvsle",
            BvOp::Slt => "bvslt",
            BvOp::Sge => "bvsge",
            BvOp::Sgt => "bvsgt",
            BvOp::Comp => "bvcomp",
        }
    }

    /// Does this operator return a Boolean?
    fn is_pred(self) -> bool {
        matches!(
            self,
            BvOp::Ule
                | BvOp::Ult
                | BvOp::Uge
                | BvOp::Ugt
                | BvOp::Sle
                | BvOp::Slt
                | BvOp::Sge
                | BvOp::Sgt
        )
    }
}

/// An operator (a function declaration up to its argument sorts).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Op {
    True,
    False,
    Not,
    And,
    Or,
    Implies,
    Xor,
    Eq,
    Distinct,
    Ite,
    /// An arithmetic numeral (its sort tells Int from Real).
    Num(Rational),
    Add,
    Sub,
    Uminus,
    Mul,
    Div,
    Idiv,
    Mod,
    Rem,
    Le,
    Ge,
    Lt,
    Gt,
    ToReal,
    ToInt,
    IsInt,
    Abs,
    /// A bit-vector numeral (value in `[0, 2^w)`).
    BvNum(Int),
    Bv(BvOp),
    Extract(u32, u32),
    ZeroExt(u32),
    SignExt(u32),
    Repeat(u32),
    RotL(u32),
    RotR(u32),
    /// An uninterpreted function or constant.
    Uf(String),
}

impl Op {
    /// z3's declaration name.
    fn name(&self, sort: &Sort) -> &str {
        match self {
            Op::True => "true",
            Op::False => "false",
            Op::Not => "not",
            Op::And => "and",
            Op::Or => "or",
            Op::Implies => "=>",
            Op::Xor => "xor",
            Op::Eq => "=",
            Op::Distinct => "distinct",
            Op::Ite => "if",
            Op::Num(_) => {
                if *sort == Sort::Int {
                    "Int"
                } else {
                    "Real"
                }
            }
            Op::Add => "+",
            Op::Sub | Op::Uminus => "-",
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
            Op::BvNum(_) => "bv",
            Op::Bv(b) => b.name(),
            Op::Extract(..) => "extract",
            Op::ZeroExt(_) => "zero_extend",
            Op::SignExt(_) => "sign_extend",
            Op::Repeat(_) => "repeat",
            Op::RotL(_) => "rotate_left",
            Op::RotR(_) => "rotate_right",
            Op::Uf(n) => n,
        }
    }

    /// The declaration's parameters, as `ast_lt` compares them (rationals and
    /// integers; integer parameters as rationals).
    fn params(&self, sort: &Sort) -> Vec<Rational> {
        let int = |v: u32| Rational::from(i64::from(v));
        match self {
            Op::Num(r) => vec![r.clone(), int(u32::from(*sort == Sort::Int))],
            Op::BvNum(v) => {
                let w = if let Sort::Bv(w) = sort { *w } else { 0 };
                vec![Rational::from_integer(v.clone()), int(w)]
            }
            Op::Extract(h, l) => vec![int(*h), int(*l)],
            Op::ZeroExt(k) | Op::SignExt(k) | Op::Repeat(k) | Op::RotL(k) | Op::RotR(k) => {
                vec![int(*k)]
            }
            _ => Vec::new(),
        }
    }
}

/// One hash-consed node.
#[derive(Clone, Debug)]
struct Node {
    op: Op,
    args: Vec<T>,
    sort: Sort,
    depth: u32,
}

/// A rewrite step's outcome (`br_status`): the rewritten term is final
/// (`Done`), must be rewritten again to the given depth (`Rw`, with
/// `u32::MAX` for `BR_REWRITE_FULL`), or no rule applied (`None` returned).
enum St {
    Done(T),
    Rw(T, u32),
}

const FULL: u32 = u32::MAX;

/// The kind of an (in)equality, `arith_rewriter`'s `op_kind`.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Le,
    Ge,
    Eq,
}

fn inv(k: Kind) -> Kind {
    match k {
        Kind::Le => Kind::Ge,
        Kind::Ge => Kind::Le,
        Kind::Eq => Kind::Eq,
    }
}

/// The term arena and the rewriter.
#[derive(Default)]
pub struct Simp {
    nodes: Vec<Node>,
    table: BTreeMap<(Op, Vec<T>, Sort), T>,
    /// Number of parent slots referencing each node of the input term.
    input_rc: BTreeMap<T, u32>,
    /// The nodes of the input term.
    input: BTreeSet<T>,
    /// Results of unbounded rewriting of input nodes.
    cache: BTreeMap<T, T>,
    /// Terms the rewriter's cache keeps alive (reference count above one):
    /// rule results rewritten again, their rewritten forms, and the results
    /// of shared input subterms.
    pinned: BTreeSet<T>,
    /// For each node, how many created nodes use it as an argument.
    parents: Vec<u32>,
}

fn rat(v: i64) -> Rational {
    Rational::from(v)
}

/// z3's `mod` on integral rationals: the remainder in `[0, |b|)`.
fn rmod(a: &Rational, b: &Rational) -> Rational {
    a.rem_euclid(b)
}

/// z3's `div` on integral rationals: `(a - mod(a, b)) / b`.
fn rdiv(a: &Rational, b: &Rational) -> Rational {
    (a - &rmod(a, b)) / b.clone()
}

fn rgcd(a: &Rational, b: &Rational) -> Rational {
    Rational::from_integer(a.numerator().gcd(b.numerator()))
}

impl Simp {
    /// An empty arena.
    pub fn new() -> Simp {
        Simp::default()
    }

    // ---- construction ------------------------------------------------------

    /// The hash-consed node `op(args)` of sort `sort`.
    pub fn mk_sorted(&mut self, op: Op, args: Vec<T>, sort: Sort) -> T {
        let key = (op, args, sort);
        if let Some(&t) = self.table.get(&key) {
            return t;
        }
        let depth = 1 + key
            .1
            .iter()
            .map(|&a| self.nodes[a].depth)
            .max()
            .unwrap_or(0);
        let t = self.nodes.len();
        for &a in &key.1 {
            self.parents[a] += 1;
        }
        self.parents.push(0);
        self.nodes.push(Node {
            op: key.0.clone(),
            args: key.1.clone(),
            sort: key.2.clone(),
            depth,
        });
        self.table.insert(key, t);
        t
    }

    /// `op(args)` with its sort inferred from the operator and arguments.
    pub fn mk(&mut self, op: Op, args: Vec<T>) -> T {
        let s0 = || self.nodes[args[0]].sort.clone();
        let sort = match &op {
            Op::True
            | Op::False
            | Op::Not
            | Op::And
            | Op::Or
            | Op::Implies
            | Op::Xor
            | Op::Eq
            | Op::Distinct
            | Op::Le
            | Op::Ge
            | Op::Lt
            | Op::Gt
            | Op::IsInt => Sort::Bool,
            Op::Ite => self.nodes[args[1]].sort.clone(),
            Op::Add | Op::Sub | Op::Uminus | Op::Mul | Op::Idiv | Op::Mod | Op::Rem | Op::Abs => {
                s0()
            }
            Op::Div | Op::ToReal => Sort::Real,
            Op::ToInt => Sort::Int,
            Op::Bv(BvOp::Concat) => Sort::Bv(args.iter().map(|&a| self.bv_width(a)).sum::<u32>()),
            Op::Bv(BvOp::Comp) => Sort::Bv(1),
            Op::Bv(b) if b.is_pred() => Sort::Bool,
            Op::Bv(_) | Op::RotL(_) | Op::RotR(_) => s0(),
            Op::Extract(h, l) => Sort::Bv(h - l + 1),
            Op::ZeroExt(k) | Op::SignExt(k) => Sort::Bv(self.bv_width(args[0]) + k),
            Op::Repeat(k) => Sort::Bv(self.bv_width(args[0]) * k),
            Op::Num(_) | Op::BvNum(_) | Op::Uf(_) => {
                panic!("mk: numerals and uninterpreted symbols need an explicit sort")
            }
        };
        self.mk_sorted(op, args, sort)
    }

    pub fn mk_true(&mut self) -> T {
        self.mk_sorted(Op::True, Vec::new(), Sort::Bool)
    }

    pub fn mk_false(&mut self) -> T {
        self.mk_sorted(Op::False, Vec::new(), Sort::Bool)
    }

    fn mk_bool(&mut self, b: bool) -> T {
        if b { self.mk_true() } else { self.mk_false() }
    }

    /// An arithmetic numeral of sort Int (`is_int`) or Real.
    pub fn mk_num(&mut self, r: Rational, is_int: bool) -> T {
        let s = if is_int { Sort::Int } else { Sort::Real };
        self.mk_sorted(Op::Num(r), Vec::new(), s)
    }

    /// A bit-vector numeral of width `w` (reduced modulo `2^w`).
    pub fn mk_bv_num(&mut self, v: &Int, w: u32) -> T {
        let v = v.mod_2k(u64::from(w));
        self.mk_sorted(Op::BvNum(v), Vec::new(), Sort::Bv(w))
    }

    fn mk_not(&mut self, a: T) -> T {
        self.mk(Op::Not, vec![a])
    }

    fn mk_eq(&mut self, a: T, b: T) -> T {
        self.mk(Op::Eq, vec![a, b])
    }

    fn mk_ite(&mut self, c: T, t: T, e: T) -> T {
        self.mk(Op::Ite, vec![c, t, e])
    }

    fn mk_or2(&mut self, a: T, b: T) -> T {
        self.mk(Op::Or, vec![a, b])
    }

    fn mk_and2(&mut self, a: T, b: T) -> T {
        self.mk(Op::And, vec![a, b])
    }

    /// The node's operator.
    pub fn op(&self, t: T) -> &Op {
        &self.nodes[t].op
    }

    /// The node's arguments.
    pub fn args(&self, t: T) -> &[T] {
        &self.nodes[t].args
    }

    /// The node's sort.
    pub fn sort(&self, t: T) -> &Sort {
        &self.nodes[t].sort
    }

    fn arg(&self, t: T, i: usize) -> T {
        self.nodes[t].args[i]
    }

    fn bv_width(&self, t: T) -> u32 {
        match self.nodes[t].sort {
            Sort::Bv(w) => w,
            _ => 0,
        }
    }

    fn is_op(&self, t: T, op: &Op) -> bool {
        self.nodes[t].op == *op
    }

    fn is_true(&self, t: T) -> bool {
        self.is_op(t, &Op::True)
    }

    fn is_false(&self, t: T) -> bool {
        self.is_op(t, &Op::False)
    }

    fn is_not(&self, t: T) -> Option<T> {
        self.is_op(t, &Op::Not).then(|| self.arg(t, 0))
    }

    fn is_ite(&self, t: T) -> Option<(T, T, T)> {
        self.is_op(t, &Op::Ite)
            .then(|| (self.arg(t, 0), self.arg(t, 1), self.arg(t, 2)))
    }

    fn is_bool(&self, t: T) -> bool {
        self.nodes[t].sort == Sort::Bool
    }

    /// An arithmetic numeral's value.
    fn arith_num(&self, t: T) -> Option<&Rational> {
        match &self.nodes[t].op {
            Op::Num(r) => Some(r),
            _ => None,
        }
    }

    /// `m.is_value`: a numeral or a Boolean constant.
    fn is_value(&self, t: T) -> bool {
        matches!(
            self.nodes[t].op,
            Op::True | Op::False | Op::Num(_) | Op::BvNum(_)
        )
    }

    /// `m.are_distinct`: two different values.
    fn are_distinct(&self, a: T, b: T) -> bool {
        a != b && self.is_value(a) && self.is_value(b)
    }

    /// Is this an application of the arithmetic family (numerals included)?
    fn is_arith_app(&self, t: T) -> bool {
        matches!(
            self.nodes[t].op,
            Op::Num(_)
                | Op::Add
                | Op::Sub
                | Op::Uminus
                | Op::Mul
                | Op::Div
                | Op::Idiv
                | Op::Mod
                | Op::Rem
                | Op::Le
                | Op::Ge
                | Op::Lt
                | Op::Gt
                | Op::ToReal
                | Op::ToInt
                | Op::IsInt
                | Op::Abs
        )
    }

    /// Is this an application of the bit-vector family?
    fn is_bv_app(&self, t: T) -> bool {
        matches!(
            self.nodes[t].op,
            Op::BvNum(_)
                | Op::Bv(_)
                | Op::Extract(..)
                | Op::ZeroExt(_)
                | Op::SignExt(_)
                | Op::Repeat(_)
                | Op::RotL(_)
                | Op::RotR(_)
        )
    }

    // ---- ast_lt --------------------------------------------------------------

    /// `ast_lt.cpp`'s structural order.
    fn lt(&self, a: T, b: T) -> bool {
        self.ast_cmp(a, b) == Ordering::Less
    }

    fn ast_cmp(&self, a: T, b: T) -> Ordering {
        let (mut a, mut b) = (a, b);
        loop {
            if a == b {
                return Ordering::Equal;
            }
            let (na, nb) = (&self.nodes[a], &self.nodes[b]);
            if na.args.len() != nb.args.len() {
                return na.args.len().cmp(&nb.args.len());
            }
            if na.depth != nb.depth {
                return na.depth.cmp(&nb.depth);
            }
            let d = self.decl_cmp(a, b);
            if d != Ordering::Equal {
                return d;
            }
            let i = (0..na.args.len()).find(|&i| na.args[i] != nb.args[i]);
            match i {
                Some(i) => {
                    a = na.args[i];
                    b = nb.args[i];
                }
                None => return Ordering::Equal,
            }
        }
    }

    /// `ast_lt` on the declarations of two applications with the same number
    /// of arguments: name, parameters, domain, range.
    fn decl_cmp(&self, a: T, b: T) -> Ordering {
        let (na, nb) = (&self.nodes[a], &self.nodes[b]);
        let o = na
            .op
            .name(&na.sort)
            .as_bytes()
            .cmp(nb.op.name(&nb.sort).as_bytes());
        if o != Ordering::Equal {
            return o;
        }
        let (pa, pb) = (na.op.params(&na.sort), nb.op.params(&nb.sort));
        if pa.len() != pb.len() {
            return pa.len().cmp(&pb.len());
        }
        for (x, y) in pa.iter().zip(&pb) {
            if x != y {
                return x.cmp(y);
            }
        }
        for (&x, &y) in na.args.iter().zip(&nb.args) {
            let o = sort_cmp(&self.nodes[x].sort, &self.nodes[y].sort);
            if o != Ordering::Equal {
                return o;
            }
        }
        sort_cmp(&na.sort, &nb.sort)
    }

    /// z3's `ast_lt` functor (by expression id), approximated by creation
    /// order.
    fn id_lt(a: T, b: T) -> bool {
        a < b
    }

    // ---- the rewriter driver (rewriter_def.h) --------------------------------

    /// Simplify `root` as z3's `simplify` command does.
    pub fn simplify(&mut self, root: T) -> T {
        self.input.clear();
        self.input_rc.clear();
        self.cache.clear();
        self.pinned.clear();
        let mut stack = vec![root];
        while let Some(t) = stack.pop() {
            if !self.input.insert(t) {
                continue;
            }
            for &a in &self.nodes[t].args {
                *self.input_rc.entry(a).or_insert(0) += 1;
                stack.push(a);
            }
        }
        self.rw(root, FULL)
    }

    /// Is `t` an expression with reference count one: a new term, or an
    /// input subterm with a single parent?
    fn fresh(&self, t: T) -> bool {
        !self.input.contains(&t) && !self.pinned.contains(&t) && self.parents[t] == 0
    }

    /// Does the rewriter flatten nested applications of this operator?
    fn flat_assoc(op: &Op) -> bool {
        matches!(
            op,
            Op::And | Op::Or | Op::Add | Op::Bv(BvOp::Add | BvOp::Or | BvOp::And | BvOp::Xor)
        )
    }

    /// Rewrite `t` to depth `depth` (`FULL` = unbounded).
    fn rw(&mut self, t: T, depth: u32) -> T {
        if depth == 0 || self.nodes[t].args.is_empty() {
            return t;
        }
        if depth == FULL
            && let Some(&r) = self.cache.get(&t)
        {
            return r;
        }
        let child_depth = if depth == FULL { FULL } else { depth - 1 };
        let op = self.nodes[t].op.clone();
        // `constant_fold`: an `ite` whose condition rewrites to a constant is
        // its branch (rewritten at the frame's depth).
        let mut args = Vec::with_capacity(self.nodes[t].args.len());
        if op == Op::Ite {
            let c = self.rw(self.arg(t, 0), child_depth);
            if self.is_true(c) || self.is_false(c) {
                let b = if self.is_true(c) {
                    self.arg(t, 1)
                } else {
                    self.arg(t, 2)
                };
                let r = self.rw(b, child_depth);
                if depth == FULL {
                    self.cache.insert(t, r);
                }
                return r;
            }
            args.push(c);
            for i in 1..3 {
                let a = self.arg(t, i);
                args.push(self.rw(a, child_depth));
            }
        } else {
            self.rw_args(t, &op, child_depth, &mut args);
        }
        let r = self.reduce(&op, &args, t);
        if depth == FULL {
            self.cache.insert(t, r);
        }
        if self.input_rc.get(&t).copied().unwrap_or(0) > 1 {
            self.pinned.insert(r);
        }
        r
    }

    /// The rewritten arguments of `t`, splicing in the arguments of an
    /// unshared nested application of the same associative operator (the
    /// rewriter's AC flattening).
    fn rw_args(&mut self, t: T, op: &Op, child_depth: u32, out: &mut Vec<T>) {
        let kids = self.nodes[t].args.clone();
        for c in kids {
            if child_depth == FULL
                && self.input.contains(&t)
                && Self::flat_assoc(op)
                && self.nodes[c].op == *op
                && self.nodes[c].sort == self.nodes[t].sort
                && !self.nodes[c].args.is_empty()
                && self.input_rc.get(&c).copied().unwrap_or(1) <= 1
                && self.input.contains(&c)
            {
                self.rw_args(c, op, child_depth, out);
            } else {
                out.push(self.rw(c, child_depth));
            }
        }
    }

    /// `reduce_app`: apply the theory rules to `op(args)`, rewriting the
    /// result further as the rule asks.
    fn reduce(&mut self, op: &Op, args: &[T], orig: T) -> T {
        match self.reduce_app(op, args) {
            None => {
                let s = self.nodes[orig].sort.clone();
                self.mk_sorted(op.clone(), args.to_vec(), s)
            }
            Some(St::Done(r)) => r,
            Some(St::Rw(r, d)) => self.rw_result(r, d),
        }
    }

    /// Rewrite a rule's result `r` to depth `d`.
    fn rw_result(&mut self, r: T, d: u32) -> T {
        // The rule's result is held twice (`m_r` and the result stack) when
        // visited, so the rewriter caches its rewritten form.
        self.pinned.insert(r);
        let x = self.rw(r, d);
        self.pinned.insert(x);
        x
    }

    /// `th_rewriter_cfg::reduce_app_core`.
    fn reduce_app(&mut self, op: &Op, args: &[T]) -> Option<St> {
        match op {
            Op::Eq => {
                if let Some(st) = self.reduce_eq(args[0], args[1]) {
                    return Some(st);
                }
                self.bool_eq(args[0], args[1])
            }
            Op::Distinct => self.bool_distinct(args),
            Op::And => self.bool_and(args),
            Op::Or => self.bool_or(args),
            Op::Not => self.bool_not(args[0]),
            Op::Ite => self.bool_ite(args[0], args[1], args[2]),
            Op::Implies => {
                let n = self.mk_not_rw(args[0]);
                Some(St::Done(self.mk_or_rw(&[n, args[1]])))
            }
            Op::Xor => match args.len() {
                0 => Some(St::Done(self.mk_false())),
                1 => Some(St::Done(args[0])),
                _ => {
                    let n = self.mk_not_rw(args[0]);
                    Some(St::Done(self.mk_eq_rw(n, args[1])))
                }
            },
            Op::True | Op::False => None,
            _ if self.arith_op(op) => self.arith_app(op, args),
            _ => None,
        }
    }

    fn arith_op(&self, op: &Op) -> bool {
        matches!(
            op,
            Op::Add
                | Op::Sub
                | Op::Uminus
                | Op::Mul
                | Op::Div
                | Op::Idiv
                | Op::Mod
                | Op::Rem
                | Op::Le
                | Op::Ge
                | Op::Lt
                | Op::Gt
                | Op::ToReal
                | Op::ToInt
                | Op::IsInt
                | Op::Abs
        )
    }

    /// `th_rewriter_cfg::reduce_eq`: the equality rules of the arguments'
    /// theory.
    fn reduce_eq(&mut self, a: T, b: T) -> Option<St> {
        if self.nodes[a].sort.is_arith_sort() {
            return self.arith_eq(a, b);
        }
        None
    }

    // ---- bool_rewriter -------------------------------------------------------

    /// `bool_rewriter::mk_not`.
    fn mk_not_rw(&mut self, t: T) -> T {
        match self.bool_not(t) {
            Some(St::Done(r)) => r,
            Some(St::Rw(r, d)) => self.rw(r, d),
            None => self.mk_not(t),
        }
    }

    /// `bool_rewriter::mk_or`.
    fn mk_or_rw(&mut self, args: &[T]) -> T {
        match self.bool_or(args) {
            Some(St::Done(r)) => r,
            Some(St::Rw(r, d)) => self.rw(r, d),
            None => self.mk(Op::Or, args.to_vec()),
        }
    }

    /// `bool_rewriter::mk_and`.
    fn mk_and_rw(&mut self, args: &[T]) -> T {
        match self.bool_and(args) {
            Some(St::Done(r)) => r,
            // `mk_and` takes the core's result as is.
            Some(St::Rw(r, _)) => r,
            None => self.mk(Op::And, args.to_vec()),
        }
    }

    /// `bool_rewriter::mk_eq` (the Boolean rules only).
    fn mk_eq_rw(&mut self, a: T, b: T) -> T {
        match self.bool_eq(a, b) {
            Some(St::Done(r)) => r,
            Some(St::Rw(r, _)) => r,
            None => self.mk_eq_plain(a, b),
        }
    }

    /// `bool_rewriter::mk_eq_plain`.
    fn mk_eq_plain(&mut self, a: T, b: T) -> T {
        if a == b {
            return self.mk_true();
        }
        if self.are_distinct(a, b) {
            return self.mk_false();
        }
        self.mk_eq(a, b)
    }

    fn bool_not(&mut self, t: T) -> Option<St> {
        if let Some(a) = self.is_not(t) {
            return Some(St::Done(a));
        }
        if self.is_true(t) {
            return Some(St::Done(self.mk_false()));
        }
        if self.is_false(t) {
            return Some(St::Done(self.mk_true()));
        }
        if self.is_op(t, &Op::Eq) && self.is_bool(self.arg(t, 0)) {
            let (l, r) = (self.arg(t, 0), self.arg(t, 1));
            let nl = self.mk_not_rw(l);
            return Some(St::Done(self.mk_eq_rw(nl, r)));
        }
        None
    }

    /// `mk_flat_and_core` (with `mk_nflat_and_core`).
    fn bool_and(&mut self, args: &[T]) -> Option<St> {
        if args.iter().any(|&a| self.is_op(a, &Op::And)) {
            let mut flat = Vec::new();
            for &a in args {
                if self.is_op(a, &Op::And) {
                    flat.extend_from_slice(&self.nodes[a].args.clone());
                } else {
                    flat.push(a);
                }
            }
            let r = match self.nflat_and(&flat) {
                Some(r) => r,
                None => self.mk(Op::And, flat),
            };
            return Some(St::Rw(r, 1));
        }
        self.nflat_and(args).map(St::Done)
    }

    fn nflat_and(&mut self, args: &[T]) -> Option<T> {
        let mut s = false;
        let mut buf = Vec::new();
        let mut pos = BTreeSet::new();
        let mut neg = BTreeSet::new();
        for &a in args {
            if self.is_true(a) {
                s = true;
                continue;
            }
            if self.is_false(a) {
                return Some(self.mk_false());
            }
            if let Some(atom) = self.is_not(a) {
                if neg.contains(&atom) {
                    s = true;
                    continue;
                }
                if pos.contains(&atom) {
                    return Some(self.mk_false());
                }
                neg.insert(atom);
            } else {
                if pos.contains(&a) {
                    s = true;
                    continue;
                }
                if neg.contains(&a) {
                    return Some(self.mk_false());
                }
                pos.insert(a);
            }
            buf.push(a);
        }
        match buf.len() {
            0 => Some(self.mk_true()),
            1 => Some(buf[0]),
            _ if s => Some(self.mk(Op::And, buf)),
            _ => None,
        }
    }

    /// `mk_flat_or_core` (with `mk_nflat_or_core`).
    fn bool_or(&mut self, args: &[T]) -> Option<St> {
        if args.iter().any(|&a| self.is_op(a, &Op::Or)) {
            let mut flat = Vec::new();
            let mut ordered = true;
            let mut prev: Option<T> = None;
            for &a in args {
                if self.is_op(a, &Op::Or) {
                    ordered = false;
                    flat.extend_from_slice(&self.nodes[a].args.clone());
                } else {
                    flat.push(a);
                    ordered &= prev.is_none_or(|p| !self.lt(a, p));
                    prev = Some(a);
                }
            }
            let r = match self.nflat_or(&flat) {
                Some(r) => r,
                None => {
                    if !ordered {
                        flat.sort_by(|&x, &y| {
                            if Self::id_lt(x, y) {
                                Ordering::Less
                            } else if Self::id_lt(y, x) {
                                Ordering::Greater
                            } else {
                                Ordering::Equal
                            }
                        });
                    }
                    match flat.len() {
                        0 => self.mk_false(),
                        1 => flat[0],
                        _ => self.mk(Op::Or, flat),
                    }
                }
            };
            return Some(St::Done(r));
        }
        self.nflat_or(args).map(St::Done)
    }

    fn nflat_or(&mut self, args: &[T]) -> Option<T> {
        let mut s = false;
        let mut buf: Vec<T> = Vec::new();
        let mut pos = BTreeSet::new();
        let mut neg = BTreeSet::new();
        let mut prev: Option<T> = None;
        for &a in args {
            if self.is_true(a) {
                return Some(self.mk_true());
            }
            if self.is_false(a) {
                s = true;
                continue;
            }
            if let Some(atom) = self.is_not(a) {
                if neg.contains(&atom) {
                    s = true;
                    continue;
                }
                if pos.contains(&atom) {
                    return Some(self.mk_true());
                }
                neg.insert(atom);
            } else {
                if pos.contains(&a) {
                    s = true;
                    continue;
                }
                if neg.contains(&a) {
                    return Some(self.mk_true());
                }
                pos.insert(a);
            }
            buf.push(a);
            s |= prev.is_some_and(|p| self.lt(a, p));
            prev = Some(a);
        }
        match buf.len() {
            0 => Some(self.mk_false()),
            1 => Some(buf[0]),
            _ if s => {
                buf.sort_by_key(|&x| x);
                Some(self.mk(Op::Or, buf))
            }
            _ => None,
        }
    }

    /// `bool_rewriter::mk_eq_core`.
    fn bool_eq(&mut self, lhs: T, rhs: T) -> Option<St> {
        let (mut lhs, mut rhs) = (lhs, rhs);
        if lhs == rhs {
            return Some(St::Done(self.mk_true()));
        }
        if self.are_distinct(lhs, rhs) {
            return Some(St::Done(self.mk_false()));
        }
        if let Some(r) = self.try_ite_eq(lhs, rhs) {
            return Some(St::Rw(r, 1));
        }
        if let Some(r) = self.try_ite_eq(rhs, lhs) {
            return Some(St::Rw(r, 1));
        }
        // ite_extra_rules
        let mut r = None;
        if self.is_ite(lhs).is_some() && self.is_value(rhs) {
            r = self.try_ite_value(lhs, rhs);
        } else if self.is_ite(rhs).is_some() && self.is_value(lhs) {
            r = self.try_ite_value(rhs, lhs);
        } else if let (Some((c1, t1, e1)), Some((c2, t2, e2))) =
            (self.is_ite(lhs), self.is_ite(rhs))
            && self.is_value(t1)
            && self.is_value(e1)
            && self.is_value(t2)
            && self.is_value(e2)
        {
            let eq_e = self.mk_eq(e1, e2);
            let a1 = self.mk(Op::Or, vec![c1, c2, eq_e]);
            let nc1 = self.mk_not(c1);
            let nc2 = self.mk_not(c2);
            let eq_t = self.mk_eq(t1, t2);
            let a2 = self.mk(Op::Or, vec![nc1, nc2, eq_t]);
            let eq_te = self.mk_eq(t1, e2);
            let a3 = self.mk(Op::Or, vec![nc1, c2, eq_te]);
            let eq_et = self.mk_eq(e1, t2);
            let a4 = self.mk(Op::Or, vec![c1, nc2, eq_et]);
            return Some(St::Rw(self.mk(Op::And, vec![a1, a2, a3, a4]), FULL));
        }
        if r.is_some() {
            return r;
        }
        if self.is_bool(lhs) {
            let mut unfolded = false;
            if let (Some(l), Some(r)) = (self.is_not(lhs), self.is_not(rhs)) {
                lhs = l;
                rhs = r;
                unfolded = true;
            }
            if self.is_true(lhs) {
                return Some(St::Done(rhs));
            }
            if self.is_false(lhs) {
                return Some(St::Done(self.mk_not_rw(rhs)));
            }
            if self.is_true(rhs) {
                return Some(St::Done(lhs));
            }
            if self.is_false(rhs) {
                return Some(St::Done(self.mk_not_rw(lhs)));
            }
            if self.is_complement(lhs, rhs) {
                return Some(St::Done(self.mk_false()));
            }
            if self.is_not(rhs).is_some() {
                core::mem::swap(&mut lhs, &mut rhs);
            }
            if let Some(l) = self.is_not(lhs) {
                let e = self.mk_eq(l, rhs);
                return Some(St::Rw(self.mk_not(e), 2));
            }
            if unfolded {
                return Some(St::Rw(self.mk_eq(lhs, rhs), 1));
            }
            if self.is_op(lhs, &Op::Eq) && self.is_op(rhs, &Op::Eq) {
                let (la, lb) = (self.arg(lhs, 0), self.arg(lhs, 1));
                let (ra, rb) = (self.arg(rhs, 0), self.arg(rhs, 1));
                let neg_of = |s: &Self, x: T, y: T| s.is_not(x) == Some(y);
                if (la == ra && (neg_of(self, rb, lb) || neg_of(self, lb, rb)))
                    || (lb == rb && (neg_of(self, ra, la) || neg_of(self, la, ra)))
                {
                    return Some(St::Done(self.mk_false()));
                }
            }
        }
        None
    }

    /// `m.is_complement`: `a = not b` or `b = not a`, or `true`/`false`.
    fn is_complement(&self, a: T, b: T) -> bool {
        self.is_not(a) == Some(b)
            || self.is_not(b) == Some(a)
            || (self.is_true(a) && self.is_false(b))
            || (self.is_false(a) && self.is_true(b))
    }

    fn try_ite_eq(&mut self, lhs: T, rhs: T) -> Option<T> {
        let (c, t, e) = self.is_ite(lhs)?;
        if t == rhs && self.are_distinct(e, rhs) {
            return Some(c);
        }
        if e == rhs && self.are_distinct(t, rhs) {
            return Some(self.mk_not(c));
        }
        None
    }

    /// `bool_rewriter::try_ite_value`.
    fn try_ite_value(&mut self, ite: T, val: T) -> Option<St> {
        let (cond, t, e) = self.is_ite(ite)?;
        if self.are_distinct(val, e) {
            let r = self.mk_eq_rw(t, val);
            return Some(St::Rw(self.mk_and2(r, cond), 2));
        }
        if self.are_distinct(val, t) {
            let r = self.mk_eq_rw(e, val);
            let nc = self.mk_not(cond);
            return Some(St::Rw(self.mk_and2(r, nc), 2));
        }
        if val == t {
            if val == e {
                return Some(St::Done(self.mk_true()));
            }
            let r = self.mk_eq_rw(e, val);
            return Some(St::Rw(self.mk_or2(r, cond), 2));
        }
        if val == e {
            let r = self.mk_eq_rw(t, val);
            let nc = self.mk_not(cond);
            return Some(St::Rw(self.mk_or2(r, nc), 2));
        }
        if let Some((_, t2, e2)) = self.is_ite(t)
            && self.is_value(t2)
            && self.is_value(e2)
            && let Some(st) = self.try_ite_value(t, val)
        {
            let inner = match st {
                St::Done(r) | St::Rw(r, _) => r,
            };
            let pe = self.mk_eq_plain(e, val);
            return Some(St::Rw(self.mk_ite(cond, inner, pe), 2));
        }
        if let Some((_, t2, e2)) = self.is_ite(e)
            && self.is_value(t2)
            && self.is_value(e2)
            && let Some(st) = self.try_ite_value(e, val)
        {
            let inner = match st {
                St::Done(r) | St::Rw(r, _) => r,
            };
            let pt = self.mk_eq_plain(t, val);
            return Some(St::Rw(self.mk_ite(cond, pt, inner), 2));
        }
        if self.ite_leaves_disjoint(val, ite) {
            return Some(St::Rw(self.mk_false(), FULL));
        }
        None
    }

    /// `simplify_eq_ite`: every leaf of the `ite` tree is a value other than
    /// `value`.
    fn ite_leaves_disjoint(&self, value: T, ite: T) -> bool {
        let mut seen = BTreeSet::new();
        let mut todo = vec![ite];
        while let Some(a) = todo.pop() {
            if !seen.insert(a) {
                continue;
            }
            if self.is_value(a) && self.are_distinct(a, value) {
                continue;
            }
            if let Some((_, t, e)) = self.is_ite(a) {
                todo.push(t);
                todo.push(e);
                continue;
            }
            return false;
        }
        true
    }

    /// `bool_rewriter::mk_distinct_core`.
    fn bool_distinct(&mut self, args: &[T]) -> Option<St> {
        if args.len() <= 1 {
            return Some(St::Done(self.mk_true()));
        }
        if args.len() == 2 {
            let e = self.mk_eq_rw(args[0], args[1]);
            let r = self.mk_not_rw(e);
            return Some(St::Rw(r, 2));
        }
        let mut seen = BTreeSet::new();
        let mut all_value = true;
        let mut all_diff = true;
        for (i, &a) in args.iter().enumerate() {
            if !seen.insert(a) {
                return Some(St::Done(self.mk_false()));
            }
            if !self.is_value(a) {
                all_value = false;
            }
            if !all_value && all_diff {
                for &b in &args[..i] {
                    all_diff = self.are_distinct(a, b);
                    if !all_diff {
                        if a == b {
                            return Some(St::Done(self.mk_false()));
                        }
                        break;
                    }
                }
            }
        }
        if all_diff {
            return Some(St::Done(self.mk_true()));
        }
        if self.is_bool(args[0]) {
            return Some(St::Done(self.mk_false()));
        }
        None
    }

    /// `bool_rewriter::mk_ite_core`.
    fn bool_ite(&mut self, c: T, t: T, e: T) -> Option<St> {
        let (mut c, mut t, mut e) = (c, t, e);
        let mut s = false;
        if let Some(a) = self.is_not(c) {
            c = a;
            core::mem::swap(&mut t, &mut e);
            s = true;
        }
        if let Some((tc, tt, _)) = self.is_ite(t)
            && tc == c
        {
            t = tt;
            s = true;
        }
        if let Some((ec, et, ee)) = self.is_ite(e)
            && et == t
        {
            let o = self.mk_or2(c, ec);
            return Some(St::Rw(self.mk_ite(o, t, ee), 3));
        }
        if let Some((ec, _, ee)) = self.is_ite(e)
            && ec == c
        {
            e = ee;
            s = true;
        }
        if self.is_true(c) {
            return Some(St::Done(t));
        }
        if self.is_false(c) {
            return Some(St::Done(e));
        }
        if t == e {
            return Some(St::Done(t));
        }
        if self.is_bool(t) {
            if self.is_true(t) {
                if self.is_false(e) {
                    return Some(St::Done(c));
                }
                return Some(St::Done(self.mk_or_rw(&[c, e])));
            }
            if self.is_false(t) {
                if self.is_true(e) {
                    return Some(St::Done(self.mk_not_rw(c)));
                }
                let nc = self.mk_not_rw(c);
                return Some(St::Rw(self.mk_and_rw(&[nc, e]), 1));
            }
            if self.is_true(e) {
                let nc = self.mk_not_rw(c);
                return Some(St::Done(self.mk_or_rw(&[nc, t])));
            }
            if self.is_false(e) {
                return Some(St::Rw(self.mk_and_rw(&[c, t]), 1));
            }
            if c == e {
                return Some(St::Rw(self.mk_and_rw(&[c, t]), 1));
            }
            if c == t {
                return Some(St::Done(self.mk_or_rw(&[c, e])));
            }
            if self.is_not(t) == Some(e) || self.is_not(e) == Some(t) {
                return Some(St::Done(self.mk_eq_rw(c, t)));
            }
        }
        if let Some((tc, tt, te)) = self.is_ite(t) {
            if e == tt {
                let nc2 = self.mk_not_rw(tc);
                let nc = self.mk_and_rw(&[c, nc2]);
                return Some(St::Rw(self.mk_ite(nc, te, e), 2));
            }
            if e == te {
                let nc = self.mk_and_rw(&[c, tc]);
                return Some(St::Rw(self.mk_ite(nc, tt, e), 2));
            }
            if let Some((ec, et, ee)) = self.is_ite(e) {
                if tt == et && te == ee {
                    let a1 = self.mk_and_rw(&[c, tc]);
                    let notc = self.mk_not_rw(c);
                    let a2 = self.mk_and_rw(&[notc, ec]);
                    let nc = self.mk_or_rw(&[a1, a2]);
                    return Some(St::Rw(self.mk_ite(nc, tt, te), 3));
                }
                if tt == ee && te == et {
                    let a1 = self.mk_and_rw(&[c, tc]);
                    let notc = self.mk_not_rw(c);
                    let notc3 = self.mk_not_rw(ec);
                    let a2 = self.mk_and_rw(&[notc, notc3]);
                    let nc = self.mk_or_rw(&[a1, a2]);
                    return Some(St::Rw(self.mk_ite(nc, tt, te), 3));
                }
            }
        }
        if let Some((ec, et, ee)) = self.is_ite(e) {
            if t == et {
                let nc = self.mk_or_rw(&[c, ec]);
                return Some(St::Rw(self.mk_ite(nc, t, ee), 1));
            }
            if t == ee {
                let nc2 = self.mk_not_rw(ec);
                let nc = self.mk_or_rw(&[c, nc2]);
                return Some(St::Rw(self.mk_ite(nc, t, et), 1));
            }
        }
        if s {
            return Some(St::Done(self.mk_ite(c, t, e)));
        }
        None
    }

    // ---- poly_rewriter (arithmetic configuration) ------------------------------

    /// A numeral of the arithmetic or bit-vector sort `s`.
    fn p_num(&mut self, c: &Rational, s: &Sort) -> T {
        match s {
            Sort::Bv(w) => {
                let v = c.numerator().clone();
                self.mk_bv_num(&v, *w)
            }
            _ => self.mk_num(c.clone(), *s == Sort::Int),
        }
    }

    /// `is_numeral` of the polynomial family of `s`.
    fn p_is_num(&self, t: T) -> Option<Rational> {
        match &self.nodes[t].op {
            Op::Num(r) => Some(r.clone()),
            Op::BvNum(v) => Some(Rational::from_integer(v.clone())),
            _ => None,
        }
    }

    fn p_normalize(c: &Rational, s: &Sort) -> Rational {
        match s {
            Sort::Bv(w) => Rational::from_integer(c.numerator().mod_2k(u64::from(*w))),
            _ => c.clone(),
        }
    }

    fn add_op(s: &Sort) -> Op {
        if matches!(s, Sort::Bv(_)) {
            Op::Bv(BvOp::Add)
        } else {
            Op::Add
        }
    }

    fn mul_op(s: &Sort) -> Op {
        if matches!(s, Sort::Bv(_)) {
            Op::Bv(BvOp::Mul)
        } else {
            Op::Mul
        }
    }

    fn is_add(&self, t: T) -> bool {
        matches!(self.nodes[t].op, Op::Add | Op::Bv(BvOp::Add))
    }

    fn is_mul(&self, t: T) -> bool {
        matches!(self.nodes[t].op, Op::Mul | Op::Bv(BvOp::Mul))
    }

    /// Is `t` an application of the polynomial family of sort `s`?
    fn p_family(&self, t: T, s: &Sort) -> bool {
        if matches!(s, Sort::Bv(_)) {
            self.is_bv_app(t)
        } else {
            self.is_arith_app(t)
        }
    }

    fn mk_add_app(&mut self, args: &[T], s: &Sort) -> T {
        match args.len() {
            0 => self.p_num(&rat(0), s),
            1 => args[0],
            _ => self.mk_sorted(Self::add_op(s), args.to_vec(), s.clone()),
        }
    }

    fn mk_mul_app(&mut self, args: &[T], s: &Sort) -> T {
        match args.len() {
            0 => self.p_num(&rat(1), s),
            1 => args[0],
            _ => {
                if args.len() > 2
                    && let Some(a) = self.p_is_num(args[0])
                {
                    let rest = self.mk_mul_app(&args[1..], s);
                    return self.mk_mul_app_c(&a, rest, s);
                }
                self.mk_sorted(Self::mul_op(s), args.to_vec(), s.clone())
            }
        }
    }

    fn mk_mul_app_c(&mut self, c: &Rational, arg: T, s: &Sort) -> T {
        if c.is_one() {
            return arg;
        }
        if self.p_is_num(arg).is_some_and(|v| v.is_zero()) {
            return arg;
        }
        let n = self.p_num(c, s);
        self.mk_mul_app(&[n, arg], s)
    }

    /// `mk_flat_mul_core`.
    fn flat_mul(&mut self, args: &[T], s: &Sort) -> Option<St> {
        let already_flat = args.len() == 2
            && self.p_is_num(args[0]).is_some()
            && !(self.is_mul(args[1]) && self.p_is_num(self.arg(args[1], 0)).is_some());
        if !already_flat && let Some(i) = args.iter().position(|&a| self.is_mul(a)) {
            let mut flat: Vec<T> = args[..i].to_vec();
            for &a in &args[i..] {
                if self.is_mul(a) {
                    let mut todo = vec![a];
                    while let Some(cur) = todo.pop() {
                        if self.is_mul(cur) {
                            for &k in self.nodes[cur].args.iter().rev() {
                                todo.push(k);
                            }
                        } else {
                            flat.push(cur);
                        }
                    }
                } else {
                    flat.push(a);
                }
            }
            return match self.nflat_mul(&flat, s) {
                None => Some(St::Done(self.mk_mul_app(&flat, s))),
                st => st,
            };
        }
        self.nflat_mul(args, s)
    }

    /// `mk_nflat_mul_core` (without `som`).
    fn nflat_mul(&mut self, args: &[T], s: &Sort) -> Option<St> {
        if args.len() == 2
            && let Some(a) = self.p_is_num(args[0])
            && !a.is_one()
            && !a.is_zero()
            && !self.p_family(args[1], s)
        {
            return None;
        }
        let mut c = rat(1);
        let mut num_coeffs = 0;
        let mut num_add = 0;
        let mut var = None;
        for &a in args {
            if let Some(v) = self.p_is_num(a) {
                num_coeffs += 1;
                c = &c * &v;
            } else {
                var = Some(a);
                if self.is_add(a) {
                    num_add += 1;
                }
            }
        }
        c = Self::p_normalize(&c, s);
        if num_coeffs == args.len() || c.is_zero() {
            return Some(St::Done(self.p_num(&c, s)));
        }
        if num_coeffs == args.len() - 1 {
            let var = var.unwrap();
            if c.is_one() {
                return Some(St::Done(var));
            }
            if self.is_mul(var) {
                if self.nodes[var].args.len() == 2
                    && let Some(c2) = self.p_is_num(self.arg(var, 0))
                {
                    let c = Self::p_normalize(&(&c * &c2), s);
                    let x = self.arg(var, 1);
                    return Some(St::Rw(self.mk_mul_app_c(&c, x, s), 1));
                }
                return None;
            }
            if num_add == 0 {
                if args.len() == 2 && args[1] == var {
                    return None;
                }
                return Some(St::Done(self.mk_mul_app_c(&c, var, s)));
            }
            let kids = self.nodes[var].args.clone();
            let terms: Vec<T> = kids.iter().map(|&k| self.mk_mul_app_c(&c, k, s)).collect();
            return Some(St::Rw(self.mk_add_app(&terms, s), 2));
        }
        if num_coeffs > 1 || (num_coeffs == 1 && self.p_is_num(args[0]).is_none()) {
            let rest: Vec<T> = args
                .iter()
                .copied()
                .filter(|&a| self.p_is_num(a).is_none())
                .collect();
            let m = self.mk_mul_app(&rest, s);
            return Some(St::Rw(self.mk_mul_app_c(&c, m, s), 2));
        }
        let mut new_args = Vec::new();
        let mut prev: Option<T> = None;
        let mut ordered = true;
        for &a in args {
            if self.p_is_num(a).is_some() {
                continue;
            }
            if let Some(p) = prev
                && self.lt(a, p)
            {
                ordered = false;
            }
            new_args.push(a);
            prev = Some(a);
        }
        if ordered && num_coeffs == 0 {
            return None;
        }
        if !ordered {
            new_args.sort_by(|&x, &y| self.ast_cmp(x, y));
        }
        let m = self.mk_mul_app(&new_args, s);
        Some(St::Done(self.mk_mul_app_c(&c, m, s)))
    }

    /// `mk_flat_add_core`.
    fn flat_add(&mut self, args: &[T], s: &Sort) -> Option<St> {
        if args.iter().any(|&a| self.is_add(a)) {
            let mut flat = Vec::new();
            for &a in args {
                if self.is_add(a) {
                    flat.extend_from_slice(&self.nodes[a].args.clone());
                } else {
                    flat.push(a);
                }
            }
            return match self.nflat_add(&flat, s) {
                None => Some(St::Done(self.mk_add_app(&flat, s))),
                st => st,
            };
        }
        self.nflat_add(args, s)
    }

    /// `get_power_product`: `t = c·pp` with numeral `c`.
    fn power_product(&self, t: T) -> (T, Rational) {
        if self.is_mul(t)
            && self.nodes[t].args.len() == 2
            && let Some(a) = self.p_is_num(self.arg(t, 0))
        {
            return (self.arg(t, 1), a);
        }
        (t, rat(1))
    }

    /// `mk_nflat_add_core`.
    fn nflat_add(&mut self, args: &[T], s: &Sort) -> Option<St> {
        let sort_sums = matches!(s, Sort::Bv(_));
        let mut c = rat(0);
        let mut num_coeffs = 0;
        let mut visited = BTreeSet::new();
        let mut multiple = BTreeSet::new();
        let mut prev: Option<T> = None;
        let mut ordered = true;
        for (i, &a) in args.iter().enumerate() {
            if let Some(v) = self.p_is_num(a) {
                num_coeffs += 1;
                c = &c + &v;
                ordered = !sort_sums || i == 0;
            } else if sort_sums && ordered {
                if let Some(p) = prev
                    && self.lt(a, p)
                {
                    ordered = false;
                }
                prev = Some(a);
            }
            let (pp, _) = self.power_product(a);
            if !visited.insert(pp) {
                multiple.insert(pp);
            }
        }
        c = Self::p_normalize(&c, s);
        if !multiple.is_empty() {
            let mut coeffs: Vec<Rational> = Vec::new();
            let mut pos: BTreeMap<T, usize> = BTreeMap::new();
            for &a in args {
                if self.p_is_num(a).is_some() {
                    continue;
                }
                let (pp, k) = self.power_product(a);
                if !multiple.contains(&pp) {
                    continue;
                }
                if let Some(&i) = pos.get(&pp) {
                    coeffs[i] = &coeffs[i] + &k;
                } else {
                    pos.insert(pp, coeffs.len());
                    coeffs.push(k);
                }
            }
            let mut new_args = Vec::new();
            if !c.is_zero() {
                new_args.push(self.p_num(&c, s));
            }
            let mut seen = BTreeSet::new();
            for &a in args {
                if self.p_is_num(a).is_some() {
                    continue;
                }
                let (pp, _) = self.power_product(a);
                if !multiple.contains(&pp) {
                    new_args.push(a);
                } else if seen.insert(pp) {
                    let k = Self::p_normalize(&coeffs[pos[&pp]], s);
                    if !k.is_zero() {
                        new_args.push(self.mk_mul_app_c(&k, pp, s));
                    }
                }
            }
            if sort_sums {
                let from = usize::from(!c.is_zero());
                new_args[from..].sort_by(|&x, &y| self.mon_cmp(x, y));
            }
            return Some(St::Done(self.mk_add_app(&new_args, s)));
        }
        if ordered {
            if num_coeffs == 0 {
                return None;
            }
            if num_coeffs == 1
                && let Some(a) = self.p_is_num(args[0])
                && !a.is_zero()
            {
                return None;
            }
        }
        let mut new_args = Vec::new();
        if !c.is_zero() {
            new_args.push(self.p_num(&c, s));
        }
        for &a in args {
            if self.p_is_num(a).is_none() {
                new_args.push(a);
            }
        }
        if !ordered {
            let from = usize::from(!c.is_zero());
            new_args[from..].sort_by(|&x, &y| self.mon_cmp(x, y));
        }
        Some(St::Done(self.mk_add_app(&new_args, s)))
    }

    /// `mon_lt` with `m_ast_order` (the default): `ast_lt`.
    fn mon_cmp(&self, a: T, b: T) -> Ordering {
        self.ast_cmp(a, b)
    }

    /// `poly_rewriter::mk_uminus`.
    fn p_uminus(&mut self, a: T, s: &Sort) -> St {
        if let Some(v) = self.p_is_num(a) {
            let v = Self::p_normalize(&-v, s);
            return St::Done(self.p_num(&v, s));
        }
        St::Rw(self.mk_mul_app_c(&rat(-1), a, s), 1)
    }

    /// `poly_rewriter::mk_sub`.
    fn p_sub(&mut self, args: &[T], s: &Sort) -> St {
        if args.len() == 1 {
            return St::Done(args[0]);
        }
        let m1 = Self::p_normalize(&rat(-1), s);
        let minus_one = self.p_num(&m1, s);
        let mut new_args = vec![args[0]];
        for &a in &args[1..] {
            if self.p_is_num(a).is_some_and(|v| v.is_zero()) {
                continue;
            }
            new_args.push(self.mk_mul_app(&[minus_one, a], s));
        }
        St::Rw(self.mk_add_app(&new_args, s), 2)
    }

    fn monomials(&self, t: T) -> Vec<T> {
        if self.is_add(t) {
            self.nodes[t].args.clone()
        } else {
            vec![t]
        }
    }

    /// `poly_rewriter::cancel_monomials` (with `move = false`).
    fn cancel_monomials(&mut self, lhs: T, rhs: T) -> Option<(T, T)> {
        let s = self.nodes[lhs].sort.clone();
        let lm = self.monomials(lhs);
        let rm = self.monomials(rhs);
        let mut c = rat(0);
        let mut num_coeffs = 0;
        let mut visited = BTreeSet::new();
        let mut multiple = BTreeSet::new();
        for &a in &lm {
            if let Some(v) = self.p_is_num(a) {
                c = &c + &v;
                num_coeffs += 1;
            } else {
                visited.insert(self.power_product(a).0);
            }
        }
        for &a in &rm {
            if let Some(v) = self.p_is_num(a) {
                c = &c - &v;
                num_coeffs += 1;
            } else {
                let pp = self.power_product(a).0;
                if visited.contains(&pp) {
                    multiple.insert(pp);
                }
            }
        }
        c = Self::p_normalize(&c, &s);
        if multiple.is_empty()
            && num_coeffs <= 1
            && (num_coeffs == 0 || self.p_is_num(rhs).is_some())
        {
            return None;
        }
        let mut coeffs: Vec<Rational> = Vec::new();
        let mut pos: BTreeMap<T, usize> = BTreeMap::new();
        for &a in &lm {
            if self.p_is_num(a).is_some() {
                continue;
            }
            let (pp, k) = self.power_product(a);
            if !multiple.contains(&pp) {
                continue;
            }
            if let Some(&i) = pos.get(&pp) {
                coeffs[i] = &coeffs[i] + &k;
            } else {
                pos.insert(pp, coeffs.len());
                coeffs.push(k);
            }
        }
        for &a in &rm {
            if self.p_is_num(a).is_some() {
                continue;
            }
            let (pp, k) = self.power_product(a);
            if !multiple.contains(&pp) {
                continue;
            }
            let i = pos[&pp];
            coeffs[i] = &coeffs[i] - &k;
        }
        let mut new_lhs: Vec<T> = Vec::new();
        let mut seen = BTreeSet::new();
        for &a in &lm {
            if self.p_is_num(a).is_some() {
                continue;
            }
            let (pp, _) = self.power_product(a);
            if !multiple.contains(&pp) {
                new_lhs.push(a);
            } else if seen.insert(pp) {
                let k = coeffs[pos[&pp]].clone();
                if !k.is_zero() {
                    new_lhs.push(self.mk_mul_app_c(&k, pp, &s));
                }
            }
        }
        let mut new_rhs: Vec<T> = Vec::new();
        for &a in &rm {
            if self.p_is_num(a).is_some() {
                continue;
            }
            let (pp, _) = self.power_product(a);
            if !multiple.contains(&pp) {
                new_rhs.push(a);
            }
        }
        let c_at_rhs = new_rhs.is_empty() || !new_lhs.is_empty();
        if c_at_rhs {
            c = Self::p_normalize(&-c, &s);
        }
        let insert_c_lhs = !c_at_rhs && (new_lhs.is_empty() || !c.is_zero());
        let insert_c_rhs = c_at_rhs && (new_rhs.is_empty() || !c.is_zero());
        if insert_c_lhs {
            let n = self.p_num(&c, &s);
            new_lhs.insert(0, n);
        }
        if insert_c_rhs {
            let n = self.p_num(&c, &s);
            new_rhs.insert(0, n);
        }
        let l = self.mk_add_app(&new_lhs, &s);
        let r = self.mk_add_app(&new_rhs, &s);
        Some((l, r))
    }

    // ---- arith_rewriter ----------------------------------------------------------

    fn arith_app(&mut self, op: &Op, args: &[T]) -> Option<St> {
        let s = self.nodes[args[0]].sort.clone();
        match op {
            Op::Le => self.le_ge_eq(args[0], args[1], Kind::Le),
            Op::Ge => self.le_ge_eq(args[0], args[1], Kind::Ge),
            Op::Lt => {
                let le = self.mk(Op::Le, vec![args[1], args[0]]);
                Some(St::Rw(self.mk_not(le), 2))
            }
            Op::Gt => {
                let le = self.mk(Op::Le, vec![args[0], args[1]]);
                Some(St::Rw(self.mk_not(le), 2))
            }
            Op::Add => {
                if args.len() == 1 {
                    return Some(St::Done(args[0]));
                }
                self.flat_add(args, &s)
            }
            Op::Mul => {
                if args.len() == 1 {
                    return Some(St::Done(args[0]));
                }
                self.flat_mul(args, &s)
            }
            Op::Sub => Some(self.p_sub(args, &s)),
            Op::Uminus => Some(self.p_uminus(args[0], &s)),
            Op::Div => {
                if args.len() == 1 {
                    return Some(St::Done(args[0]));
                }
                self.mk_div(args[0], args[1])
            }
            Op::Idiv => {
                if args.len() == 1 {
                    return Some(St::Done(args[0]));
                }
                self.mk_idiv(args[0], args[1])
            }
            Op::Mod => self.mk_mod(args[0], args[1]),
            Op::Rem => self.mk_rem(args[0], args[1]),
            Op::ToReal => self.mk_to_real(args[0]),
            Op::ToInt => self.mk_to_int(args[0]),
            Op::IsInt => self.mk_is_int(args[0]),
            Op::Abs => {
                let zero = self.p_num(&rat(0), &s);
                let ge = self.mk(Op::Ge, vec![args[0], zero]);
                let neg = self.mk(Op::Uminus, vec![args[0]]);
                Some(St::Rw(self.mk_ite(ge, args[0], neg), 2))
            }
            _ => None,
        }
    }

    fn is_zero(&self, t: T) -> bool {
        self.arith_num(t).is_some_and(|r| r.is_zero())
    }

    fn mk_cmp(&mut self, k: Kind, a: T, b: T) -> T {
        match k {
            Kind::Le => self.mk(Op::Le, vec![a, b]),
            Kind::Ge => self.mk(Op::Ge, vec![a, b]),
            Kind::Eq => self.mk_eq(a, b),
        }
    }

    /// `arith_rewriter::mk_le_ge_eq_core`.
    fn le_ge_eq(&mut self, arg1: T, arg2: T, kind: Kind) -> Option<St> {
        let (orig1, orig2) = (arg1, arg2);
        let (mut arg1, mut arg2) = (arg1, arg2);
        let mut changed = false;
        if let Some((l, r)) = self.cancel_monomials(arg1, arg2) {
            arg1 = l;
            arg2 = r;
            changed = true;
        }
        if let (Some(a1), Some(a2)) = (self.arith_num(arg1), self.arith_num(arg2)) {
            let b = match kind {
                Kind::Le => a1 <= a2,
                Kind::Ge => a1 >= a2,
                Kind::Eq => a1 == a2,
            };
            return Some(St::Done(self.mk_bool(b)));
        }
        if let Some(st) = self.is_separated(arg1, arg2, kind) {
            return Some(st);
        }
        if let Some(r) = self.is_bound(arg1, arg2, kind) {
            return Some(St::Done(r));
        }
        if let Some(r) = self.is_bound(arg2, arg1, inv(kind)) {
            return Some(St::Done(r));
        }
        if let Some((c, t, e)) = self.is_ite(arg1)
            && let Some(a2) = self.arith_num(arg2).cloned()
        {
            if let Some(a1) = self.arith_num(t).cloned() {
                let holds = match kind {
                    Kind::Le => a1 <= a2,
                    Kind::Ge => a1 >= a2,
                    Kind::Eq => a1 == a2,
                };
                let r = if holds {
                    let cmp = self.mk_cmp(kind, e, arg2);
                    self.mk_or2(c, cmp)
                } else {
                    let nc = self.mk_not(c);
                    let cmp = self.mk_cmp(kind, e, arg2);
                    self.mk_and2(nc, cmp)
                };
                return Some(St::Rw(r, 2));
            }
            if let Some(a1) = self.arith_num(e).cloned() {
                let holds = match kind {
                    Kind::Le => a1 <= a2,
                    Kind::Ge => a1 >= a2,
                    Kind::Eq => a1 == a2,
                };
                let r = if holds {
                    let nc = self.mk_not(c);
                    let cmp = self.mk_cmp(kind, t, arg2);
                    self.mk_or2(nc, cmp)
                } else {
                    let cmp = self.mk_cmp(kind, t, arg2);
                    self.mk_and2(c, cmp)
                };
                return Some(St::Rw(r, 2));
            }
        }
        if let Some((c, t, e)) = self.is_ite(arg1)
            && self.fresh(arg1)
        {
            let a = self.mk_cmp(kind, t, arg2);
            let b = self.mk_cmp(kind, e, arg2);
            return Some(St::Rw(self.mk_ite(c, a, b), 2));
        }
        let mut kind = kind;
        if self.is_op(arg2, &Op::ToInt) && self.arith_num(arg1).is_some() {
            kind = inv(kind);
            core::mem::swap(&mut arg1, &mut arg2);
        }
        if self.is_op(arg1, &Op::ToInt)
            && let Some(a2) = self.arith_num(arg2).cloned()
        {
            let t = self.arg(arg1, 0);
            let r = match kind {
                Kind::Le => {
                    let k = self.mk_num(&a2 + &rat(1), false);
                    self.mk(Op::Lt, vec![t, k])
                }
                Kind::Ge => {
                    let k = self.mk_num(a2, false);
                    self.mk(Op::Ge, vec![t, k])
                }
                Kind::Eq => {
                    let k = self.mk_num(a2.clone(), false);
                    let ge = self.mk(Op::Ge, vec![t, k]);
                    let k1 = self.mk_num(&a2 + &rat(1), false);
                    let lt = self.mk(Op::Lt, vec![t, k1]);
                    return Some(St::Rw(self.mk_and2(lt, ge), 3));
                }
            };
            return Some(St::Rw(r, 1));
        }
        if changed && arg1 == orig1 && arg2 == orig2 {
            return None;
        }
        if changed {
            return Some(St::Done(self.mk_cmp(kind, arg1, arg2)));
        }
        self.factor_le_ge_eq(arg1, arg2, kind)
    }

    /// `arith_rewriter::is_bound`.
    fn is_bound(&mut self, arg1: T, arg2: T, kind: Kind) -> Option<T> {
        let mut kind = kind;
        if !self.is_add(arg1)
            && !self.is_op(arg1, &Op::Mod)
            && let Some(c) = self.arith_num(arg2).cloned()
        {
            let mut c = c;
            let (pp, mut a) = self.power_product(arg1);
            let mut r = false;
            if a.is_negative() {
                a = -a;
                c = -c;
                kind = inv(kind);
                r = true;
            }
            if a.is_zero() {
                return None;
            }
            if !a.is_one() {
                r = true;
            }
            if !r {
                return None;
            }
            c = &c / &a;
            let is_int = self.nodes[arg1].sort == Sort::Int;
            if is_int && !c.is_integer() {
                match kind {
                    Kind::Le => c = Rational::from_integer(c.floor()),
                    Kind::Ge => c = Rational::from_integer(c.ceil()),
                    Kind::Eq => return Some(self.mk_false()),
                }
            }
            let k = self.mk_num(c, is_int);
            return Some(self.mk_cmp(kind, pp, k));
        }
        let (mut arg1, mut arg2) = (arg1, arg2);
        if self.is_op(arg2, &Op::Mod) {
            core::mem::swap(&mut arg1, &mut arg2);
            kind = inv(kind);
        }
        if let Some(c) = self.arith_num(arg2).cloned()
            && self.nodes[arg2].sort == Sort::Int
            && self.is_op(arg1, &Op::Mod)
            && let Some(b) = self.arith_num(self.arg(arg1, 1)).cloned()
            && !b.is_zero()
        {
            if c.is_negative() {
                return Some(match kind {
                    Kind::Eq | Kind::Le => self.mk_false(),
                    Kind::Ge => self.mk_true(),
                });
            }
            if c.is_zero() && kind == Kind::Ge {
                return Some(self.mk_true());
            }
            if !c.is_negative() && !c.is_zero() && c >= b.abs() {
                return Some(match kind {
                    Kind::Le => self.mk_true(),
                    Kind::Eq | Kind::Ge => self.mk_false(),
                });
            }
            if &c + &rat(1) == b.abs() && kind == Kind::Le {
                return Some(self.mk_true());
            }
        }
        None
    }

    /// `arith_rewriter::is_non_negative` (without powers and lengths).
    fn is_non_negative(&self, e: T) -> bool {
        if !self.is_op(e, &Op::Mul) {
            return false;
        }
        let args = self.flat_mul_args(e);
        let mut sign = false;
        let mut factors = Vec::new();
        for a in args {
            if let Some(r) = self.arith_num(a) {
                if r.is_negative() {
                    sign = !sign;
                }
                continue;
            }
            factors.push(a);
        }
        if sign {
            return false;
        }
        factors.sort();
        let mut odd = Vec::new();
        let mut i = 0;
        while i < factors.len() {
            let mut j = i;
            while j < factors.len() && factors[j] == factors[i] {
                j += 1;
            }
            if (j - i) % 2 == 1 {
                odd.push(factors[i]);
            }
            i = j;
        }
        if odd.is_empty() {
            return true;
        }
        if self.nodes[e].sort == Sort::Int && odd.len() == 2 {
            let is_succ = |a: T, b: T| {
                if !self.is_op(b, &Op::Add) {
                    return false;
                }
                let mut offset = rat(0);
                let mut num_a = 0;
                for &x in &self.nodes[b].args {
                    if let Some(c) = self.arith_num(x) {
                        offset = &offset + c;
                    } else if x == a {
                        num_a += 1;
                    } else {
                        return false;
                    }
                }
                num_a == 1 && (offset.is_one() || offset == rat(-1))
            };
            if is_succ(odd[0], odd[1]) || is_succ(odd[1], odd[0]) {
                return true;
            }
        }
        false
    }

    /// `arith_rewriter::flat_mul`: the factors of nested products (in z3's
    /// swap-with-last order).
    fn flat_mul_args(&self, e: T) -> Vec<T> {
        let mut args = vec![e];
        let mut i = 0;
        while i < args.len() {
            let x = args[i];
            if self.is_op(x, &Op::Mul) {
                args.extend_from_slice(&self.nodes[x].args);
                let last = args.pop().unwrap();
                args[i] = last;
                continue;
            }
            i += 1;
        }
        args
    }

    /// `arith_rewriter::is_separated`.
    fn is_separated(&mut self, arg1: T, arg2: T, kind: Kind) -> Option<St> {
        if kind == Kind::Eq {
            return None;
        }
        let r2 = self.arith_num(arg2)?.clone();
        if kind == Kind::Ge
            && r2.is_zero()
            && self.is_op(arg1, &Op::Mul)
            && self.is_non_negative(arg1)
        {
            return Some(St::Done(self.mk_true()));
        }
        let mut r1 = rat(0);
        let mut has_bound = true;
        let terms = if self.is_op(arg1, &Op::Add) {
            self.nodes[arg1].args.clone()
        } else {
            vec![arg1]
        };
        for &a in &terms {
            if let Some(v) = self.arith_num(a) {
                r1 = v.clone();
                continue;
            }
            if kind == Kind::Le && self.is_non_negative(a) {
                continue;
            }
            if kind == Kind::Ge
                && let Some(n) = self.is_neg_poly(a)
                && self.is_non_negative(n)
            {
                continue;
            }
            has_bound = false;
        }
        if !has_bound {
            return None;
        }
        if kind == Kind::Le && r1 < r2 {
            return None;
        }
        if kind == Kind::Ge && r1 > r2 {
            return None;
        }
        if kind == Kind::Le && r1 > r2 {
            return Some(St::Done(self.mk_false()));
        }
        if kind == Kind::Ge && r1 < r2 {
            return Some(St::Done(self.mk_false()));
        }
        let s = self.nodes[arg1].sort.clone();
        let zero = self.p_num(&rat(0), &s);
        if r1.is_zero() && self.is_op(arg1, &Op::Mul) {
            let mut eqs = Vec::new();
            for a in self.flat_mul_args(arg1) {
                if self.arith_num(a).is_some() {
                    continue;
                }
                eqs.push(self.mk_eq(a, zero));
            }
            let r = self.mk_or_app(eqs);
            return Some(St::Rw(r, 2));
        }
        if self.is_op(arg1, &Op::Add) {
            let mut cs = Vec::new();
            for &a in &self.nodes[arg1].args.clone() {
                if self.arith_num(a).is_none() {
                    let k = if kind == Kind::Le { Op::Le } else { Op::Ge };
                    cs.push(self.mk(k, vec![a, zero]));
                }
            }
            let r = self.mk_and_app(cs);
            return Some(St::Rw(r, 2));
        }
        None
    }

    /// `m.mk_or(args)`: `false`, the single argument, or the disjunction.
    fn mk_or_app(&mut self, args: Vec<T>) -> T {
        match args.len() {
            0 => self.mk_false(),
            1 => args[0],
            _ => self.mk(Op::Or, args),
        }
    }

    /// `m.mk_and(args)`: `true`, the single argument, or the conjunction.
    fn mk_and_app(&mut self, args: Vec<T>) -> T {
        match args.len() {
            0 => self.mk_true(),
            1 => args[0],
            _ => self.mk(Op::And, args),
        }
    }

    /// `arith_rewriter::neg_monomial`.
    fn neg_monomial(&mut self, e: T) -> T {
        let s = self.nodes[e].sort.clone();
        let mut args = Vec::new();
        if let Some(a) = self.arith_num(e).cloned() {
            args.push(self.p_num(&-a, &s));
        } else if self.is_op(e, &Op::Mul) {
            if let Some(a) = self.arith_num(self.arg(e, 0)).cloned() {
                if a != rat(-1) {
                    args.push(self.p_num(&-a, &s));
                }
                args.extend_from_slice(&self.nodes[e].args[1..]);
            } else {
                args.push(self.p_num(&rat(-1), &s));
                args.push(e);
            }
        } else {
            args.push(self.p_num(&rat(-1), &s));
            args.push(e);
        }
        if args.len() == 1 {
            args[0]
        } else {
            self.mk_sorted(Op::Mul, args, s)
        }
    }

    /// `arith_rewriter::is_neg_poly`.
    fn is_neg_poly(&mut self, t: T) -> Option<T> {
        let s = self.nodes[t].sort.clone();
        if self.is_op(t, &Op::Mul)
            && self
                .arith_num(self.arg(t, 0))
                .is_some_and(|r| r.is_negative())
        {
            return Some(self.neg_monomial(t));
        }
        if !self.is_op(t, &Op::Add) {
            return None;
        }
        let t2 = self.arg(t, 0);
        if self.is_op(t2, &Op::Mul)
            && self
                .arith_num(self.arg(t2, 0))
                .is_some_and(|r| r.is_negative())
        {
            let kids = self.nodes[t].args.clone();
            let ns: Vec<T> = kids.iter().map(|&k| self.neg_monomial(k)).collect();
            return Some(self.mk_sorted(Op::Add, ns, s));
        }
        None
    }

    fn is_mul_factor(&self, s: T, t: T) -> bool {
        if self.is_op(t, &Op::Mul) {
            return self.nodes[t].args.iter().any(|&m| self.is_mul_factor(s, m));
        }
        s == t
    }

    fn is_add_factor(&self, s: T, t: T) -> bool {
        if self.is_op(t, &Op::Add) {
            return self.nodes[t].args.iter().all(|&f| self.is_add_factor(s, f));
        }
        self.is_mul_factor(s, t)
    }

    /// `arith_rewriter::remove_factor`.
    fn remove_factor(&mut self, s: T, t: T) -> T {
        let srt = self.nodes[t].sort.clone();
        if self.is_op(t, &Op::Mul) {
            let mut r = vec![t];
            let mut i = 0;
            while i < r.len() {
                let arg = r[i];
                if self.is_op(arg, &Op::Mul) {
                    r.extend_from_slice(&self.nodes[arg].args.clone());
                    let last = r.pop().unwrap();
                    r[i] = last;
                    continue;
                }
                if s == arg {
                    let last = r.pop().unwrap();
                    if i < r.len() {
                        r[i] = last;
                    }
                    break;
                }
                i += 1;
            }
            return match r.len() {
                0 => self.p_num(&rat(1), &srt),
                1 => r[0],
                _ => self.mk_sorted(Op::Mul, r, srt),
            };
        }
        if self.is_op(t, &Op::Add) {
            let mut sum = vec![t];
            let mut i = 0;
            while i < sum.len() {
                let arg = sum[i];
                if self.is_op(arg, &Op::Add) {
                    sum.extend_from_slice(&self.nodes[arg].args.clone());
                    let last = sum.pop().unwrap();
                    sum[i] = last;
                    continue;
                }
                sum[i] = self.remove_factor(s, arg);
                i += 1;
            }
            return if sum.len() == 1 {
                sum[0]
            } else {
                self.mk_sorted(Op::Add, sum, srt)
            };
        }
        self.p_num(&rat(1), &srt)
    }

    /// `arith_rewriter::find_nl_factor`.
    fn find_nl_factor(&self, t: T) -> Option<T> {
        let mut sum = vec![t];
        let mut i = 0;
        while i < sum.len() {
            let arg = sum[i];
            i += 1;
            if self.is_op(arg, &Op::Add) {
                sum.extend_from_slice(&self.nodes[arg].args);
            } else if self.is_op(arg, &Op::Mul) {
                let mut muls = Vec::new();
                self.nl_muls(arg, &mut muls);
                if muls.len() <= 1 {
                    continue;
                }
                for &m in &muls {
                    if self.is_add_factor(m, t) {
                        return Some(m);
                    }
                }
                return None;
            }
        }
        None
    }

    fn nl_muls(&self, t: T, out: &mut Vec<T>) {
        if self.is_op(t, &Op::Mul) {
            for &a in &self.nodes[t].args {
                self.nl_muls(a, out);
            }
        } else if self.arith_num(t).is_none() {
            out.push(t);
        }
    }

    /// `arith_rewriter::factor_le_ge_eq`.
    fn factor_le_ge_eq(&mut self, arg1: T, arg2: T, kind: Kind) -> Option<St> {
        if !self.is_zero(arg2) {
            return None;
        }
        let f = self.find_nl_factor(arg1)?;
        let f2 = self.remove_factor(f, arg1);
        let s = self.nodes[arg1].sort.clone();
        let z = self.p_num(&rat(0), &s);
        let e1 = self.mk_eq(f, z);
        let e2 = self.mk_eq(f2, z);
        let mut r = self.mk_or2(e1, e2);
        match kind {
            Kind::Eq => {}
            Kind::Ge | Kind::Le => {
                let g1 = self.mk(Op::Ge, vec![f, z]);
                let g2 = self.mk(Op::Ge, vec![f2, z]);
                let iff = self.mk_eq(g1, g2);
                let lit = if kind == Kind::Ge {
                    iff
                } else {
                    self.mk_not(iff)
                };
                r = self.mk_or2(lit, r);
            }
        }
        Some(St::Rw(r, 3))
    }

    /// `arith_rewriter::mk_eq_core`.
    fn arith_eq(&mut self, a: T, b: T) -> Option<St> {
        if self.is_arith_app(a) || self.is_arith_app(b) {
            let st = self.le_ge_eq(a, b, Kind::Eq);
            if st.is_some() {
                return st;
            }
        }
        // mk_eq_mod: k*u mod p = l
        if self.is_op(a, &Op::Mod)
            && let Some(p) = self.arith_num(self.arg(a, 1)).cloned()
            && self.is_op(self.arg(a, 0), &Op::Mul)
            && self.nodes[self.arg(a, 0)].args.len() == 2
            && let Some(k) = self.arith_num(self.arg(self.arg(a, 0), 0)).cloned()
            && let Some(l) = self.arith_num(b).cloned()
            && !l.is_negative()
            && l < p
        {
            let (g, _, bb) = ext_gcd(p.numerator(), k.numerator());
            if g.is_one() {
                let y = self.arg(a, 1);
                let u = self.arg(self.arg(a, 0), 1);
                let nb = self.mk_num(Rational::from_integer(bb), true);
                let lhs = self.mk(Op::Mod, vec![u, y]);
                let prod = self.mk(Op::Mul, vec![nb, b]);
                let rhs = self.mk(Op::Mod, vec![prod, y]);
                return Some(St::Rw(self.mk_eq(lhs, rhs), 2));
            }
        }
        None
    }

    /// `arith_rewriter::mk_div_core`.
    fn mk_div(&mut self, a: T, b: T) -> Option<St> {
        let v2 = self.arith_num(b)?.clone();
        if v2.is_zero() {
            return None;
        }
        if let Some(v1) = self.arith_num(a).cloned() {
            return Some(St::Done(self.mk_num(&v1 / &v2, false)));
        }
        let k = self.mk_num(&rat(1) / &v2, false);
        Some(St::Rw(self.mk_sorted(Op::Mul, vec![k, a], Sort::Real), 1))
    }

    /// `arith_rewriter::mk_idiv_core`.
    fn mk_idiv(&mut self, a: T, b: T) -> Option<St> {
        let v1 = self.arith_num(a).cloned();
        let v2 = self.arith_num(b).cloned();
        if let (Some(v1), Some(v2)) = (&v1, &v2)
            && !v2.is_zero()
        {
            return Some(St::Done(self.mk_num(rdiv(v1, v2), true)));
        }
        if let Some(v2) = &v2 {
            if v2.is_one() {
                return Some(St::Done(a));
            }
            if *v2 == rat(-1) {
                let m1 = self.mk_num(rat(-1), true);
                return Some(St::Rw(self.mk(Op::Mul, vec![m1, a]), 1));
            }
            if v2.is_zero() {
                return None;
            }
        }
        if a == b {
            let zero = self.mk_num(rat(0), true);
            let eq = self.mk_eq(a, zero);
            let d00 = self.mk(Op::Idiv, vec![zero, zero]);
            let one = self.mk_num(rat(1), true);
            return Some(St::Rw(self.mk_ite(eq, d00, one), 3));
        }
        if let Some(v2) = &v2
            && !v2.is_negative()
            && self.is_op(a, &Op::Add)
        {
            let mut args = Vec::new();
            let mut change = false;
            let mut add = rat(0);
            for &x in &self.nodes[a].args.clone() {
                if let Some(xv) = self.arith_num(x).cloned()
                    && !xv.is_negative()
                    && !xv.is_zero()
                    && rmod(&xv, v2) != xv
                {
                    change = true;
                    args.push(self.mk_num(rmod(&xv, v2), true));
                    add = &add + &rdiv(&xv, v2);
                } else {
                    args.push(x);
                }
            }
            if change {
                let sum = self.mk_sorted(Op::Add, args, Sort::Int);
                let d = self.mk(Op::Idiv, vec![sum, b]);
                let k = self.mk_num(add, true);
                return Some(St::Rw(self.mk(Op::Add, vec![k, d]), 3));
            }
        }
        if let Some(r) = self.get_divides(a, b) {
            let zero = self.mk_num(rat(0), true);
            let eq = self.mk_eq(zero, b);
            let d0 = self.mk(Op::Idiv, vec![a, zero]);
            return Some(St::Rw(self.mk_ite(eq, d0, r), FULL));
        }
        None
    }

    /// `arith_rewriter::get_divides`.
    fn get_divides(&mut self, num: T, den: T) -> Option<T> {
        let mut args1 = self.flat_mul_args(num);
        let mut args2 = self.flat_mul_args(den);
        let mut num_r = rat(1);
        let mut den_r = rat(1);
        let mut num_e = None;
        let mut den_e = None;
        let marked: BTreeSet<T> = args1.iter().copied().collect();
        for &a in &args1 {
            if let Some(v) = self.arith_num(a) {
                num_r = v.clone();
                num_e = Some(a);
            }
        }
        for &a in &args2.clone() {
            // z3 reads a marked numeral into `num_r` while testing it.
            if marked.contains(&a) {
                match self.arith_num(a).cloned() {
                    Some(v) => {
                        let minus_one = v == rat(-1);
                        num_r = v;
                        if !minus_one {
                            return Some(self.remove_divisor(a, num, den));
                        }
                    }
                    None => return Some(self.remove_divisor(a, num, den)),
                }
            }
            if let Some(v) = self.arith_num(a) {
                den_r = v.clone();
                den_e = Some(a);
            }
        }
        let g = rgcd(&num_r, &den_r);
        if !g.is_one() {
            if let Some(i) = args1.iter().position(|&x| Some(x) == num_e) {
                args1[i] = self.mk_num(&num_r / &g, true);
            }
            if let Some(i) = args2.iter().position(|&x| Some(x) == den_e) {
                args2[i] = self.mk_num(&den_r / &g, true);
            }
            let n = self.mk_mul_raw(args1);
            let d = self.mk_mul_raw(args2);
            return Some(self.mk(Op::Idiv, vec![n, d]));
        }
        None
    }

    /// `m_util.mk_mul(args)` (a single factor stays itself).
    fn mk_mul_raw(&mut self, args: Vec<T>) -> T {
        if args.len() == 1 {
            return args[0];
        }
        self.mk_sorted(Op::Mul, args, Sort::Int)
    }

    /// `arith_rewriter::remove_divisor`.
    fn remove_divisor(&mut self, arg: T, num: T, den: T) -> T {
        let mut a1 = self.flat_mul_args(num);
        let mut a2 = self.flat_mul_args(den);
        for v in [&mut a1, &mut a2] {
            if let Some(i) = v.iter().position(|&x| x == arg) {
                let last = v.pop().unwrap();
                if i < v.len() {
                    v[i] = last;
                }
            }
        }
        let zero = self.mk_num(rat(0), true);
        let n = if a1.is_empty() {
            self.mk_num(rat(1), true)
        } else {
            self.mk_mul_raw(a1)
        };
        let d = if a2.is_empty() {
            self.mk_num(rat(1), true)
        } else {
            self.mk_mul_raw(a2)
        };
        let dd = self.mk(Op::Idiv, vec![n, d]);
        let un = self.mk(Op::Uminus, vec![n]);
        let ud = self.mk(Op::Uminus, vec![d]);
        let nd = self.mk(Op::Idiv, vec![un, ud]);
        let e0 = self.mk_eq(zero, arg);
        let d00 = self.mk(Op::Idiv, vec![zero, zero]);
        let ge = self.mk(Op::Ge, vec![arg, zero]);
        let inner = self.mk_ite(ge, dd, nd);
        self.mk_ite(e0, d00, inner)
    }

    /// `arith_rewriter::mk_mod_core`.
    fn mk_mod(&mut self, a: T, b: T) -> Option<St> {
        let v1 = self.arith_num(a).cloned();
        let v2 = self.arith_num(b).cloned();
        let is_int = self.nodes[a].sort == Sort::Int;
        if let (Some(v1), Some(v2)) = (&v1, &v2)
            && !v2.is_zero()
        {
            return Some(St::Done(self.mk_num(rmod(v1, v2), is_int)));
        }
        if let Some(v2) = &v2
            && is_int
            && (v2.is_one() || *v2 == rat(-1))
        {
            return Some(St::Done(self.mk_num(rat(0), true)));
        }
        if a == b && v2.is_none() {
            let zero = self.mk_num(rat(0), true);
            let eq = self.mk_eq(b, zero);
            let m00 = self.mk(Op::Mod, vec![zero, zero]);
            return Some(St::Done(self.mk_ite(eq, m00, zero)));
        }
        if self.is_op(a, &Op::Mod) && self.arg(a, 1) == b {
            if v2.as_ref().is_some_and(|v| !v.is_zero()) && is_int {
                return Some(St::Done(a));
            }
            if v2.is_none() && self.nodes[b].sort == Sort::Int {
                let zero = self.mk_num(rat(0), true);
                let eq = self.mk_eq(b, zero);
                let t1 = self.arg(a, 0);
                let m1 = self.mk(Op::Mod, vec![t1, zero]);
                let m2 = self.mk(Op::Mod, vec![m1, zero]);
                return Some(St::Rw(self.mk_ite(eq, m2, a), 2));
            }
        }
        if let Some(v2) = &v2
            && is_int
            && !v2.is_negative()
            && !v2.is_zero()
            && (self.is_add(a) || self.is_mul(a))
        {
            let mut args = Vec::new();
            let mut change = false;
            for &x in &self.nodes[a].args.clone() {
                if let Some(xv) = self.arith_num(x).cloned()
                    && rmod(&xv, v2) != xv
                {
                    change = true;
                    args.push(self.mk_num(rmod(&xv, v2), true));
                } else if self.is_op(x, &Op::Mod) && self.arg(x, 1) == b {
                    change = true;
                    args.push(self.arg(x, 0));
                } else if self.is_op(x, &Op::Mul)
                    && self.nodes[x].args.len() == 2
                    && let Some(xv) = self.arith_num(self.arg(x, 0)).cloned()
                    && symmod(&xv, v2) != xv
                {
                    change = true;
                    let k = self.mk_num(symmod(&xv, v2), true);
                    let t2 = self.arg(x, 1);
                    args.push(self.mk(Op::Mul, vec![k, t2]));
                } else {
                    args.push(x);
                }
            }
            if change {
                let op = self.nodes[a].op.clone();
                let inner = self.mk_sorted(op, args, Sort::Int);
                return Some(St::Rw(self.mk(Op::Mod, vec![inner, b]), 3));
            }
        }
        if v2.is_none() && self.nodes[b].sort == Sort::Int && self.is_add(a) {
            let mut args = Vec::new();
            let mut change = false;
            for &x in &self.nodes[a].args.clone() {
                if x == b {
                    change = true;
                } else if self.is_op(x, &Op::Mul) && self.nodes[x].args.len() == 2 {
                    let (t1, t2) = (self.arg(x, 0), self.arg(x, 1));
                    if (self.arith_num(t1).is_some() && t2 == b)
                        || (self.arith_num(t2).is_some() && t1 == b)
                    {
                        change = true;
                    } else {
                        args.push(x);
                    }
                } else {
                    args.push(x);
                }
            }
            if change {
                let na = if args.is_empty() {
                    self.mk_num(rat(0), true)
                } else if args.len() == 1 {
                    args[0]
                } else {
                    self.mk_sorted(Op::Add, args, Sort::Int)
                };
                return Some(St::Rw(self.mk(Op::Mod, vec![na, b]), 3));
            }
        }
        if let Some(v2) = &v2
            && !v2.is_negative()
            && !v2.is_zero()
            && self.is_op(a, &Op::Mul)
            && self.nodes[a].args.len() == 2
            && let Some(v1) = self.arith_num(self.arg(a, 0)).cloned()
            && !v1.is_negative()
            && !v1.is_zero()
            && v1.is_integer()
            && rmod(v2, &v1).is_zero()
        {
            let k = self.mk_num(v1.clone(), true);
            let q = self.mk_num(v2 / &v1, true);
            let y = self.arg(a, 1);
            let m = self.mk(Op::Mod, vec![y, q]);
            return Some(St::Rw(self.mk(Op::Mul, vec![k, m]), 1));
        }
        if self.is_op(b, &Op::Mul)
            && self.nodes[b].args.len() == 2
            && self
                .arith_num(self.arg(b, 0))
                .is_some_and(|v| *v == rat(-1))
        {
            let t2 = self.arg(b, 1);
            return Some(St::Rw(self.mk(Op::Mod, vec![a, t2]), 1));
        }
        if let Some((x, y, z)) = self.is_ite(b) {
            let m1 = self.mk(Op::Mod, vec![a, y]);
            let m2 = self.mk(Op::Mod, vec![a, z]);
            return Some(St::Rw(self.mk_ite(x, m1, m2), 3));
        }
        None
    }

    /// `arith_rewriter::mk_rem_core` (without `elim_rem`).
    fn mk_rem(&mut self, a: T, b: T) -> Option<St> {
        let v1 = self.arith_num(a).cloned();
        let v2 = self.arith_num(b).cloned();
        let is_int = self.nodes[a].sort == Sort::Int;
        if let (Some(v1), Some(v2)) = (&v1, &v2)
            && !v2.is_zero()
        {
            let mut m = rmod(v1, v2);
            if v2.is_negative() {
                m = -m;
            }
            return Some(St::Done(self.mk_num(m, is_int)));
        }
        if let Some(v2) = &v2
            && is_int
        {
            if v2.is_one() {
                return Some(St::Done(self.mk_num(rat(0), true)));
            }
            if !v2.is_zero() {
                if self.is_add(a) || self.is_mul(a) {
                    return None;
                }
                let m = self.mk(Op::Mod, vec![a, b]);
                if v2.is_negative() {
                    return Some(St::Rw(self.mk(Op::Uminus, vec![m]), 2));
                }
                return Some(St::Rw(m, 1));
            }
        }
        None
    }

    /// `arith_rewriter::mk_to_real_core`.
    fn mk_to_real(&mut self, a: T) -> Option<St> {
        if let Some(v) = self.arith_num(a).cloned() {
            return Some(St::Done(self.mk_num(v, false)));
        }
        if self.nodes[a].sort == Sort::Real {
            return Some(St::Done(a));
        }
        if self.is_op(a, &Op::Add) || self.is_op(a, &Op::Mul) {
            let op = self.nodes[a].op.clone();
            let kids = self.nodes[a].args.clone();
            let ns: Vec<T> = kids.iter().map(|&k| self.mk(Op::ToReal, vec![k])).collect();
            return Some(St::Rw(self.mk_sorted(op, ns, Sort::Real), 2));
        }
        None
    }

    /// `arith_rewriter::mk_to_int_core`.
    fn mk_to_int(&mut self, a: T) -> Option<St> {
        if self.nodes[a].sort == Sort::Int {
            return Some(St::Done(a));
        }
        if let Some(v) = self.arith_num(a).cloned() {
            return Some(St::Done(
                self.mk_num(Rational::from_integer(v.floor()), true),
            ));
        }
        if self.is_op(a, &Op::ToReal) && self.nodes[self.arg(a, 0)].sort == Sort::Int {
            return Some(St::Done(self.arg(a, 0)));
        }
        if self.is_op(a, &Op::Add) || self.is_op(a, &Op::Mul) {
            let op = self.nodes[a].op.clone();
            let mut int_args = Vec::new();
            let mut real_args = Vec::new();
            for &c in &self.nodes[a].args.clone() {
                if let Some(v) = self.arith_num(c).cloned()
                    && v.is_integer()
                {
                    int_args.push(self.mk_num(v, true));
                } else if self.is_op(c, &Op::ToReal) {
                    int_args.push(self.arg(c, 0));
                } else {
                    real_args.push(c);
                }
            }
            if real_args.is_empty() {
                return Some(St::Rw(self.mk_sorted(op, int_args, Sort::Int), 1));
            }
            if !int_args.is_empty() && op == Op::Add {
                let t1 = self.mk_sorted(Op::Add, int_args, Sort::Int);
                let t2 = self.mk_sorted(Op::Add, real_args, Sort::Real);
                let ti = self.mk(Op::ToInt, vec![t2]);
                return Some(St::Rw(self.mk_sorted(Op::Add, vec![t1, ti], Sort::Int), 3));
            }
        }
        None
    }

    /// `arith_rewriter::mk_is_int`.
    fn mk_is_int(&mut self, a: T) -> Option<St> {
        if let Some(v) = self.arith_num(a) {
            let b = v.is_integer();
            return Some(St::Done(self.mk_bool(b)));
        }
        if self.is_op(a, &Op::ToReal) && self.nodes[self.arg(a, 0)].sort == Sort::Int {
            return Some(St::Done(self.mk_true()));
        }
        let mut todo = vec![a];
        let mut seen = BTreeSet::new();
        let mut ok = true;
        while let Some(e) = todo.pop() {
            if !seen.insert(e) {
                continue;
            }
            if self.is_op(e, &Op::ToReal) {
                continue;
            }
            if let Some(v) = self.arith_num(e) {
                if v.is_integer() {
                    continue;
                }
                ok = false;
                break;
            }
            if matches!(self.nodes[e].op, Op::Mul | Op::Add | Op::Sub | Op::Uminus) {
                todo.extend_from_slice(&self.nodes[e].args);
                continue;
            }
            ok = false;
            break;
        }
        if ok {
            return Some(St::Done(self.mk_true()));
        }
        let ti = self.mk(Op::ToInt, vec![a]);
        let tr = self.mk(Op::ToReal, vec![ti]);
        Some(St::Rw(self.mk_eq(tr, a), 3))
    }
}

/// `symmod`: the representative of `a mod b` in `(-b/2, b/2]`.
fn symmod(a: &Rational, b: &Rational) -> Rational {
    let mut r = rmod(a, b);
    if &r * &rat(2) > *b {
        r = &r - b;
    }
    r
}

/// The extended gcd `(g, x, y)` with `x·a + y·b = g`, as z3's `gcd(p, k, a, b)`.
fn ext_gcd(a: &Int, b: &Int) -> (Int, Int, Int) {
    let (mut r0, mut r1) = (a.clone(), b.clone());
    let (mut s0, mut s1) = (Int::from(1), Int::from(0));
    let (mut t0, mut t1) = (Int::from(0), Int::from(1));
    while !r1.is_zero() {
        let q = r0.div_floor(&r1);
        let r2 = &r0 - &(&q * &r1);
        r0 = core::mem::replace(&mut r1, r2);
        let s2 = &s0 - &(&q * &s1);
        s0 = core::mem::replace(&mut s1, s2);
        let t2 = &t0 - &(&q * &t1);
        t0 = core::mem::replace(&mut t1, t2);
    }
    if r0.is_negative() {
        (-&r0, -&s0, -&t0)
    } else {
        (r0, s0, t0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nested_sums_flatten_and_fold() {
        // (+ 1 (+ 1 x)) → (+ 2 x)
        let mut s = Simp::new();
        let x = s.mk_sorted(Op::Uf("x".into()), Vec::new(), Sort::Int);
        let one = s.mk_num(rat(1), true);
        let inner = s.mk(Op::Add, vec![one, x]);
        let outer = s.mk(Op::Add, vec![one, inner]);
        let r = s.simplify(outer);
        assert_eq!(*s.op(r), Op::Add);
        assert_eq!(*s.op(s.args(r)[0]), Op::Num(rat(2)));
        assert_eq!(s.args(r)[1], x);
    }

    #[test]
    fn strict_inequality_moves_constants_right() {
        // (< x (+ y 2)) → (not (<= y (+ (- 2) x)))
        let mut s = Simp::new();
        let x = s.mk_sorted(Op::Uf("x".into()), Vec::new(), Sort::Int);
        let y = s.mk_sorted(Op::Uf("y".into()), Vec::new(), Sort::Int);
        let two = s.mk_num(rat(2), true);
        let sum = s.mk(Op::Add, vec![y, two]);
        let lt = s.mk(Op::Lt, vec![x, sum]);
        let r = s.simplify(lt);
        assert_eq!(*s.op(r), Op::Not);
        let le = s.args(r)[0];
        assert_eq!(*s.op(le), Op::Le);
        assert_eq!(s.args(le)[0], y);
        let rhs = s.args(le)[1];
        assert_eq!(*s.op(s.args(rhs)[0]), Op::Num(rat(-2)));
        assert_eq!(s.args(rhs)[1], x);
    }
}
