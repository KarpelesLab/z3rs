//! A bounded decision procedure for word equations.
//!
//! The problem is a conjunction of word equations and disequations between
//! concatenations of string variables and literals, plus constraints on the
//! variables' lengths that a caller-supplied oracle decides. Once every
//! variable's length is fixed, the equations become position constraints: the
//! two sides must have the same length and agree position by position, which a
//! union-find over the variables' character positions and the literal
//! characters checks exactly. A disequation fails only when both sides are
//! forced equal position by position; giving each free position class its own
//! fresh character then satisfies every other disequation at once. So for
//! each length vector the conjunction is decided exactly, and enumerating all
//! length vectors within proven bounds decides the whole problem.

use alloc::vec;
use alloc::vec::Vec;

/// One factor of a concatenation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Tok {
    /// String variable `i`.
    Var(usize),
    /// A literal (code points).
    Lit(Vec<u32>),
}

/// The word-equation part of a problem.
#[derive(Clone, Debug, Default)]
pub struct WordProblem {
    /// Number of string variables.
    pub nvars: usize,
    /// Equations `lhs = rhs`.
    pub eqs: Vec<(Vec<Tok>, Vec<Tok>)>,
    /// Disequations `lhs ≠ rhs`.
    pub neqs: Vec<(Vec<Tok>, Vec<Tok>)>,
}

/// The outcome of the bounded search.
#[derive(Debug, PartialEq, Eq)]
pub enum Outcome {
    /// A solution: each variable's value.
    Found(Vec<Vec<u32>>),
    /// No length vector within the bounds admits a solution.
    Exhausted,
    /// The search was cut short (budget, or an undecided length vector).
    Incomplete,
}

/// What the length oracle says about a length vector.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LenVerdict {
    Feasible,
    Infeasible,
    Unknown,
}

/// A character position: variable `v`'s `i`-th character, or a literal one.
#[derive(Clone, Copy)]
enum Cell {
    Pos(usize, usize),
    Ch(u32),
}

struct Classes {
    parent: Vec<usize>,
    /// The literal character a class is pinned to.
    pinned: Vec<Option<u32>>,
}

impl Classes {
    fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            self.parent[x] = self.parent[self.parent[x]];
            x = self.parent[x];
        }
        x
    }
}

fn cells(side: &[Tok], lens: &[usize]) -> Vec<Cell> {
    let mut out = Vec::new();
    for t in side {
        match t {
            Tok::Var(v) => out.extend((0..lens[*v]).map(|i| Cell::Pos(*v, i))),
            Tok::Lit(l) => out.extend(l.iter().map(|&c| Cell::Ch(c))),
        }
    }
    out
}

fn side_len(side: &[Tok], lens: &[usize]) -> usize {
    side.iter()
        .map(|t| match t {
            Tok::Var(v) => lens[*v],
            Tok::Lit(l) => l.len(),
        })
        .sum()
}

impl WordProblem {
    /// Decide the equations and disequations for fixed lengths `lens`,
    /// returning the variables' values (free classes get fresh characters
    /// from `fresh`) or `None` when unsatisfiable at these lengths.
    fn solve_at(&self, lens: &[usize], fresh: &[u32]) -> Option<Vec<Vec<u32>>> {
        let mut offset = vec![0usize; self.nvars + 1];
        for v in 0..self.nvars {
            offset[v + 1] = offset[v] + lens[v];
        }
        let n = offset[self.nvars];
        let mut cl = Classes {
            parent: (0..n).collect(),
            pinned: vec![None; n],
        };
        let idx = |c: Cell| match c {
            Cell::Pos(v, i) => Some(offset[v] + i),
            Cell::Ch(_) => None,
        };
        for (l, r) in &self.eqs {
            if side_len(l, lens) != side_len(r, lens) {
                return None;
            }
            for (a, b) in cells(l, lens).into_iter().zip(cells(r, lens)) {
                match (idx(a), idx(b), a, b) {
                    (Some(x), Some(y), _, _) => {
                        let (x, y) = (cl.find(x), cl.find(y));
                        if x != y {
                            match (cl.pinned[x], cl.pinned[y]) {
                                (Some(p), Some(q)) if p != q => return None,
                                (None, Some(q)) => cl.pinned[x] = Some(q),
                                _ => {}
                            }
                            cl.parent[y] = x;
                        }
                    }
                    (Some(x), None, _, Cell::Ch(c)) | (None, Some(x), Cell::Ch(c), _) => {
                        let x = cl.find(x);
                        match cl.pinned[x] {
                            Some(p) if p != c => return None,
                            _ => cl.pinned[x] = Some(c),
                        }
                    }
                    (None, None, Cell::Ch(p), Cell::Ch(q)) => {
                        if p != q {
                            return None;
                        }
                    }
                    _ => unreachable!(),
                }
            }
        }
        // A disequation fails when every position pair is forced equal.
        for (l, r) in &self.neqs {
            if side_len(l, lens) != side_len(r, lens) {
                continue;
            }
            let mut forced = true;
            for (a, b) in cells(l, lens).into_iter().zip(cells(r, lens)) {
                let same = match (idx(a), idx(b), a, b) {
                    (Some(x), Some(y), _, _) => {
                        let (x, y) = (cl.find(x), cl.find(y));
                        x == y
                            || matches!((cl.pinned[x], cl.pinned[y]), (Some(p), Some(q)) if p == q)
                    }
                    (Some(x), None, _, Cell::Ch(c)) | (None, Some(x), Cell::Ch(c), _) => {
                        let x = cl.find(x);
                        cl.pinned[x] == Some(c)
                    }
                    (None, None, Cell::Ch(p), Cell::Ch(q)) => p == q,
                    _ => unreachable!(),
                };
                if !same {
                    forced = false;
                    break;
                }
            }
            if forced {
                return None;
            }
        }
        // Values: pinned classes take their character, free ones a fresh one.
        let mut fresh_of: Vec<Option<u32>> = vec![None; n];
        let mut next = 0usize;
        let mut values = Vec::with_capacity(self.nvars);
        for v in 0..self.nvars {
            let mut s = Vec::with_capacity(lens[v]);
            for i in 0..lens[v] {
                let r = cl.find(offset[v] + i);
                let c = match cl.pinned[r] {
                    Some(c) => c,
                    None => match fresh_of[r] {
                        Some(c) => c,
                        None => {
                            let c = *fresh.get(next)?;
                            next += 1;
                            fresh_of[r] = Some(c);
                            c
                        }
                    },
                };
                s.push(c);
            }
            values.push(s);
        }
        Some(values)
    }

    /// Search the length vectors with `lens[v] ≤ bounds[v]`, in order of total
    /// length, asking `len_ok` about each one that the equations allow. At most
    /// `budget` vectors are examined.
    pub fn search(
        &self,
        bounds: &[usize],
        budget: usize,
        len_ok: &mut dyn FnMut(&[usize]) -> LenVerdict,
    ) -> Outcome {
        // Fresh characters: upper-case letters, then other code points, none
        // of them occurring in a literal.
        let mut used: Vec<u32> = Vec::new();
        for (l, r) in self.eqs.iter().chain(&self.neqs) {
            for t in l.iter().chain(r) {
                if let Tok::Lit(s) = t {
                    used.extend_from_slice(s);
                }
            }
        }
        let total_max: usize = bounds.iter().sum();
        let fresh: Vec<u32> = ('A' as u32..)
            .filter(|c| !used.contains(c))
            .take(total_max + 1)
            .collect();
        let mut complete = true;
        let mut examined = 0usize;
        for total in 0..=total_max {
            let mut lens = vec![0usize; self.nvars];
            let stopped = self.enumerate(0, total, bounds, &mut lens, &mut |lens| {
                examined += 1;
                if examined > budget {
                    complete = false;
                    return Some(None);
                }
                // Cheap length check of every equation first.
                if self
                    .eqs
                    .iter()
                    .any(|(l, r)| side_len(l, lens) != side_len(r, lens))
                {
                    return None;
                }
                let values = self.solve_at(lens, &fresh)?;
                match len_ok(lens) {
                    LenVerdict::Feasible => Some(Some(values)),
                    LenVerdict::Infeasible => None,
                    LenVerdict::Unknown => {
                        complete = false;
                        None
                    }
                }
            });
            match stopped {
                Some(Some(values)) => return Outcome::Found(values),
                Some(None) => return Outcome::Incomplete,
                None => {}
            }
        }
        if complete {
            Outcome::Exhausted
        } else {
            Outcome::Incomplete
        }
    }

    /// Enumerate the vectors with entries `≤ bounds` summing to `total`
    /// (variables from `v` on), calling `f` on each; `f` returns `Some(_)` to
    /// stop the walk, which is then returned.
    #[allow(clippy::type_complexity)]
    fn enumerate(
        &self,
        v: usize,
        total: usize,
        bounds: &[usize],
        lens: &mut Vec<usize>,
        f: &mut dyn FnMut(&[usize]) -> Option<Option<Vec<Vec<u32>>>>,
    ) -> Option<Option<Vec<Vec<u32>>>> {
        if v == self.nvars {
            return if total == 0 { f(lens) } else { None };
        }
        let rest: usize = bounds[v + 1..].iter().sum();
        let lo = total.saturating_sub(rest);
        let hi = bounds[v].min(total);
        for k in lo..=hi {
            lens[v] = k;
            // Prune on the equations whose variables are all assigned now.
            let balanced = self.eqs.iter().all(|(l, r)| {
                let last = l.iter().chain(r).fold(None, |m: Option<usize>, t| match t {
                    Tok::Var(i) => Some(m.map_or(*i, |m| m.max(*i))),
                    Tok::Lit(_) => m,
                });
                last.is_none_or(|m| m != v) || side_len(l, lens) == side_len(r, lens)
            });
            if !balanced {
                continue;
            }
            if let Some(r) = self.enumerate(v + 1, total - k, bounds, lens, f) {
                return Some(r);
            }
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(s: &str) -> Tok {
        Tok::Lit(s.chars().map(|c| c as u32).collect())
    }

    #[test]
    fn decides_bounded_equations() {
        // e = a·"abc"·b ∧ e = c·"ef"·d with |e| = 4: unsat; |e| = 5: sat.
        let p = WordProblem {
            nvars: 5,
            eqs: vec![
                (
                    vec![Tok::Var(4)],
                    vec![Tok::Var(0), lit("abc"), Tok::Var(1)],
                ),
                (vec![Tok::Var(4)], vec![Tok::Var(2), lit("ef"), Tok::Var(3)]),
            ],
            neqs: vec![],
        };
        let bounds = [4, 4, 4, 4, 4];
        let r = p.search(&bounds, 100_000, &mut |l| {
            if l[4] == 4 {
                LenVerdict::Feasible
            } else {
                LenVerdict::Infeasible
            }
        });
        assert_eq!(r, Outcome::Exhausted);
        let bounds = [5, 5, 5, 5, 5];
        let r = p.search(&bounds, 100_000, &mut |l| {
            if l[4] == 5 {
                LenVerdict::Feasible
            } else {
                LenVerdict::Infeasible
            }
        });
        let Outcome::Found(v) = r else {
            panic!("{r:?}")
        };
        let s: alloc::string::String = v[4].iter().map(|&c| char::from_u32(c).unwrap()).collect();
        assert_eq!(s, "abcef");
    }
}
