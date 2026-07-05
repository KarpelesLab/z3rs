//! DRAT proof checking — the checker behind Z3's `-drat` frontend
//! (`z3/src/sat/dimacs.cpp` proof reader + `z3/src/sat/drat.cpp`, Z3 4.17.0,
//! MIT). Given a CNF and a DRAT proof (a sequence of clause additions and
//! deletions), verify that every added clause is redundant with respect to the
//! current formula — by **RUP** (reverse unit propagation), falling back to
//! **RAT** (resolution asymmetric tautology) on the clause's first literal — and
//! that the proof derives the empty clause. This certifies UNSAT independently
//! of the solver that produced the proof.
//!
//! Clauses and literals reuse the SAT core's [`Lit`] packing. The proof text
//! format is the standard DRAT one: whitespace-separated DIMACS integers per
//! step terminated by `0`, with a leading `d` marking a deletion.

use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec::Vec;

use crate::sat::literal::Lit;

/// One line of a DRAT proof.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Step {
    /// Add (learn) a clause; the checker must certify it is redundant.
    Add(Vec<Lit>),
    /// Delete a previously-present clause.
    Delete(Vec<Lit>),
}

/// Parse a signed DIMACS integer into a [`Lit`] (`|n|-1` is the variable,
/// negative sign ⇒ negative literal).
fn lit_of(n: i64) -> Lit {
    Lit::new((n.unsigned_abs() - 1) as u32, n < 0)
}

/// Parse the CNF portion (DIMACS) into a clause list, ignoring the `p`/`c`
/// lines. Shared shape with [`crate::sat::dimacs`] but keeps the raw clauses.
pub fn parse_cnf(input: &str) -> Result<Vec<Vec<Lit>>, String> {
    let mut clauses = Vec::new();
    let mut clause: Vec<Lit> = Vec::new();
    for line in input.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') || line.starts_with('p') {
            continue;
        }
        for tok in line.split_whitespace() {
            let n: i64 = tok.parse().map_err(|_| format!("invalid token {tok:?}"))?;
            if n == 0 {
                clauses.push(core::mem::take(&mut clause));
            } else {
                clause.push(lit_of(n));
            }
        }
    }
    if !clause.is_empty() {
        clauses.push(clause);
    }
    Ok(clauses)
}

/// Parse a DRAT proof: each line is a step (leading `d` = deletion), a
/// whitespace-separated list of DIMACS integers ending in `0`.
pub fn parse_proof(input: &str) -> Result<Vec<Step>, String> {
    let mut steps = Vec::new();
    for line in input.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        let (is_del, rest) = match line.strip_prefix("d ") {
            Some(r) => (true, r),
            None => (false, line),
        };
        let mut clause = Vec::new();
        for tok in rest.split_whitespace() {
            let n: i64 = tok.parse().map_err(|_| format!("invalid token {tok:?}"))?;
            if n == 0 {
                break;
            }
            clause.push(lit_of(n));
        }
        steps.push(if is_del {
            Step::Delete(clause)
        } else {
            Step::Add(clause)
        });
    }
    Ok(steps)
}

/// Unit-propagate `assign` over `clauses`; return `true` if a conflict (a clause
/// whose literals are all falsified) is reached. `assign[var]` is
/// `Some(value)` for assigned variables. Runs to fixpoint.
fn propagate_conflict(clauses: &[Vec<Lit>], assign: &mut [Option<bool>]) -> bool {
    let mut changed = true;
    while changed {
        changed = false;
        for c in clauses {
            let mut unassigned: Option<Lit> = None;
            let mut satisfied = false;
            let mut count_unassigned = 0;
            for &l in c {
                match assign[l.var() as usize] {
                    Some(v) if v != l.sign() => {
                        // literal is true (sign=false→need value true)
                        satisfied = true;
                        break;
                    }
                    Some(_) => {} // false literal
                    None => {
                        count_unassigned += 1;
                        unassigned = Some(l);
                    }
                }
            }
            if satisfied {
                continue;
            }
            if count_unassigned == 0 {
                return true; // all literals false ⇒ conflict
            }
            if count_unassigned == 1 {
                let l = unassigned.unwrap();
                // Force l true: value = !sign.
                assign[l.var() as usize] = Some(!l.sign());
                changed = true;
            }
        }
    }
    false
}

/// Does `clauses` entail the negation of `clause` by unit propagation — i.e. is
/// `clause` a **RUP** (reverse unit propagation) consequence? Assign every
/// literal of `clause` to false, then propagate; RUP holds iff a conflict
/// results.
fn is_rup(clauses: &[Vec<Lit>], clause: &[Lit], num_vars: usize) -> bool {
    let mut assign = alloc::vec![None; num_vars];
    for &l in clause {
        // ¬l: set var so that l is false.
        let want_false = l.sign(); // if l negative, l false ⇒ var true
        match assign[l.var() as usize] {
            Some(v) if v != want_false => return true, // clause has l and ¬l ⇒ tautology, trivially redundant
            _ => assign[l.var() as usize] = Some(want_false),
        }
    }
    propagate_conflict(clauses, &mut assign)
}

/// RAT check on the first literal: `clause` is RAT if it is RUP, or for every
/// clause `D` in the formula containing `¬p` (p = first literal), the resolvent
/// `clause ∪ (D \ {¬p})` is RUP.
fn is_rat(clauses: &[Vec<Lit>], clause: &[Lit], num_vars: usize) -> bool {
    if is_rup(clauses, clause, num_vars) {
        return true;
    }
    let Some(&p) = clause.first() else {
        // Empty clause must be RUP to be valid.
        return false;
    };
    let np = !p;
    for d in clauses {
        if !d.contains(&np) {
            continue;
        }
        let mut resolvent: Vec<Lit> = clause.to_vec();
        for &l in d {
            if l != np && !resolvent.contains(&l) {
                resolvent.push(l);
            }
        }
        if !is_rup(clauses, &resolvent, num_vars) {
            return false;
        }
    }
    true
}

/// Check a DRAT proof against a CNF. Returns `Ok(())` iff every added clause is
/// RAT-redundant at the point it is added and the proof derives the empty
/// clause (certifying UNSAT). Deletions remove one matching clause occurrence.
pub fn check(cnf: &[Vec<Lit>], proof: &[Step]) -> Result<(), String> {
    let mut num_vars = 0usize;
    let mut scan = |c: &[Lit]| {
        for &l in c {
            num_vars = num_vars.max(l.var() as usize + 1);
        }
    };
    for c in cnf {
        scan(c);
    }
    for s in proof {
        match s {
            Step::Add(c) | Step::Delete(c) => scan(c),
        }
    }

    let mut db: Vec<Vec<Lit>> = cnf.to_vec();
    let mut derived_empty = false;
    for step in proof {
        match step {
            Step::Add(c) => {
                if !is_rat(&db, c, num_vars) {
                    return Err(format!(
                        "clause {:?} is not RAT-redundant",
                        c.iter().map(|l| l.to_string()).collect::<Vec<_>>()
                    ));
                }
                if c.is_empty() {
                    derived_empty = true;
                }
                db.push(c.clone());
            }
            Step::Delete(c) => {
                // Remove one clause equal as a set.
                if let Some(pos) = db.iter().position(|d| same_clause(d, c)) {
                    db.swap_remove(pos);
                }
            }
        }
    }
    if derived_empty {
        Ok(())
    } else {
        Err("proof does not derive the empty clause".into())
    }
}

fn same_clause(a: &[Lit], b: &[Lit]) -> bool {
    a.len() == b.len() && a.iter().all(|l| b.contains(l))
}

/// Convenience: parse a DIMACS CNF and a DRAT proof from text and check.
pub fn check_text(cnf: &str, proof: &str) -> Result<(), String> {
    let cnf = parse_cnf(cnf)?;
    let proof = parse_proof(proof)?;
    check(&cnf, &proof)
}

#[cfg(test)]
mod tests {
    use super::*;

    // The classic tiny UNSAT core: (a)(¬a) — DRAT adds the empty clause.
    #[test]
    fn checks_trivial_refutation() {
        let cnf = "p cnf 1 2\n1 0\n-1 0\n";
        let proof = "0\n"; // add empty clause; it is RUP (propagation conflicts)
        assert!(check_text(cnf, proof).is_ok());
    }

    // A real DRUP proof of a small UNSAT instance.
    // (1 2)(-1 2)(1 -2)(-1 -2) is UNSAT. A RUP proof: derive (2), (-2), ().
    #[test]
    fn checks_rup_refutation() {
        let cnf = "p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n";
        let proof = "2 0\n-2 0\n0\n";
        assert!(check_text(cnf, proof).is_ok(), "valid DRUP proof rejected");
    }

    // A bogus proof (adds a non-redundant clause) is rejected.
    #[test]
    fn rejects_invalid_addition() {
        let cnf = "p cnf 2 1\n1 2 0\n"; // satisfiable
        // Claim we can add the unit (1) — not RUP-implied.
        let proof = "1 0\n0\n";
        assert!(check_text(cnf, proof).is_err());
    }

    // A proof that never reaches the empty clause is incomplete.
    #[test]
    fn rejects_incomplete_proof() {
        let cnf = "p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n";
        let proof = "2 0\n"; // stops early
        assert!(check_text(cnf, proof).is_err());
    }

    // Deletion lines are honoured (parsed and applied) without breaking a valid
    // proof.
    #[test]
    fn handles_deletions() {
        let cnf = "p cnf 2 4\n1 2 0\n-1 2 0\n1 -2 0\n-1 -2 0\n";
        let proof = "2 0\nd 1 2 0\n-2 0\n0\n";
        assert!(check_text(cnf, proof).is_ok());
    }
}
