//! DIMACS CNF parsing — ports the reader used by Z3's DIMACS frontend
//! (`z3/src/sat/dimacs.{h,cpp}`, Z3 4.17.0, MIT).
//!
//! Accepts the standard format: `c` comment lines, an optional `p cnf V C`
//! header, and clauses given as whitespace-separated 1-based signed integers
//! terminated by `0` (clauses may span lines).

use alloc::format;
use alloc::string::String;

use crate::sat::literal::Lit;
use crate::sat::solver::Solver;

/// An error parsing DIMACS input.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct DimacsError(pub String);

impl core::fmt::Display for DimacsError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "DIMACS parse error: {}", self.0)
    }
}

/// Parse DIMACS CNF `input` into a ready-to-solve [`Solver`].
pub fn parse(input: &str) -> Result<Solver, DimacsError> {
    let mut solver = Solver::new();
    let mut clause: alloc::vec::Vec<Lit> = alloc::vec::Vec::new();

    for line in input.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('c') || line.starts_with('p') {
            continue; // comment, empty, or the problem header
        }
        for tok in line.split_whitespace() {
            let n: i64 = tok
                .parse()
                .map_err(|_| DimacsError(format!("invalid token {tok:?}")))?;
            if n == 0 {
                solver.add_clause(&clause);
                clause.clear();
            } else {
                let var = (n.unsigned_abs() - 1) as u32;
                clause.push(Lit::new(var, n < 0));
            }
        }
    }
    // Tolerate a final clause without a trailing 0.
    if !clause.is_empty() {
        solver.add_clause(&clause);
    }
    Ok(solver)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sat::solver::SatResult;

    #[test]
    fn parses_and_solves_sat() {
        let cnf = "\
c a small satisfiable instance
p cnf 3 2
1 -2 0
2 3 0
";
        let mut s = parse(cnf).unwrap();
        assert_eq!(s.num_vars(), 3);
        assert_eq!(s.solve(), SatResult::Sat);
    }

    #[test]
    fn parses_and_solves_unsat() {
        // (x1) ∧ (¬x1)
        let cnf = "p cnf 1 2\n1 0\n-1 0\n";
        let mut s = parse(cnf).unwrap();
        assert_eq!(s.solve(), SatResult::Unsat);
    }

    #[test]
    fn clauses_may_span_lines() {
        let cnf = "1 2\n3 0 -1\n-2 0";
        let mut s = parse(cnf).unwrap();
        // Two clauses: (1 2 3) and (-1 -2).
        assert_eq!(s.solve(), SatResult::Sat);
    }

    #[test]
    fn rejects_garbage() {
        assert!(parse("1 foo 0").is_err());
    }
}
