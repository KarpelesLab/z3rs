//! `z3rs` command-line frontend — the pure-Rust counterpart of Z3's `shell`
//! (`z3/src/shell/main.cpp`). Aims for CLI compatibility with the `z3` binary.
//!
//! Frontends, mirroring `z3/src/shell/`:
//! - [x] DIMACS (`dimacs_frontend.cpp`)   — `-dimacs` / `*.cnf`
//! - [x] SMT-LIB2 (`smtlib_frontend.cpp`) — the default `-smt2` mode
//! - [x] Datalog (`datalog_frontend.cpp`) — `-dl`
//! - [x] DRAT (`drat_frontend.cpp`)       — `-drat <cnf> <proof>`

use std::process::ExitCode;

use z3rs::cmd_context::run_smt2;
use z3rs::sat::{SatResult, check_drat_text, parse_dimacs};
use z3rs::util::lbool::LBool;

fn print_version() {
    println!(
        "z3rs version {} (pure-Rust port of Z3 {})",
        z3rs::VERSION,
        z3rs::Z3_UPSTREAM_VERSION
    );
}

fn print_usage() {
    println!("z3rs [options] <file>");
    println!();
    println!("A pure-Rust port of the Z3 theorem prover (early, in progress).");
    println!();
    println!("Options:");
    println!("  -h, --help       print this message");
    println!("  --version        print version information");
    println!("  -smt2            read input as SMT-LIB2 (default; QF_UF subset)");
    println!("  -dimacs          read input in DIMACS CNF format (default for *.cnf)");
    println!("  -dl              read input as Datalog (facts/rules/?- queries)");
    println!("  -drat <cnf> <p>  check a DRAT proof <p> against a DIMACS CNF <cnf>");
}

/// Run a Datalog program: evaluate its least fixpoint and answer each `?-`
/// query, printing `sat`/`unsat` per query (z3's `-dl` verdict for whether the
/// query relation is non-empty), plus enumerated solutions for open queries.
fn run_datalog_file(path: &str) -> ExitCode {
    let text = match std::fs::read_to_string(path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("z3rs: cannot read {path:?}: {e}");
            return ExitCode::from(1);
        }
    };
    let program = match z3rs::muz::parse(&text) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("z3rs: {e}");
            return ExitCode::from(1);
        }
    };
    let model = z3rs::muz::evaluate(&program);
    for q in &program.queries {
        let answers = model.query(q);
        if answers.is_empty() {
            println!("unsat");
        } else {
            println!("sat");
        }
    }
    ExitCode::SUCCESS
}

/// Check a DRAT proof against a DIMACS CNF, printing `s VERIFIED` (exit 0) or a
/// diagnostic (exit 1), mirroring an independent DRAT checker.
fn run_drat(cnf_path: &str, proof_path: &str) -> ExitCode {
    let cnf = match std::fs::read_to_string(cnf_path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("z3rs: cannot read {cnf_path:?}: {e}");
            return ExitCode::from(1);
        }
    };
    let proof = match std::fs::read_to_string(proof_path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("z3rs: cannot read {proof_path:?}: {e}");
            return ExitCode::from(1);
        }
    };
    match check_drat_text(&cnf, &proof) {
        Ok(()) => {
            println!("s VERIFIED");
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("z3rs: DRAT check failed: {e}");
            ExitCode::from(1)
        }
    }
}

/// Solve a DIMACS CNF file and print SAT-competition-style output.
/// Exit codes follow the convention: 10 = SAT, 20 = UNSAT.
fn run_dimacs(path: &str) -> ExitCode {
    let text = match std::fs::read_to_string(path) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("z3rs: cannot read {path:?}: {e}");
            return ExitCode::from(1);
        }
    };
    let mut solver = match parse_dimacs(&text) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("z3rs: {e}");
            return ExitCode::from(1);
        }
    };
    match solver.solve() {
        SatResult::Sat => {
            println!("s SATISFIABLE");
            // Emit the model as a DIMACS `v` line (1-based signed literals).
            let mut line = String::from("v");
            for v in 0..solver.num_vars() as u32 {
                let signed = match solver.value(v) {
                    LBool::False => -((v + 1) as i64),
                    _ => (v + 1) as i64, // True, or Undef (don't-care) reported positive
                };
                line.push_str(&format!(" {signed}"));
            }
            line.push_str(" 0");
            println!("{line}");
            ExitCode::from(10)
        }
        SatResult::Unsat => {
            println!("s UNSATISFIABLE");
            ExitCode::from(20)
        }
    }
}

/// Run an SMT-LIB2 script file, printing one response line per `(check-sat)`.
fn run_smt2_file(path: &str) -> ExitCode {
    let bytes = match std::fs::read(path) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("z3rs: cannot read {path:?}: {e}");
            return ExitCode::from(1);
        }
    };
    // z3 reads scripts as raw bytes; fall back to a latin-1 decoding when the
    // input is not valid UTF-8 (non-UTF8 bytes usually appear only in comments
    // or string literals), so such files still parse.
    let text = match String::from_utf8(bytes) {
        Ok(t) => t,
        Err(e) => e.into_bytes().iter().map(|&b| b as char).collect(),
    };
    match run_smt2(&text) {
        Ok(responses) => {
            for r in responses {
                println!("{r}");
            }
            ExitCode::SUCCESS
        }
        Err(e) => {
            eprintln!("z3rs: {e}");
            ExitCode::from(1)
        }
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();

    if args.is_empty() {
        print_usage();
        return ExitCode::SUCCESS;
    }

    let mut force_dimacs = false;
    let mut force_datalog = false;
    let mut force_drat = false;
    let mut files: Vec<String> = Vec::new();
    for arg in &args {
        match arg.as_str() {
            "--version" | "-version" | "/version" => {
                print_version();
                return ExitCode::SUCCESS;
            }
            "-h" | "--help" | "-?" | "/?" => {
                print_usage();
                return ExitCode::SUCCESS;
            }
            "-dimacs" => force_dimacs = true,
            "-dl" => force_datalog = true,
            "-drat" => force_drat = true,
            "-smt2" | "-in" => {} // format hints; inferred from extension otherwise
            other if other.starts_with('-') => {
                eprintln!("z3rs: unknown option {other:?}");
                return ExitCode::from(1);
            }
            other => files.push(other.to_string()),
        }
    }

    if force_drat {
        return match files.as_slice() {
            [cnf, proof] => run_drat(cnf, proof),
            _ => {
                eprintln!("z3rs: -drat requires exactly two files: <cnf> <proof>");
                ExitCode::from(1)
            }
        };
    }

    let file = files.into_iter().next();
    match file {
        Some(path) if force_datalog || path.ends_with(".dl") || path.ends_with(".datalog") => {
            run_datalog_file(&path)
        }
        Some(path) if force_dimacs || path.ends_with(".cnf") || path.ends_with(".dimacs") => {
            run_dimacs(&path)
        }
        Some(path) => run_smt2_file(&path), // default: SMT-LIB2 (e.g. *.smt2)
        None => {
            print_usage();
            ExitCode::SUCCESS
        }
    }
}
