//! `z3rs` command-line frontend — the pure-Rust counterpart of Z3's `shell`
//! (`z3/src/shell/main.cpp`). Aims for CLI compatibility with the `z3` binary.
//!
//! Frontends, mirroring `z3/src/shell/`:
//! - [x] DIMACS (`dimacs_frontend.cpp`)   — `-dimacs` / `*.cnf`
//! - [ ] SMT-LIB2 (`smtlib_frontend.cpp`) — the default `-smt2` mode
//! - [ ] Datalog (`datalog_frontend.cpp`) — `-dl`
//! - [ ] DRAT (`drat_frontend.cpp`)       — `-drat`

use std::process::ExitCode;

use z3rs::sat::{SatResult, parse_dimacs};
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
    println!("  -dimacs          read input in DIMACS CNF format (default for *.cnf)");
    println!("  -smt2            read input as SMT-LIB2                         [TODO]");
    println!("  -dl              read input as Datalog                         [TODO]");
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

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();

    if args.is_empty() {
        print_usage();
        return ExitCode::SUCCESS;
    }

    let mut force_dimacs = false;
    let mut file: Option<String> = None;
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
            other if other.starts_with('-') => {
                eprintln!("z3rs: unknown option {other:?}");
                return ExitCode::from(1);
            }
            other => file = Some(other.to_string()),
        }
    }

    match file {
        Some(path) if force_dimacs || path.ends_with(".cnf") || path.ends_with(".dimacs") => {
            run_dimacs(&path)
        }
        Some(path) => {
            eprintln!("z3rs: don't know how to handle {path:?} yet (only DIMACS is wired up).");
            eprintln!("z3rs: use -dimacs for CNF; SMT-LIB2 support is coming. See ROADMAP.md.");
            ExitCode::from(1)
        }
        None => {
            print_usage();
            ExitCode::SUCCESS
        }
    }
}
