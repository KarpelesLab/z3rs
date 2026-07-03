//! `z3rs` command-line frontend — the pure-Rust counterpart of Z3's `shell`
//! (`z3/src/shell/main.cpp`). Aims for CLI compatibility with the `z3` binary.
//!
//! Frontends to port, mirroring `z3/src/shell/`:
//! - [ ] SMT-LIB2 (`smtlib_frontend.cpp`) — the default `-smt2` mode
//! - [ ] DIMACS (`dimacs_frontend.cpp`)   — `-dimacs`
//! - [ ] Datalog (`datalog_frontend.cpp`) — `-dl`
//! - [ ] DRAT (`drat_frontend.cpp`)       — `-drat`
//! - [ ] Z3 log replay (`z3_log_frontend.cpp`)
//! - [ ] Optimization (`opt_frontend.cpp`)

use std::process::ExitCode;

fn print_version() {
    println!(
        "z3rs version {} (pure-Rust port of Z3 {})",
        z3rs::VERSION,
        z3rs::Z3_UPSTREAM_VERSION
    );
}

fn print_usage() {
    println!("z3rs [options] [-file:]file");
    println!();
    println!("A pure-Rust, zero-dependency port of the Z3 theorem prover.");
    println!("This is an early scaffold — solving is not yet implemented.");
    println!();
    println!("Options:");
    println!("  -h, --help       print this message");
    println!("  --version        print version information");
    println!("  -smt2            read input as SMT-LIB2 (default for .smt2)  [TODO]");
    println!("  -in              read from stdin                              [TODO]");
    println!("  -dimacs          read input in DIMACS format                 [TODO]");
    println!("  -dl              read input as Datalog                        [TODO]");
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();

    if args.is_empty() {
        print_usage();
        return ExitCode::SUCCESS;
    }

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
            _ => {}
        }
    }

    // Until frontends are ported, fail loudly rather than pretending to solve.
    eprintln!("z3rs: solver frontends are not implemented yet (scaffold stage).");
    eprintln!("z3rs: see ROADMAP.md for the porting plan.");
    ExitCode::from(1)
}
