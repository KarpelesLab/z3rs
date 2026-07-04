#![no_main]
//! Fuzz the DIMACS CNF parser: arbitrary bytes must never panic.
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &str| {
    let _ = z3rs::sat::parse_dimacs(data);
});
