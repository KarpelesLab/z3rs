#![no_main]
//! Fuzz the SMT-LIB (v2 and v1) front end: arbitrary text must never panic —
//! it must parse-error, decide, or return `unknown`, but always terminate
//! cleanly. Guards the tokenizer, parser, term builder, and theory dispatch.
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &str| {
    let _ = z3rs::cmd_context::run_smt2(data);
});
