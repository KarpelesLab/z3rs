//! The C ABI for z3rs — a thin, `unsafe`-only layer exposing the SMT-LIB2 entry
//! point to C callers. This mirrors Z3's `Z3_eval_smtlib2_string` (`z3/src/api`,
//! Z3 4.17.0, MIT): parse and evaluate a script, returning its responses.
//!
//! This is the only module that uses `unsafe`. It is gated behind the `ffi`
//! feature (which turns on `std` for `CStr`/`CString`); the reasoning core stays
//! pure, safe, and `no_std`.
//!
//! ```c
//! #include "z3rs.h"
//! char *out = z3rs_eval_smtlib2_string("(assert true)(check-sat)");
//! puts(out);              // -> "sat"
//! z3rs_string_free(out);
//! ```

use core::ffi::c_char;
use core::ptr;
use std::ffi::{CStr, CString};

use crate::cmd_context::run_smt2;

/// The z3rs version string (`env!("CARGO_PKG_VERSION")`), NUL-terminated and
/// statically owned — do **not** free it.
#[unsafe(no_mangle)]
pub extern "C" fn z3rs_version() -> *const c_char {
    concat!(env!("CARGO_PKG_VERSION"), "\0").as_ptr() as *const c_char
}

/// Evaluate an SMT-LIB 2 (or 1.2) `script` given as a NUL-terminated UTF-8 C
/// string. Returns a newly allocated C string with one response line per
/// `check-sat` (newline-separated), or a single `(error "…")` line on a parse
/// error. Returns NULL if `script` is NULL or not valid UTF-8. The result must
/// be released with [`z3rs_string_free`].
///
/// # Safety
/// `script` must be NULL or a valid pointer to a NUL-terminated C string that
/// stays valid for the duration of the call.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn z3rs_eval_smtlib2_string(script: *const c_char) -> *mut c_char {
    if script.is_null() {
        return ptr::null_mut();
    }
    let text = match unsafe { CStr::from_ptr(script) }.to_str() {
        Ok(s) => s,
        Err(_) => return ptr::null_mut(),
    };
    let out = match run_smt2(text) {
        Ok(lines) => lines.join("\n"),
        Err(e) => alloc::format!("(error \"{e}\")"),
    };
    // `out` never contains an interior NUL (verdicts/errors are plain text), but
    // fall back to NULL rather than panicking if it somehow does.
    match CString::new(out) {
        Ok(c) => c.into_raw(),
        Err(_) => ptr::null_mut(),
    }
}

/// Free a string returned by [`z3rs_eval_smtlib2_string`]. NULL is ignored.
///
/// # Safety
/// `s` must be NULL or a pointer previously returned by
/// [`z3rs_eval_smtlib2_string`] and not yet freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn z3rs_string_free(s: *mut c_char) {
    if !s.is_null() {
        drop(unsafe { CString::from_raw(s) });
    }
}
