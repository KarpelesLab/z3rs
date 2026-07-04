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

use crate::cmd_context::{Session, run_smt2};

/// Read a C string argument as `&str`, returning `None` if NULL or not UTF-8.
///
/// # Safety
/// `p` must be NULL or a valid pointer to a NUL-terminated C string.
unsafe fn c_str<'a>(p: *const c_char) -> Option<&'a str> {
    if p.is_null() {
        return None;
    }
    unsafe { CStr::from_ptr(p) }.to_str().ok()
}

/// Move a Rust `String` into a freshly allocated C string (NULL on interior NUL).
fn into_c_string(s: String) -> *mut c_char {
    match CString::new(s) {
        Ok(c) => c.into_raw(),
        Err(_) => ptr::null_mut(),
    }
}

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

/// Free a string returned by [`z3rs_eval_smtlib2_string`] or
/// [`z3rs_session_eval`]. NULL is ignored.
///
/// # Safety
/// `s` must be NULL or a pointer previously returned by one of those functions
/// and not yet freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn z3rs_string_free(s: *mut c_char) {
    if !s.is_null() {
        drop(unsafe { CString::from_raw(s) });
    }
}

// --- Stateful solver session (incremental) --------------------------------

/// An opaque handle to a persistent [`Session`]. Create with
/// [`z3rs_mk_session`], drive with [`z3rs_session_eval`], free with
/// [`z3rs_del_session`].
pub struct Z3rsSession(Session);

/// Create a new, empty solver session.
#[unsafe(no_mangle)]
pub extern "C" fn z3rs_mk_session() -> *mut Z3rsSession {
    Box::into_raw(Box::new(Z3rsSession(Session::new())))
}

/// Evaluate more SMT-LIB2 `script` against the session's accumulated state
/// (declarations, assertions, push/pop stack all persist across calls). Returns
/// a newly allocated C string with one response line per output-producing
/// command (newline-separated; empty string if none), an `(error "…")` line on
/// a parse/eval error, or NULL on a NULL argument or invalid UTF-8. Free the
/// result with [`z3rs_string_free`].
///
/// # Safety
/// `s` must be a valid session handle; `script` a NULL or valid C string.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn z3rs_session_eval(
    s: *mut Z3rsSession,
    script: *const c_char,
) -> *mut c_char {
    if s.is_null() {
        return ptr::null_mut();
    }
    let session = unsafe { &mut *s };
    let Some(text) = (unsafe { c_str(script) }) else {
        return ptr::null_mut();
    };
    let out = match session.0.eval(text) {
        Ok(lines) => lines.join("\n"),
        Err(e) => alloc::format!("(error \"{e}\")"),
    };
    into_c_string(out)
}

/// Free a session created by [`z3rs_mk_session`]. NULL is ignored.
///
/// # Safety
/// `s` must be NULL or a handle from [`z3rs_mk_session`] not yet freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn z3rs_del_session(s: *mut Z3rsSession) {
    if !s.is_null() {
        drop(unsafe { Box::from_raw(s) });
    }
}
