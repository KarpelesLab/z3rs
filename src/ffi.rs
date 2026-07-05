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

use crate::api::SatResult;
use crate::api::build::{Ast, Context as BuildContext, Sort};
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

/// Check satisfiability of the session's current assertions
/// (`(check-sat)`), returning `1` = sat, `0` = unsat, `-1` = unknown, and
/// `-2` on a NULL handle or internal error. A convenience wrapper over
/// [`z3rs_session_eval`] mirroring `Z3_solver_check`.
///
/// # Safety
/// `s` must be a valid session handle from [`z3rs_mk_session`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn z3rs_session_check(s: *mut Z3rsSession) -> i32 {
    if s.is_null() {
        return -2;
    }
    let session = unsafe { &mut *s };
    match session.0.eval("(check-sat)") {
        Ok(lines) => match lines.first().map(String::as_str) {
            Some("sat") => 1,
            Some("unsat") => 0,
            Some("unknown") => -1,
            _ => -2,
        },
        Err(_) => -2,
    }
}

/// Push a new assertion scope (`(push)`). Returns `0` on success, `-1` on error.
///
/// # Safety
/// `s` must be a valid session handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn z3rs_session_push(s: *mut Z3rsSession) -> i32 {
    unsafe { session_cmd(s, "(push)") }
}

/// Pop the innermost assertion scope (`(pop)`). Returns `0` / `-1`.
///
/// # Safety
/// `s` must be a valid session handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn z3rs_session_pop(s: *mut Z3rsSession) -> i32 {
    unsafe { session_cmd(s, "(pop)") }
}

/// Reset the session (`(reset)`), dropping all declarations and assertions.
/// Returns `0` / `-1`.
///
/// # Safety
/// `s` must be a valid session handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn z3rs_session_reset(s: *mut Z3rsSession) -> i32 {
    unsafe { session_cmd(s, "(reset)") }
}

/// Run a no-output session command, mapping success/failure to `0`/`-1`.
///
/// # Safety
/// `s` must be NULL or a valid session handle.
unsafe fn session_cmd(s: *mut Z3rsSession, cmd: &str) -> i32 {
    if s.is_null() {
        return -1;
    }
    let session = unsafe { &mut *s };
    match session.0.eval(cmd) {
        Ok(_) => 0,
        Err(_) => -1,
    }
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

// --- Z3-compatible C ABI slice --------------------------------------------
//
// A drop-in subset of Z3's own `z3_api.h` symbols (same names & ABI), so a C
// program written against Z3 that uses only this slice — configuration,
// context, and `Z3_eval_smtlib2_string` (whose state persists across calls,
// exactly as documented upstream) — links and runs against `libz3rs`. Pointer
// handles are opaque, matching Z3's `typedef struct _Z3_{config,context}*`.

/// Opaque configuration handle (Z3's `Z3_config`). Options are accepted but,
/// for now, ignored (the defaults match z3rs's behaviour).
pub struct Z3rsZ3Config;

/// Opaque context handle (Z3's `Z3_context`): a persistent expression-building
/// session, the arenas owning every `Z3_ast`/`Z3_sort`/`Z3_symbol` it hands out
/// (all freed together at [`Z3_del_context`]), and the buffer owning the most
/// recent `Z3_eval_smtlib2_string` result.
// The `Box` in each arena is REQUIRED, not redundant: we hand raw pointers to
// the boxed contents across the C ABI, and they must stay valid as the arena
// `Vec` grows. Without the `Box`, a reallocation would move the elements and
// dangle every previously-returned `Z3_ast`/`Z3_sort`/`Z3_solver`.
#[allow(clippy::vec_box)]
pub struct Z3rsZ3Context {
    build: BuildContext,
    asts: alloc::vec::Vec<alloc::boxed::Box<Ast>>,
    sorts: alloc::vec::Vec<alloc::boxed::Box<Sort>>,
    symbols: alloc::vec::Vec<CString>,
    solvers: alloc::vec::Vec<alloc::boxed::Box<u8>>,
    /// Context-owned string outputs (models, `ast_to_string`), stable until
    /// context deletion.
    strings: alloc::vec::Vec<CString>,
    last: Option<CString>,
}

impl Z3rsZ3Context {
    fn intern_ast(&mut self, a: Ast) -> *const Ast {
        let boxed = alloc::boxed::Box::new(a);
        let ptr: *const Ast = &*boxed;
        self.asts.push(boxed);
        ptr
    }
    fn intern_sort(&mut self, s: Sort) -> *const Sort {
        let boxed = alloc::boxed::Box::new(s);
        let ptr: *const Sort = &*boxed;
        self.sorts.push(boxed);
        ptr
    }
}

/// `Z3_mk_config()` — create a configuration object.
#[unsafe(no_mangle)]
pub extern "C" fn Z3_mk_config() -> *mut Z3rsZ3Config {
    Box::into_raw(Box::new(Z3rsZ3Config))
}

/// `Z3_del_config(c)` — free a configuration object. NULL is ignored.
///
/// # Safety
/// `c` must be NULL or a handle from [`Z3_mk_config`] not yet freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_del_config(c: *mut Z3rsZ3Config) {
    if !c.is_null() {
        drop(unsafe { Box::from_raw(c) });
    }
}

/// `Z3_mk_context(cfg)` — create a logical context from a configuration.
///
/// # Safety
/// `cfg` must be NULL or a valid [`Z3_mk_config`] handle (it is not consumed).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_context(_cfg: *mut Z3rsZ3Config) -> *mut Z3rsZ3Context {
    Box::into_raw(Box::new(Z3rsZ3Context {
        build: BuildContext::new(),
        asts: alloc::vec::Vec::new(),
        sorts: alloc::vec::Vec::new(),
        symbols: alloc::vec::Vec::new(),
        solvers: alloc::vec::Vec::new(),
        strings: alloc::vec::Vec::new(),
        last: None,
    }))
}

/// `Z3_del_context(c)` — free a logical context. NULL is ignored.
///
/// # Safety
/// `c` must be NULL or a handle from [`Z3_mk_context`] not yet freed.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_del_context(c: *mut Z3rsZ3Context) {
    if !c.is_null() {
        drop(unsafe { Box::from_raw(c) });
    }
}

/// `Z3_eval_smtlib2_string(c, str)` — parse and evaluate an SMT-LIB2 command
/// sequence against the context; state from previous calls is retained. Returns
/// a string **owned by the context** (valid until the next call on `c` or
/// [`Z3_del_context`]); the caller must **not** free it — matching Z3's
/// contract exactly.
///
/// # Safety
/// `c` must be a valid context handle; `str` a NULL or valid C string.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_eval_smtlib2_string(
    c: *mut Z3rsZ3Context,
    str: *const c_char,
) -> *const c_char {
    if c.is_null() {
        return ptr::null();
    }
    let ctx = unsafe { &mut *c };
    let text = unsafe { c_str(str) }.unwrap_or("");
    let out = match ctx.build.session_eval(text) {
        Ok(lines) => lines.join("\n"),
        Err(e) => alloc::format!("(error \"{e}\")"),
    };
    ctx.last = CString::new(out).ok();
    ctx.last
        .as_ref()
        .map(|s| s.as_ptr())
        .unwrap_or(ptr::null())
}

// --- Z3-compatible object (handle) API -------------------------------------
//
// The handle surface a Z3 C test program uses: build sorts/consts/terms through
// the context, then assert & check with a solver. `Z3_ast`/`Z3_sort` are opaque
// pointers into the context's arenas (freed at `Z3_del_context`); `Z3_symbol` is
// a context-owned C string; `Z3_solver` shares the context's session.

/// `Z3_symbol` — an interned name (context-owned C string).
pub type Z3rsSymbol = c_char;
/// `Z3_sort` — an opaque sort handle.
pub type Z3rsSort = Sort;
/// `Z3_ast` — an opaque term handle.
pub type Z3rsAst = Ast;
/// `Z3_solver` — an opaque solver handle (shares the context's session).
pub type Z3rsSolver = u8;

/// `Z3_mk_string_symbol(c, s)` — intern a name, returning a `Z3_symbol`.
///
/// # Safety
/// `c` must be a valid context; `s` a NUL-terminated C string.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_string_symbol(
    c: *mut Z3rsZ3Context,
    s: *const c_char,
) -> *const Z3rsSymbol {
    if c.is_null() {
        return ptr::null();
    }
    let ctx = unsafe { &mut *c };
    let name = unsafe { c_str(s) }.unwrap_or("");
    let cstr = match CString::new(name) {
        Ok(cs) => cs,
        Err(_) => return ptr::null(),
    };
    let ptr = cstr.as_ptr();
    ctx.symbols.push(cstr);
    ptr
}

/// `Z3_mk_int_sort(c)` / `Z3_mk_bool_sort(c)` / `Z3_mk_real_sort(c)` /
/// `Z3_mk_bv_sort(c, sz)` — the primitive sort constructors.
///
/// # Safety
/// `c` must be a valid context handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_int_sort(c: *mut Z3rsZ3Context) -> *const Z3rsSort {
    unsafe { mk_sort(c, Sort::Int) }
}
/// # Safety
/// `c` must be a valid context handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_bool_sort(c: *mut Z3rsZ3Context) -> *const Z3rsSort {
    unsafe { mk_sort(c, Sort::Bool) }
}
/// # Safety
/// `c` must be a valid context handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_real_sort(c: *mut Z3rsZ3Context) -> *const Z3rsSort {
    unsafe { mk_sort(c, Sort::Real) }
}
/// # Safety
/// `c` must be a valid context handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_bv_sort(c: *mut Z3rsZ3Context, sz: u32) -> *const Z3rsSort {
    unsafe { mk_sort(c, Sort::BitVec(sz)) }
}

unsafe fn mk_sort(c: *mut Z3rsZ3Context, s: Sort) -> *const Z3rsSort {
    if c.is_null() {
        return ptr::null();
    }
    unsafe { &mut *c }.intern_sort(s)
}

/// `Z3_mk_const(c, sym, sort)` — a constant of the given sort named by `sym`.
///
/// # Safety
/// All pointers must be valid handles from this context.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_const(
    c: *mut Z3rsZ3Context,
    sym: *const Z3rsSymbol,
    sort: *const Z3rsSort,
) -> *const Z3rsAst {
    if c.is_null() || sort.is_null() {
        return ptr::null();
    }
    let ctx = unsafe { &mut *c };
    let name = unsafe { c_str(sym) }.unwrap_or("");
    let sort = unsafe { &*sort }.clone();
    let ast = ctx.build.const_(name, sort);
    ctx.intern_ast(ast)
}

/// `Z3_mk_numeral(c, text, sort)` — a numeral of `sort` parsed from `text`.
///
/// # Safety
/// All pointers must be valid handles from this context.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_numeral(
    c: *mut Z3rsZ3Context,
    text: *const c_char,
    sort: *const Z3rsSort,
) -> *const Z3rsAst {
    if c.is_null() || sort.is_null() {
        return ptr::null();
    }
    let ctx = unsafe { &mut *c };
    let s = unsafe { c_str(text) }.unwrap_or("0");
    let sort = unsafe { &*sort }.clone();
    let ast = BuildContext::numeral(s, sort);
    ctx.intern_ast(ast)
}

/// Read an n-ary `Z3_ast const args[]` into a `Vec<&Ast>`.
///
/// # Safety
/// `args` must point to `num` valid `Z3_ast` handles.
unsafe fn read_args<'a>(num: u32, args: *const *const Z3rsAst) -> Option<alloc::vec::Vec<&'a Ast>> {
    if args.is_null() {
        return None;
    }
    let mut out = alloc::vec::Vec::with_capacity(num as usize);
    for i in 0..num as isize {
        let p = unsafe { *args.offset(i) };
        if p.is_null() {
            return None;
        }
        out.push(unsafe { &*p });
    }
    Some(out)
}

/// `Z3_mk_add` / `Z3_mk_mul` / `Z3_mk_sub` — n-ary arithmetic.
///
/// # Safety
/// `c` valid context; `args` points to `num` valid handles.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_add(
    c: *mut Z3rsZ3Context,
    num: u32,
    args: *const *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_nary(c, num, args, |a, b| a.add(b)) }
}
/// # Safety
/// See [`Z3_mk_add`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_mul(
    c: *mut Z3rsZ3Context,
    num: u32,
    args: *const *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_nary(c, num, args, |a, b| a.mul(b)) }
}
/// # Safety
/// See [`Z3_mk_add`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_sub(
    c: *mut Z3rsZ3Context,
    num: u32,
    args: *const *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_nary(c, num, args, |a, b| a.sub(b)) }
}
/// `Z3_mk_and` / `Z3_mk_or` — n-ary Boolean connectives.
///
/// # Safety
/// See [`Z3_mk_add`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_and(
    c: *mut Z3rsZ3Context,
    num: u32,
    args: *const *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_nary(c, num, args, |a, b| a.and(b)) }
}
/// # Safety
/// See [`Z3_mk_add`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_or(
    c: *mut Z3rsZ3Context,
    num: u32,
    args: *const *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_nary(c, num, args, |a, b| a.or(b)) }
}

unsafe fn mk_nary(
    c: *mut Z3rsZ3Context,
    num: u32,
    args: *const *const Z3rsAst,
    fold: impl Fn(&Ast, &Ast) -> Ast,
) -> *const Z3rsAst {
    if c.is_null() || num == 0 {
        return ptr::null();
    }
    let Some(items) = (unsafe { read_args(num, args) }) else {
        return ptr::null();
    };
    let mut acc = items[0].clone();
    for it in &items[1..] {
        acc = fold(&acc, it);
    }
    unsafe { &mut *c }.intern_ast(acc)
}

/// Binary comparison / equality / connective constructors.
///
/// # Safety
/// `c` valid context; `l`/`r` valid `Z3_ast` handles.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_lt(
    c: *mut Z3rsZ3Context,
    l: *const Z3rsAst,
    r: *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_bin(c, l, r, |a, b| a.lt(b)) }
}
/// # Safety
/// See [`Z3_mk_lt`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_le(
    c: *mut Z3rsZ3Context,
    l: *const Z3rsAst,
    r: *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_bin(c, l, r, |a, b| a.le(b)) }
}
/// # Safety
/// See [`Z3_mk_lt`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_gt(
    c: *mut Z3rsZ3Context,
    l: *const Z3rsAst,
    r: *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_bin(c, l, r, |a, b| a.gt(b)) }
}
/// # Safety
/// See [`Z3_mk_lt`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_ge(
    c: *mut Z3rsZ3Context,
    l: *const Z3rsAst,
    r: *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_bin(c, l, r, |a, b| a.ge(b)) }
}
/// # Safety
/// See [`Z3_mk_lt`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_eq(
    c: *mut Z3rsZ3Context,
    l: *const Z3rsAst,
    r: *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_bin(c, l, r, |a, b| a.eq(b)) }
}
/// `Z3_mk_implies`.
///
/// # Safety
/// See [`Z3_mk_lt`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_implies(
    c: *mut Z3rsZ3Context,
    l: *const Z3rsAst,
    r: *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_bin(c, l, r, |a, b| a.implies(b)) }
}

unsafe fn mk_bin(
    c: *mut Z3rsZ3Context,
    l: *const Z3rsAst,
    r: *const Z3rsAst,
    op: impl Fn(&Ast, &Ast) -> Ast,
) -> *const Z3rsAst {
    if c.is_null() || l.is_null() || r.is_null() {
        return ptr::null();
    }
    let res = op(unsafe { &*l }, unsafe { &*r });
    unsafe { &mut *c }.intern_ast(res)
}

/// `Z3_mk_not(c, a)`.
///
/// # Safety
/// `c` valid context; `a` a valid `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_not(c: *mut Z3rsZ3Context, a: *const Z3rsAst) -> *const Z3rsAst {
    if c.is_null() || a.is_null() {
        return ptr::null();
    }
    let res = unsafe { &*a }.not();
    unsafe { &mut *c }.intern_ast(res)
}

/// `Z3_mk_solver(c)` — a solver over the context's session.
///
/// # Safety
/// `c` must be a valid context handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_solver(c: *mut Z3rsZ3Context) -> *const Z3rsSolver {
    if c.is_null() {
        return ptr::null();
    }
    let ctx = unsafe { &mut *c };
    let marker = alloc::boxed::Box::new(0u8);
    let ptr: *const u8 = &*marker;
    ctx.solvers.push(marker);
    ptr
}

/// `Z3_solver_assert(c, s, a)` — assert term `a`.
///
/// # Safety
/// `c` valid context; `s` a solver from this context; `a` a valid `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_solver_assert(
    c: *mut Z3rsZ3Context,
    _s: *const Z3rsSolver,
    a: *const Z3rsAst,
) {
    if c.is_null() || a.is_null() {
        return;
    }
    let ctx = unsafe { &mut *c };
    let ast = unsafe { &*a }.clone();
    ctx.build.assert(&ast);
}

/// `Z3_solver_check(c, s)` — decide the asserted constraints, returning a
/// `Z3_lbool`: `1` = sat (`Z3_L_TRUE`), `-1` = unsat (`Z3_L_FALSE`), `0` =
/// unknown (`Z3_L_UNDEF`).
///
/// # Safety
/// `c` valid context; `s` a solver from this context.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_solver_check(c: *mut Z3rsZ3Context, _s: *const Z3rsSolver) -> i32 {
    if c.is_null() {
        return 0;
    }
    match unsafe { &mut *c }.build.check() {
        SatResult::Sat => 1,
        SatResult::Unsat => -1,
        SatResult::Unknown => 0,
    }
}

/// `Z3_model` — an opaque handle. Internally it is the stable pointer to the
/// context-owned model text (a `CString` buffer), so [`Z3_model_to_string`] is
/// the identity.
pub type Z3rsModel = c_char;

/// Intern a string in the context arena, returning a stable pointer to its
/// buffer. The buffer address is fixed for the context's lifetime even as the
/// arena `Vec` reallocates (only the `CString` structs move, not their buffers).
fn intern_string(ctx: &mut Z3rsZ3Context, s: String) -> *const c_char {
    match CString::new(s) {
        Ok(cs) => {
            let ptr = cs.as_ptr();
            ctx.strings.push(cs);
            ptr
        }
        Err(_) => ptr::null(),
    }
}

/// `Z3_solver_get_model(c, s)` — the model of the most recent satisfiable check,
/// as an opaque `Z3_model` handle (render it with [`Z3_model_to_string`]).
///
/// # Safety
/// `c` valid context; `s` a solver from this context.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_solver_get_model(
    c: *mut Z3rsZ3Context,
    _s: *const Z3rsSolver,
) -> *const Z3rsModel {
    if c.is_null() {
        return ptr::null();
    }
    let ctx = unsafe { &mut *c };
    let text = ctx
        .build
        .session_eval("(get-model)")
        .map(|l| l.join("\n"))
        .unwrap_or_default();
    intern_string(ctx, text)
}

/// `Z3_model_to_string(c, m)` — the SMT-LIB rendering of a model (context-owned;
/// do not free). The handle already points at the rendered text.
///
/// # Safety
/// `c` valid context; `m` a `Z3_model` from [`Z3_solver_get_model`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_model_to_string(
    _c: *mut Z3rsZ3Context,
    m: *const Z3rsModel,
) -> *const c_char {
    m
}

/// `Z3_ast_to_string(c, a)` — the SMT-LIB 2 rendering of a term (context-owned;
/// do not free).
///
/// # Safety
/// `c` valid context; `a` a valid `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_ast_to_string(
    c: *mut Z3rsZ3Context,
    a: *const Z3rsAst,
) -> *const c_char {
    if c.is_null() || a.is_null() {
        return ptr::null();
    }
    let s = unsafe { &*a }.to_smt().to_string();
    let ctx = unsafe { &mut *c };
    intern_string(ctx, s)
}

/// `Z3_get_full_version()` — the version string (statically owned; do not free).
#[unsafe(no_mangle)]
pub extern "C" fn Z3_get_full_version() -> *const c_char {
    concat!("z3rs ", env!("CARGO_PKG_VERSION"), " (Z3 4.17.0 compatible)\0").as_ptr()
        as *const c_char
}
