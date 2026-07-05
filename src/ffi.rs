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

use crate::api::build::{Ast, Context as BuildContext, FuncDecl, Sort};
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
    func_decls: alloc::vec::Vec<alloc::boxed::Box<FuncDecl>>,
    solvers: alloc::vec::Vec<alloc::boxed::Box<Z3rsSolver>>,
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
    fn intern_func_decl(&mut self, d: FuncDecl) -> *const FuncDecl {
        let boxed = alloc::boxed::Box::new(d);
        let ptr: *const FuncDecl = &*boxed;
        self.func_decls.push(boxed);
        ptr
    }
}

/// `Z3_solver` — an independent solver: its own [`Session`] (assertions and
/// push/pop stack), seeded on demand with the context's declarations. Multiple
/// solvers in one context therefore do not share assertions, matching Z3.
pub struct Z3rsSolver {
    session: Session,
    /// Number of scopes entered by `push` and not yet `pop`ped.
    scopes: u32,
    /// How many of the context's declaration commands have been replayed.
    decl_watermark: usize,
}

impl Z3rsSolver {
    fn new() -> Z3rsSolver {
        Z3rsSolver {
            session: Session::new(),
            scopes: 0,
            decl_watermark: 0,
        }
    }
    /// Replay any context declarations this solver has not yet seen.
    fn sync(&mut self, decls: &[String]) {
        while self.decl_watermark < decls.len() {
            let _ = self.session.eval(&decls[self.decl_watermark]);
            self.decl_watermark += 1;
        }
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
        func_decls: alloc::vec::Vec::new(),
        solvers: alloc::vec::Vec::new(),
        strings: alloc::vec::Vec::new(),
        last: None,
    }))
}

/// `Z3_mk_context_rc(cfg)` — create a reference-counted context. In z3rs all
/// handles live in context-owned arenas freed at [`Z3_del_context`], so the
/// reference-counting variant is identical to [`Z3_mk_context`]; the `_rc`
/// name exists purely so clients that call it (and the `inc_ref`/`dec_ref`
/// no-ops) link and run.
///
/// # Safety
/// `cfg` must be NULL or a valid [`Z3_mk_config`] handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_context_rc(cfg: *mut Z3rsZ3Config) -> *mut Z3rsZ3Context {
    unsafe { Z3_mk_context(cfg) }
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
/// `Z3_func_decl` — an opaque function-declaration handle.
pub type Z3rsFuncDecl = FuncDecl;

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
    unsafe { mk_nary(c, num, args, "0", Sort::Int, |a, b| a.add(b)) }
}
/// # Safety
/// See [`Z3_mk_add`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_mul(
    c: *mut Z3rsZ3Context,
    num: u32,
    args: *const *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_nary(c, num, args, "1", Sort::Int, |a, b| a.mul(b)) }
}
/// # Safety
/// See [`Z3_mk_add`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_sub(
    c: *mut Z3rsZ3Context,
    num: u32,
    args: *const *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_nary(c, num, args, "0", Sort::Int, |a, b| a.sub(b)) }
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
    unsafe { mk_nary(c, num, args, "true", Sort::Bool, |a, b| a.and(b)) }
}
/// # Safety
/// See [`Z3_mk_add`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_or(
    c: *mut Z3rsZ3Context,
    num: u32,
    args: *const *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_nary(c, num, args, "false", Sort::Bool, |a, b| a.or(b)) }
}

/// Fold `num` argument terms with `fold`. With `num == 0` the identity term
/// (`identity`/`id_sort`) is returned — matching Z3, which yields `true`/`false`
/// for empty `and`/`or` and `0`/`1` for empty `add`/`mul` rather than failing.
unsafe fn mk_nary(
    c: *mut Z3rsZ3Context,
    num: u32,
    args: *const *const Z3rsAst,
    identity: &str,
    id_sort: Sort,
    fold: impl Fn(&Ast, &Ast) -> Ast,
) -> *const Z3rsAst {
    if c.is_null() {
        return ptr::null();
    }
    if num == 0 {
        return unsafe { &mut *c }.intern_ast(Ast::new(identity.to_string(), id_sort));
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

/// `Z3_mk_solver(c)` / `Z3_mk_simple_solver(c)` — a fresh, independent solver
/// with its own assertion set and push/pop stack (seeded on demand with the
/// context's declarations). Two solvers in one context do not share assertions.
///
/// # Safety
/// `c` must be a valid context handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_solver(c: *mut Z3rsZ3Context) -> *const Z3rsSolver {
    if c.is_null() {
        return ptr::null();
    }
    let ctx = unsafe { &mut *c };
    let boxed = alloc::boxed::Box::new(Z3rsSolver::new());
    let ptr: *const Z3rsSolver = &*boxed;
    ctx.solvers.push(boxed);
    ptr
}

/// `Z3_mk_simple_solver(c)` — see [`Z3_mk_solver`].
///
/// # Safety
/// `c` must be a valid context handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_simple_solver(c: *mut Z3rsZ3Context) -> *const Z3rsSolver {
    unsafe { Z3_mk_solver(c) }
}

/// Snapshot the context's declaration commands (used to seed a solver session).
///
/// # Safety
/// `c` must be NULL or a valid context handle.
unsafe fn ctx_decls(c: *mut Z3rsZ3Context) -> alloc::vec::Vec<String> {
    if c.is_null() {
        return alloc::vec::Vec::new();
    }
    unsafe { &*c }.build.declarations().to_vec()
}

/// Borrow a solver handle mutably.
///
/// # Safety
/// `s` must be NULL or a valid solver handle from this context.
unsafe fn solver_mut<'a>(s: *const Z3rsSolver) -> Option<&'a mut Z3rsSolver> {
    if s.is_null() {
        None
    } else {
        Some(unsafe { &mut *(s as *mut Z3rsSolver) })
    }
}

/// Map a `check-sat` response line to a `Z3_lbool` (`1`/`-1`/`0`).
fn lbool_of(lines: Result<alloc::vec::Vec<String>, String>) -> i32 {
    match lines.ok().and_then(|l| l.into_iter().next()).as_deref() {
        Some("sat") => 1,
        Some("unsat") => -1,
        _ => 0,
    }
}

/// `Z3_solver_assert(c, s, a)` — assert term `a` in solver `s`.
///
/// # Safety
/// `c` valid context; `s` a solver from this context; `a` a valid `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_solver_assert(
    c: *mut Z3rsZ3Context,
    s: *const Z3rsSolver,
    a: *const Z3rsAst,
) {
    if a.is_null() {
        return;
    }
    let decls = unsafe { ctx_decls(c) };
    let Some(sol) = (unsafe { solver_mut(s) }) else {
        return;
    };
    sol.sync(&decls);
    let src = unsafe { &*a }.to_smt();
    let _ = sol.session.eval(&alloc::format!("(assert {src})"));
}

/// `Z3_solver_assert_and_track(c, s, a, p)` — assert `a`, tracked by the Boolean
/// literal `p` for unsat-core extraction (`(assert (! a :named p))`).
///
/// # Safety
/// `c` valid context; `s` a solver; `a`, `p` valid `Z3_ast` (p a Bool const).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_solver_assert_and_track(
    c: *mut Z3rsZ3Context,
    s: *const Z3rsSolver,
    a: *const Z3rsAst,
    p: *const Z3rsAst,
) {
    if a.is_null() || p.is_null() {
        return;
    }
    let decls = unsafe { ctx_decls(c) };
    let Some(sol) = (unsafe { solver_mut(s) }) else {
        return;
    };
    sol.sync(&decls);
    let src = unsafe { &*a }.to_smt();
    let name = unsafe { &*p }.to_smt();
    let _ = sol.session.eval("(set-option :produce-unsat-cores true)");
    let _ = sol
        .session
        .eval(&alloc::format!("(assert (! {src} :named {name}))"));
}

/// `Z3_solver_check(c, s)` — decide solver `s`'s assertions, returning a
/// `Z3_lbool`: `1` = sat (`Z3_L_TRUE`), `-1` = unsat (`Z3_L_FALSE`), `0` =
/// unknown (`Z3_L_UNDEF`).
///
/// # Safety
/// `c` valid context; `s` a solver from this context.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_solver_check(c: *mut Z3rsZ3Context, s: *const Z3rsSolver) -> i32 {
    let decls = unsafe { ctx_decls(c) };
    let Some(sol) = (unsafe { solver_mut(s) }) else {
        return 0;
    };
    sol.sync(&decls);
    lbool_of(sol.session.eval("(check-sat)"))
}

/// `Z3_solver_check_assumptions(c, s, num, assumptions)` — decide `s`'s
/// assertions together with the given literal assumptions
/// (`(check-sat-assuming (a₁ … aₙ))`). Returns a `Z3_lbool`.
///
/// # Safety
/// `c` valid context; `s` a solver; `assumptions` points to `num` valid handles.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_solver_check_assumptions(
    c: *mut Z3rsZ3Context,
    s: *const Z3rsSolver,
    num: u32,
    assumptions: *const *const Z3rsAst,
) -> i32 {
    let decls = unsafe { ctx_decls(c) };
    let Some(sol) = (unsafe { solver_mut(s) }) else {
        return 0;
    };
    sol.sync(&decls);
    let joined = if num == 0 {
        String::new()
    } else {
        let Some(items) = (unsafe { read_args(num, assumptions) }) else {
            return 0;
        };
        let parts: alloc::vec::Vec<&str> = items.iter().map(|a| a.to_smt()).collect();
        parts.join(" ")
    };
    lbool_of(
        sol.session
            .eval(&alloc::format!("(check-sat-assuming ({joined}))")),
    )
}

/// `Z3_solver_push(c, s)` — enter a new assertion scope.
///
/// # Safety
/// `c` valid context; `s` a solver from this context.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_solver_push(c: *mut Z3rsZ3Context, s: *const Z3rsSolver) {
    let decls = unsafe { ctx_decls(c) };
    let Some(sol) = (unsafe { solver_mut(s) }) else {
        return;
    };
    sol.sync(&decls);
    if sol.session.eval("(push)").is_ok() {
        sol.scopes += 1;
    }
}

/// `Z3_solver_pop(c, s, n)` — discard the `n` innermost assertion scopes.
///
/// # Safety
/// `c` valid context; `s` a solver from this context.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_solver_pop(c: *mut Z3rsZ3Context, s: *const Z3rsSolver, n: u32) {
    let _ = c;
    let Some(sol) = (unsafe { solver_mut(s) }) else {
        return;
    };
    let n = n.min(sol.scopes);
    if n > 0 && sol.session.eval(&alloc::format!("(pop {n})")).is_ok() {
        sol.scopes -= n;
    }
}

/// `Z3_solver_get_num_scopes(c, s)` — the number of open `push` scopes.
///
/// # Safety
/// `c` valid context; `s` a solver from this context.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_solver_get_num_scopes(
    c: *mut Z3rsZ3Context,
    s: *const Z3rsSolver,
) -> u32 {
    let _ = c;
    match unsafe { solver_mut(s) } {
        Some(sol) => sol.scopes,
        None => 0,
    }
}

/// `Z3_solver_reset(c, s)` — drop all of `s`'s assertions and scopes (its
/// declarations are re-seeded from the context on the next use).
///
/// # Safety
/// `c` valid context; `s` a solver from this context.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_solver_reset(c: *mut Z3rsZ3Context, s: *const Z3rsSolver) {
    let _ = c;
    let Some(sol) = (unsafe { solver_mut(s) }) else {
        return;
    };
    sol.session = Session::new();
    sol.scopes = 0;
    sol.decl_watermark = 0;
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
    s: *const Z3rsSolver,
) -> *const Z3rsModel {
    if c.is_null() {
        return ptr::null();
    }
    let text = match unsafe { solver_mut(s) } {
        Some(sol) => sol
            .session
            .eval("(get-model)")
            .map(|l| l.join("\n"))
            .unwrap_or_default(),
        None => String::new(),
    };
    let ctx = unsafe { &mut *c };
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

// --- Reference-counting lifecycle (no-ops) ---------------------------------
//
// z3rs keeps every handle alive in context-owned arenas until `Z3_del_context`,
// so reference counting is unnecessary. These exist purely so RC-style clients
// (which bracket handle use with inc/dec_ref) link and run unchanged.

/// `Z3_inc_ref(c, a)` — no-op.
///
/// # Safety
/// Arguments are ignored; any pointer values are accepted.
#[unsafe(no_mangle)]
pub extern "C" fn Z3_inc_ref(_c: *mut Z3rsZ3Context, _a: *const Z3rsAst) {}
/// `Z3_dec_ref(c, a)` — no-op.
///
/// # Safety
/// Arguments are ignored.
#[unsafe(no_mangle)]
pub extern "C" fn Z3_dec_ref(_c: *mut Z3rsZ3Context, _a: *const Z3rsAst) {}
/// `Z3_solver_inc_ref(c, s)` — no-op.
#[unsafe(no_mangle)]
pub extern "C" fn Z3_solver_inc_ref(_c: *mut Z3rsZ3Context, _s: *const Z3rsSolver) {}
/// `Z3_solver_dec_ref(c, s)` — no-op.
#[unsafe(no_mangle)]
pub extern "C" fn Z3_solver_dec_ref(_c: *mut Z3rsZ3Context, _s: *const Z3rsSolver) {}
/// `Z3_model_inc_ref(c, m)` — no-op.
#[unsafe(no_mangle)]
pub extern "C" fn Z3_model_inc_ref(_c: *mut Z3rsZ3Context, _m: *const Z3rsModel) {}
/// `Z3_model_dec_ref(c, m)` — no-op.
#[unsafe(no_mangle)]
pub extern "C" fn Z3_model_dec_ref(_c: *mut Z3rsZ3Context, _m: *const Z3rsModel) {}

/// `Z3_get_version(major, minor, build, revision)` — write the emulated Z3
/// version (4.17.0.0). NULL out-pointers are skipped.
///
/// # Safety
/// Each non-NULL pointer must be writable.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_get_version(
    major: *mut u32,
    minor: *mut u32,
    build_number: *mut u32,
    revision_number: *mut u32,
) {
    unsafe {
        if !major.is_null() {
            *major = 4;
        }
        if !minor.is_null() {
            *minor = 17;
        }
        if !build_number.is_null() {
            *build_number = 0;
        }
        if !revision_number.is_null() {
            *revision_number = 0;
        }
    }
}

// --- Core constant / connective builders -----------------------------------

/// `Z3_mk_true(c)` / `Z3_mk_false(c)`.
///
/// # Safety
/// `c` must be a valid context handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_true(c: *mut Z3rsZ3Context) -> *const Z3rsAst {
    unsafe { mk_ast(c, Ast::new("true".to_string(), Sort::Bool)) }
}
/// # Safety
/// `c` must be a valid context handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_false(c: *mut Z3rsZ3Context) -> *const Z3rsAst {
    unsafe { mk_ast(c, Ast::new("false".to_string(), Sort::Bool)) }
}

unsafe fn mk_ast(c: *mut Z3rsZ3Context, a: Ast) -> *const Z3rsAst {
    if c.is_null() {
        return ptr::null();
    }
    unsafe { &mut *c }.intern_ast(a)
}

/// `Z3_mk_ite(c, cond, then, els)`.
///
/// # Safety
/// `c` valid context; all three `Z3_ast` valid handles.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_ite(
    c: *mut Z3rsZ3Context,
    t1: *const Z3rsAst,
    t2: *const Z3rsAst,
    t3: *const Z3rsAst,
) -> *const Z3rsAst {
    if c.is_null() || t1.is_null() || t2.is_null() || t3.is_null() {
        return ptr::null();
    }
    let res = unsafe { &*t1 }.ite(unsafe { &*t2 }, unsafe { &*t3 });
    unsafe { &mut *c }.intern_ast(res)
}

/// `Z3_mk_distinct(c, num, args)` — pairwise disequality.
///
/// # Safety
/// `c` valid context; `args` points to `num` valid handles.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_distinct(
    c: *mut Z3rsZ3Context,
    num: u32,
    args: *const *const Z3rsAst,
) -> *const Z3rsAst {
    if c.is_null() || num == 0 {
        return ptr::null();
    }
    let Some(items) = (unsafe { read_args(num, args) }) else {
        return ptr::null();
    };
    let res = Ast::distinct(&items);
    unsafe { &mut *c }.intern_ast(res)
}

/// `Z3_mk_iff(c, l, r)` / `Z3_mk_xor(c, l, r)` — Boolean equivalence / xor.
///
/// # Safety
/// See [`Z3_mk_lt`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_iff(
    c: *mut Z3rsZ3Context,
    l: *const Z3rsAst,
    r: *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_bin(c, l, r, |a, b| a.iff(b)) }
}
/// # Safety
/// See [`Z3_mk_lt`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_xor(
    c: *mut Z3rsZ3Context,
    l: *const Z3rsAst,
    r: *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_bin(c, l, r, |a, b| a.xor(b)) }
}

// --- More arithmetic --------------------------------------------------------

/// `Z3_mk_unary_minus(c, a)`.
///
/// # Safety
/// `c` valid context; `a` a valid `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_unary_minus(
    c: *mut Z3rsZ3Context,
    a: *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_un(c, a, |x| x.neg()) }
}
/// `Z3_mk_div` / `Z3_mk_mod` / `Z3_mk_rem` / `Z3_mk_power`.
///
/// # Safety
/// See [`Z3_mk_lt`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_div(
    c: *mut Z3rsZ3Context,
    l: *const Z3rsAst,
    r: *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_bin(c, l, r, |a, b| a.div(b)) }
}
/// # Safety
/// See [`Z3_mk_lt`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_mod(
    c: *mut Z3rsZ3Context,
    l: *const Z3rsAst,
    r: *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_bin(c, l, r, |a, b| a.modulo(b)) }
}
/// # Safety
/// See [`Z3_mk_lt`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_rem(
    c: *mut Z3rsZ3Context,
    l: *const Z3rsAst,
    r: *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_bin(c, l, r, |a, b| a.rem_(b)) }
}
/// # Safety
/// See [`Z3_mk_lt`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_power(
    c: *mut Z3rsZ3Context,
    l: *const Z3rsAst,
    r: *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_bin(c, l, r, |a, b| a.power(b)) }
}
/// `Z3_mk_int2real` / `Z3_mk_real2int` / `Z3_mk_is_int`.
///
/// # Safety
/// `c` valid context; `a` a valid `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_int2real(c: *mut Z3rsZ3Context, a: *const Z3rsAst) -> *const Z3rsAst {
    unsafe { mk_un(c, a, |x| x.int2real()) }
}
/// # Safety
/// `c` valid context; `a` a valid `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_real2int(c: *mut Z3rsZ3Context, a: *const Z3rsAst) -> *const Z3rsAst {
    unsafe { mk_un(c, a, |x| x.real2int()) }
}
/// # Safety
/// `c` valid context; `a` a valid `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_is_int(c: *mut Z3rsZ3Context, a: *const Z3rsAst) -> *const Z3rsAst {
    unsafe { mk_un(c, a, |x| x.is_int()) }
}
/// `Z3_mk_divides(c, t1, t2)` — `t1` divides `t2` (`t1` an integer numeral),
/// rendered `((_ divisible t1) t2)`.
///
/// # Safety
/// See [`Z3_mk_lt`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_divides(
    c: *mut Z3rsZ3Context,
    t1: *const Z3rsAst,
    t2: *const Z3rsAst,
) -> *const Z3rsAst {
    if c.is_null() || t1.is_null() || t2.is_null() {
        return ptr::null();
    }
    let k = unsafe { &*t1 }.to_smt();
    let t = unsafe { &*t2 }.to_smt();
    let res = Ast::new(alloc::format!("((_ divisible {k}) {t})"), Sort::Bool);
    unsafe { &mut *c }.intern_ast(res)
}

/// Apply a unary term operator, NULL-safe.
///
/// # Safety
/// `c` valid context; `a` a valid `Z3_ast`.
unsafe fn mk_un(
    c: *mut Z3rsZ3Context,
    a: *const Z3rsAst,
    op: impl Fn(&Ast) -> Ast,
) -> *const Z3rsAst {
    if c.is_null() || a.is_null() {
        return ptr::null();
    }
    let res = op(unsafe { &*a });
    unsafe { &mut *c }.intern_ast(res)
}

// --- Bit-vector operators ---------------------------------------------------

macro_rules! bv_binop {
    ($name:ident, $method:ident) => {
        /// # Safety
        /// `c` valid context; `l`/`r` valid `Z3_ast` handles.
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $name(
            c: *mut Z3rsZ3Context,
            l: *const Z3rsAst,
            r: *const Z3rsAst,
        ) -> *const Z3rsAst {
            unsafe { mk_bin(c, l, r, |a, b| a.$method(b)) }
        }
    };
}
macro_rules! bv_unop {
    ($name:ident, $method:ident) => {
        /// # Safety
        /// `c` valid context; `a` a valid `Z3_ast`.
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $name(
            c: *mut Z3rsZ3Context,
            a: *const Z3rsAst,
        ) -> *const Z3rsAst {
            unsafe { mk_un(c, a, |x| x.$method()) }
        }
    };
}

bv_binop!(Z3_mk_bvadd, bvadd);
bv_binop!(Z3_mk_bvsub, bvsub);
bv_binop!(Z3_mk_bvmul, bvmul);
bv_binop!(Z3_mk_bvudiv, bvudiv);
bv_binop!(Z3_mk_bvsdiv, bvsdiv);
bv_binop!(Z3_mk_bvurem, bvurem);
bv_binop!(Z3_mk_bvsrem, bvsrem);
bv_binop!(Z3_mk_bvsmod, bvsmod);
bv_binop!(Z3_mk_bvand, bvand);
bv_binop!(Z3_mk_bvor, bvor);
bv_binop!(Z3_mk_bvxor, bvxor);
bv_binop!(Z3_mk_bvnand, bvnand);
bv_binop!(Z3_mk_bvnor, bvnor);
bv_binop!(Z3_mk_bvxnor, bvxnor);
bv_binop!(Z3_mk_bvshl, bvshl);
bv_binop!(Z3_mk_bvlshr, bvlshr);
bv_binop!(Z3_mk_bvashr, bvashr);
bv_unop!(Z3_mk_bvnot, bvnot);
bv_unop!(Z3_mk_bvneg, bvneg);
bv_binop!(Z3_mk_bvult, bvult);
bv_binop!(Z3_mk_bvslt, bvslt);
bv_binop!(Z3_mk_bvule, bvule);
bv_binop!(Z3_mk_bvsle, bvsle);
bv_binop!(Z3_mk_bvugt, bvugt);
bv_binop!(Z3_mk_bvsgt, bvsgt);
bv_binop!(Z3_mk_bvuge, bvuge);
bv_binop!(Z3_mk_bvsge, bvsge);
bv_binop!(Z3_mk_concat, concat);

/// `Z3_mk_extract(c, high, low, a)` — bits `[high:low]`.
///
/// # Safety
/// `c` valid context; `a` a valid bit-vector `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_extract(
    c: *mut Z3rsZ3Context,
    high: u32,
    low: u32,
    a: *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_un(c, a, |x| x.extract(high, low)) }
}
/// `Z3_mk_sign_ext` / `Z3_mk_zero_ext` / `Z3_mk_repeat` — width `i` transforms.
///
/// # Safety
/// `c` valid context; `a` a valid bit-vector `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_sign_ext(
    c: *mut Z3rsZ3Context,
    i: u32,
    a: *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_un(c, a, |x| x.sign_ext(i)) }
}
/// # Safety
/// `c` valid context; `a` a valid bit-vector `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_zero_ext(
    c: *mut Z3rsZ3Context,
    i: u32,
    a: *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_un(c, a, |x| x.zero_ext(i)) }
}
/// # Safety
/// `c` valid context; `a` a valid bit-vector `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_repeat(
    c: *mut Z3rsZ3Context,
    i: u32,
    a: *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_un(c, a, |x| x.repeat(i)) }
}
/// `Z3_mk_rotate_left` / `Z3_mk_rotate_right`.
///
/// # Safety
/// `c` valid context; `a` a valid bit-vector `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_rotate_left(
    c: *mut Z3rsZ3Context,
    i: u32,
    a: *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_un(c, a, |x| x.rotate_left(i)) }
}
/// # Safety
/// `c` valid context; `a` a valid bit-vector `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_rotate_right(
    c: *mut Z3rsZ3Context,
    i: u32,
    a: *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_un(c, a, |x| x.rotate_right(i)) }
}
/// `Z3_mk_int2bv(c, n, a)` — integer `a` to a width-`n` bit-vector.
///
/// # Safety
/// `c` valid context; `a` a valid integer `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_int2bv(
    c: *mut Z3rsZ3Context,
    n: u32,
    a: *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_un(c, a, |x| x.int2bv(n)) }
}
/// `Z3_mk_bv2int(c, a, is_signed)` — bit-vector `a` to an integer.
///
/// # Safety
/// `c` valid context; `a` a valid bit-vector `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_bv2int(
    c: *mut Z3rsZ3Context,
    a: *const Z3rsAst,
    is_signed: bool,
) -> *const Z3rsAst {
    unsafe { mk_un(c, a, |x| x.bv2int(is_signed)) }
}

// --- Numerals ---------------------------------------------------------------

/// Render an integer decimal (negatives as `(- n)`), or a bit-vector literal
/// (value taken modulo 2^width) when `sort` is a bit-vector.
fn numeral_ast(v: i128, sort: &Sort) -> Ast {
    match sort {
        Sort::BitVec(w) => {
            let u: u128 = if *w == 0 {
                0
            } else if *w >= 128 {
                v as u128
            } else {
                (v.rem_euclid(1i128 << *w)) as u128
            };
            Ast::new(alloc::format!("(_ bv{u} {w})"), sort.clone())
        }
        _ => Ast::new(int_text(v), sort.clone()),
    }
}

/// An integer as SMT-LIB text: negatives render as `(- n)`.
fn int_text(v: i128) -> String {
    if v < 0 {
        alloc::format!("(- {})", -v)
    } else {
        v.to_string()
    }
}

/// `Z3_mk_int(c, v, ty)`.
///
/// # Safety
/// `c` valid context; `ty` a valid sort handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_int(
    c: *mut Z3rsZ3Context,
    v: i32,
    ty: *const Z3rsSort,
) -> *const Z3rsAst {
    unsafe { mk_numeral_val(c, v as i128, ty) }
}
/// `Z3_mk_unsigned_int(c, v, ty)`.
///
/// # Safety
/// `c` valid context; `ty` a valid sort handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_unsigned_int(
    c: *mut Z3rsZ3Context,
    v: u32,
    ty: *const Z3rsSort,
) -> *const Z3rsAst {
    unsafe { mk_numeral_val(c, v as i128, ty) }
}
/// `Z3_mk_int64(c, v, ty)`.
///
/// # Safety
/// `c` valid context; `ty` a valid sort handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_int64(
    c: *mut Z3rsZ3Context,
    v: i64,
    ty: *const Z3rsSort,
) -> *const Z3rsAst {
    unsafe { mk_numeral_val(c, v as i128, ty) }
}
/// `Z3_mk_unsigned_int64(c, v, ty)`.
///
/// # Safety
/// `c` valid context; `ty` a valid sort handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_unsigned_int64(
    c: *mut Z3rsZ3Context,
    v: u64,
    ty: *const Z3rsSort,
) -> *const Z3rsAst {
    unsafe { mk_numeral_val(c, v as i128, ty) }
}

unsafe fn mk_numeral_val(
    c: *mut Z3rsZ3Context,
    v: i128,
    ty: *const Z3rsSort,
) -> *const Z3rsAst {
    if c.is_null() || ty.is_null() {
        return ptr::null();
    }
    let sort = unsafe { &*ty }.clone();
    unsafe { &mut *c }.intern_ast(numeral_ast(v, &sort))
}

/// `Z3_mk_real(c, num, den)` — the rational `num/den`, as a `Real`.
///
/// # Safety
/// `c` must be a valid context handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_real(c: *mut Z3rsZ3Context, num: i32, den: i32) -> *const Z3rsAst {
    if c.is_null() {
        return ptr::null();
    }
    let src = if den == 1 {
        alloc::format!("(/ {} 1)", int_text(num as i128))
    } else {
        alloc::format!("(/ {} {})", int_text(num as i128), int_text(den as i128))
    };
    unsafe { &mut *c }.intern_ast(Ast::new(src, Sort::Real))
}

// --- Uninterpreted functions ------------------------------------------------

/// `Z3_mk_func_decl(c, name, domain_size, domain, range)` — declare an
/// uninterpreted function; apply it with [`Z3_mk_app`].
///
/// # Safety
/// `c` valid context; `domain` points to `domain_size` valid sort handles;
/// `range` a valid sort handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_func_decl(
    c: *mut Z3rsZ3Context,
    name: *const Z3rsSymbol,
    domain_size: u32,
    domain: *const *const Z3rsSort,
    range: *const Z3rsSort,
) -> *const Z3rsFuncDecl {
    if c.is_null() || range.is_null() {
        return ptr::null();
    }
    let name = unsafe { c_str(name) }.unwrap_or("");
    let mut doms = alloc::vec::Vec::with_capacity(domain_size as usize);
    if domain_size > 0 {
        if domain.is_null() {
            return ptr::null();
        }
        for i in 0..domain_size as isize {
            let p = unsafe { *domain.offset(i) };
            if p.is_null() {
                return ptr::null();
            }
            doms.push(unsafe { &*p }.clone());
        }
    }
    let range = unsafe { &*range }.clone();
    let ctx = unsafe { &mut *c };
    let fd = ctx.build.declare_func(name, doms, range);
    ctx.intern_func_decl(fd)
}

/// `Z3_mk_app(c, d, num_args, args)` — apply a function declaration.
///
/// # Safety
/// `c` valid context; `d` a func-decl from this context; `args` points to
/// `num_args` valid handles.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_app(
    c: *mut Z3rsZ3Context,
    d: *const Z3rsFuncDecl,
    num_args: u32,
    args: *const *const Z3rsAst,
) -> *const Z3rsAst {
    if c.is_null() || d.is_null() {
        return ptr::null();
    }
    let items = if num_args == 0 {
        alloc::vec::Vec::new()
    } else {
        let Some(v) = (unsafe { read_args(num_args, args) }) else {
            return ptr::null();
        };
        v
    };
    let res = unsafe { &*d }.apply(&items);
    unsafe { &mut *c }.intern_ast(res)
}

/// `Z3_mk_fresh_const(c, prefix, ty)` — a uniquely-named constant of sort `ty`.
///
/// # Safety
/// `c` valid context; `ty` a valid sort handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_fresh_const(
    c: *mut Z3rsZ3Context,
    prefix: *const c_char,
    ty: *const Z3rsSort,
) -> *const Z3rsAst {
    if c.is_null() || ty.is_null() {
        return ptr::null();
    }
    let prefix = unsafe { c_str(prefix) }.unwrap_or("fresh");
    let sort = unsafe { &*ty }.clone();
    let ctx = unsafe { &mut *c };
    let ast = ctx.build.fresh_const(prefix, sort);
    ctx.intern_ast(ast)
}

// --- Arrays -----------------------------------------------------------------

/// `Z3_mk_array_sort(c, domain, range)`.
///
/// # Safety
/// `c` valid context; `domain`/`range` valid sort handles.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_array_sort(
    c: *mut Z3rsZ3Context,
    domain: *const Z3rsSort,
    range: *const Z3rsSort,
) -> *const Z3rsSort {
    if c.is_null() || domain.is_null() || range.is_null() {
        return ptr::null();
    }
    let d = unsafe { &*domain }.clone();
    let r = unsafe { &*range }.clone();
    let s = Sort::Array(alloc::boxed::Box::new(d), alloc::boxed::Box::new(r));
    unsafe { &mut *c }.intern_sort(s)
}

/// `Z3_mk_uninterpreted_sort(c, name)` — declare an arity-0 uninterpreted sort.
///
/// # Safety
/// `c` valid context; `name` a valid `Z3_symbol`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_uninterpreted_sort(
    c: *mut Z3rsZ3Context,
    name: *const Z3rsSymbol,
) -> *const Z3rsSort {
    if c.is_null() {
        return ptr::null();
    }
    let name = unsafe { c_str(name) }.unwrap_or("");
    let ctx = unsafe { &mut *c };
    let s = ctx.build.declare_sort(name);
    ctx.intern_sort(s)
}

/// `Z3_mk_select(c, a, i)` — read array `a` at index `i`.
///
/// # Safety
/// See [`Z3_mk_lt`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_select(
    c: *mut Z3rsZ3Context,
    a: *const Z3rsAst,
    i: *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_bin(c, a, i, |x, y| x.select(y)) }
}

/// `Z3_mk_store(c, a, i, v)` — array `a` with index `i` updated to `v`.
///
/// # Safety
/// `c` valid context; all three `Z3_ast` valid handles.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_store(
    c: *mut Z3rsZ3Context,
    a: *const Z3rsAst,
    i: *const Z3rsAst,
    v: *const Z3rsAst,
) -> *const Z3rsAst {
    if c.is_null() || a.is_null() || i.is_null() || v.is_null() {
        return ptr::null();
    }
    let res = unsafe { &*a }.store(unsafe { &*i }, unsafe { &*v });
    unsafe { &mut *c }.intern_ast(res)
}

/// `Z3_mk_const_array(c, domain, v)` — the constant array mapping every index
/// of `domain` to `v`.
///
/// # Safety
/// `c` valid context; `domain` a sort handle; `v` a valid `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_const_array(
    c: *mut Z3rsZ3Context,
    domain: *const Z3rsSort,
    v: *const Z3rsAst,
) -> *const Z3rsAst {
    if c.is_null() || domain.is_null() || v.is_null() {
        return ptr::null();
    }
    let d = unsafe { &*domain }.clone();
    let res = BuildContext::const_array(d, unsafe { &*v });
    unsafe { &mut *c }.intern_ast(res)
}

// --- Sort / AST introspection ----------------------------------------------

/// `Z3_get_sort(c, a)` — the sort of term `a`.
///
/// # Safety
/// `c` valid context; `a` a valid `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_get_sort(c: *mut Z3rsZ3Context, a: *const Z3rsAst) -> *const Z3rsSort {
    if c.is_null() || a.is_null() {
        return ptr::null();
    }
    let s = unsafe { &*a }.sort().clone();
    unsafe { &mut *c }.intern_sort(s)
}

/// `Z3_get_sort_kind(c, s)` — the `Z3_sort_kind` tag (`UNINTERPRETED`=0,
/// `BOOL`=1, `INT`=2, `REAL`=3, `BV`=4, `ARRAY`=5).
///
/// # Safety
/// `s` must be NULL or a valid sort handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_get_sort_kind(_c: *mut Z3rsZ3Context, s: *const Z3rsSort) -> u32 {
    if s.is_null() {
        return 1000; // Z3_UNKNOWN_SORT
    }
    match unsafe { &*s } {
        Sort::Uninterpreted(_) => 0,
        Sort::Bool => 1,
        Sort::Int => 2,
        Sort::Real => 3,
        Sort::BitVec(_) => 4,
        Sort::Array(_, _) => 5,
    }
}

/// `Z3_get_bv_sort_size(c, s)` — the width of a bit-vector sort (0 otherwise).
///
/// # Safety
/// `s` must be NULL or a valid sort handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_get_bv_sort_size(_c: *mut Z3rsZ3Context, s: *const Z3rsSort) -> u32 {
    if s.is_null() {
        return 0;
    }
    unsafe { &*s }.bv_width().unwrap_or(0)
}

/// `Z3_get_array_sort_domain(c, s)` — the index sort of an array sort.
///
/// # Safety
/// `c` valid context; `s` a valid array sort handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_get_array_sort_domain(
    c: *mut Z3rsZ3Context,
    s: *const Z3rsSort,
) -> *const Z3rsSort {
    if c.is_null() || s.is_null() {
        return ptr::null();
    }
    match unsafe { &*s } {
        Sort::Array(d, _) => {
            let d = (**d).clone();
            unsafe { &mut *c }.intern_sort(d)
        }
        _ => ptr::null(),
    }
}

/// `Z3_get_array_sort_range(c, s)` — the element sort of an array sort.
///
/// # Safety
/// `c` valid context; `s` a valid array sort handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_get_array_sort_range(
    c: *mut Z3rsZ3Context,
    s: *const Z3rsSort,
) -> *const Z3rsSort {
    if c.is_null() || s.is_null() {
        return ptr::null();
    }
    match unsafe { &*s } {
        Sort::Array(_, r) => {
            let r = (**r).clone();
            unsafe { &mut *c }.intern_sort(r)
        }
        _ => ptr::null(),
    }
}

/// `Z3_get_bool_value(c, a)` — `Z3_lbool` for a Boolean literal: `1` for
/// `true`, `-1` for `false`, `0` (undef) otherwise.
///
/// # Safety
/// `a` must be NULL or a valid `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_get_bool_value(_c: *mut Z3rsZ3Context, a: *const Z3rsAst) -> i32 {
    if a.is_null() {
        return 0;
    }
    match unsafe { &*a }.to_smt() {
        "true" => 1,
        "false" => -1,
        _ => 0,
    }
}

/// `Z3_sort_to_string(c, s)` — the SMT-LIB rendering of a sort (context-owned;
/// do not free).
///
/// # Safety
/// `c` valid context; `s` a valid sort handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_sort_to_string(
    c: *mut Z3rsZ3Context,
    s: *const Z3rsSort,
) -> *const c_char {
    if c.is_null() || s.is_null() {
        return ptr::null();
    }
    let text = unsafe { &*s }.smt();
    let ctx = unsafe { &mut *c };
    intern_string(ctx, text)
}

/// `Z3_get_symbol_string(c, s)` — the name of a symbol. In z3rs a `Z3_symbol`
/// is already the interned C string, so this is the identity.
///
/// # Safety
/// `s` must be NULL or a valid `Z3_symbol`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_get_symbol_string(
    _c: *mut Z3rsZ3Context,
    s: *const Z3rsSymbol,
) -> *const c_char {
    s
}
