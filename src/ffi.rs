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
    models: alloc::vec::Vec<alloc::boxed::Box<Z3rsModel>>,
    ast_vectors: alloc::vec::Vec<alloc::boxed::Box<Z3rsAstVector>>,
    patterns: alloc::vec::Vec<alloc::boxed::Box<Z3rsPattern>>,
    constructors: alloc::vec::Vec<alloc::boxed::Box<Z3rsConstructor>>,
    constructor_lists: alloc::vec::Vec<alloc::boxed::Box<Z3rsConstructorList>>,
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
    fn intern_model(&mut self, m: Z3rsModel) -> *const Z3rsModel {
        let boxed = alloc::boxed::Box::new(m);
        let ptr: *const Z3rsModel = &*boxed;
        self.models.push(boxed);
        ptr
    }
    fn intern_ast_vector(&mut self, v: Z3rsAstVector) -> *const Z3rsAstVector {
        let boxed = alloc::boxed::Box::new(v);
        let ptr: *const Z3rsAstVector = &*boxed;
        self.ast_vectors.push(boxed);
        ptr
    }
    fn intern_pattern(&mut self, p: Z3rsPattern) -> *const Z3rsPattern {
        let boxed = alloc::boxed::Box::new(p);
        let ptr: *const Z3rsPattern = &*boxed;
        self.patterns.push(boxed);
        ptr
    }
    fn intern_constructor(&mut self, k: Z3rsConstructor) -> *const Z3rsConstructor {
        let boxed = alloc::boxed::Box::new(k);
        let ptr: *const Z3rsConstructor = &*boxed;
        self.constructors.push(boxed);
        ptr
    }
    fn intern_constructor_list(&mut self, l: Z3rsConstructorList) -> *const Z3rsConstructorList {
        let boxed = alloc::boxed::Box::new(l);
        let ptr: *const Z3rsConstructorList = &*boxed;
        self.constructor_lists.push(boxed);
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
    /// Assumptions asserted with [`Z3_solver_assert_and_track`], keyed by their
    /// `:named` label, so [`Z3_solver_get_unsat_core`] can map the printed core
    /// labels back to the tracking `Z3_ast`s.
    tracked: alloc::vec::Vec<(String, *const Ast)>,
}

impl Z3rsSolver {
    fn new() -> Z3rsSolver {
        Z3rsSolver {
            session: Session::new(),
            scopes: 0,
            decl_watermark: 0,
            tracked: alloc::vec::Vec::new(),
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
        models: alloc::vec::Vec::new(),
        ast_vectors: alloc::vec::Vec::new(),
        patterns: alloc::vec::Vec::new(),
        constructors: alloc::vec::Vec::new(),
        constructor_lists: alloc::vec::Vec::new(),
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
    ctx.last.as_ref().map(|s| s.as_ptr()).unwrap_or(ptr::null())
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
    let name = unsafe { &*p }.to_smt().to_string();
    let _ = sol.session.eval("(set-option :produce-unsat-cores true)");
    let _ = sol
        .session
        .eval(&alloc::format!("(assert (! {src} :named {name}))"));
    sol.tracked.push((name, p));
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
    sol.tracked.clear();
}

/// `Z3_model` — the model of a satisfiable check. It keeps the printed
/// `(get-model)` text (for [`Z3_model_to_string`]), the parsed 0-ary constant
/// `(name, sort)` entries (for [`Z3_model_get_num_consts`] /
/// [`Z3_model_get_const_decl`]), and a pointer to the [`Z3rsSolver`] that
/// produced it so [`Z3_model_eval`] / [`Z3_model_get_const_interp`] can re-query
/// values with `(get-value …)`.
pub struct Z3rsModel {
    text: CString,
    consts: alloc::vec::Vec<(String, Sort)>,
    solver: *const Z3rsSolver,
}

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
    let consts = parse_model_consts(&text);
    let model = Z3rsModel {
        text: CString::new(text).unwrap_or_default(),
        consts,
        solver: s,
    };
    unsafe { &mut *c }.intern_model(model)
}

/// Parse the `(define-fun name () Sort value)` lines of a printed model into
/// `(name, sort)` pairs for the 0-ary constants, in order.
fn parse_model_consts(text: &str) -> alloc::vec::Vec<(String, Sort)> {
    let mut out = alloc::vec::Vec::new();
    // Each definition is a balanced `(define-fun name () Sort body)` block that may
    // span several lines (z3 puts the body on its own indented line), so scan for
    // balanced blocks rather than parsing line-by-line.
    let mut search = 0;
    while let Some(rel) = text[search..].find("(define-fun") {
        let start = search + rel;
        let mut depth = 0i32;
        let mut end = start;
        for (j, c) in text[start..].char_indices() {
            match c {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        end = start + j;
                        break;
                    }
                }
                _ => {}
            }
        }
        search = end + 1;
        let Some(inner) = text[start..=end]
            .strip_prefix('(')
            .and_then(|r| r.strip_suffix(')'))
        else {
            continue;
        };
        // Collapse whitespace (including the body's newline) so token splitting is
        // line-independent; parts = ["define-fun", name, "()", <sort…>, value].
        let normalized = inner
            .split_whitespace()
            .collect::<alloc::vec::Vec<_>>()
            .join(" ");
        let parts = crate::api::build::top_level_parts(&normalized);
        if parts.len() < 5 || parts[2] != "()" {
            continue; // not a 0-ary constant we can render
        }
        let name = parts[1];
        let sort_toks = &parts[3..parts.len() - 1];
        let sort = parse_sort_tokens(sort_toks);
        out.push((name.to_string(), sort));
    }
    out
}

/// Reconstruct a [`Sort`] from its printed tokens (`Int`, `Bool`, `Real`,
/// `(_ BitVec 8)`, `(Array …)`, or an uninterpreted name).
fn parse_sort_tokens(toks: &[&str]) -> Sort {
    let joined = toks.join(" ");
    let s = joined.trim();
    match s {
        "Int" => Sort::Int,
        "Bool" => Sort::Bool,
        "Real" => Sort::Real,
        _ => {
            if let Some(inner) = s
                .strip_prefix("(_ BitVec ")
                .and_then(|r| r.strip_suffix(')'))
                && let Ok(w) = inner.trim().parse::<u32>()
            {
                return Sort::BitVec(w);
            }
            Sort::Uninterpreted(s.to_string())
        }
    }
}

/// `Z3_model_to_string(c, m)` — the SMT-LIB rendering of a model (owned by the
/// model, valid until [`Z3_del_context`]; do not free).
///
/// # Safety
/// `c` valid context; `m` a `Z3_model` from [`Z3_solver_get_model`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_model_to_string(
    _c: *mut Z3rsZ3Context,
    m: *const Z3rsModel,
) -> *const c_char {
    if m.is_null() {
        return ptr::null();
    }
    unsafe { &*m }.text.as_ptr()
}

/// Peel a `(get-value ((term value)))` response line down to `value`, matching
/// [`Z3rsSolver`]'s printed `((term value))` shape.
fn peel_get_value(line: &str, term: &str) -> Option<String> {
    let inner = line.trim().strip_prefix('(')?.strip_suffix(')')?.trim();
    let inner = inner.strip_prefix('(')?.strip_suffix(')')?.trim();
    Some(
        inner
            .strip_prefix(term)
            .map(str::trim)
            .unwrap_or(inner)
            .to_string(),
    )
}

/// Query `(get-value (term))` against a solver's current model, returning the
/// printed value string.
///
/// # Safety
/// `s` must be NULL or a valid solver handle.
unsafe fn solver_get_value(s: *const Z3rsSolver, term: &str) -> Option<String> {
    let sol = unsafe { solver_mut(s) }?;
    let out = sol
        .session
        .eval(&alloc::format!("(get-value ({term}))"))
        .ok()?;
    peel_get_value(out.first()?, term)
}

/// Sniff a [`Sort`] from a printed value literal (used when no declared sort is
/// available for the queried term).
fn sniff_value_sort(v: &str) -> Sort {
    let v = v.trim();
    if v == "true" || v == "false" {
        return Sort::Bool;
    }
    if let Some(hex) = v.strip_prefix("#x") {
        return Sort::BitVec((hex.len() as u32) * 4);
    }
    if let Some(bin) = v.strip_prefix("#b") {
        return Sort::BitVec(bin.len() as u32);
    }
    if let Some(rest) = v.strip_prefix("(_ bv")
        && let Some(w) = rest
            .split_whitespace()
            .nth(1)
            .and_then(|t| t.trim_end_matches(')').parse::<u32>().ok())
    {
        return Sort::BitVec(w);
    }
    if v.contains('/') || v.contains('.') {
        return Sort::Real;
    }
    Sort::Int
}

/// `Z3_model_eval(c, m, t, model_completion, out)` — evaluate term `t` under
/// model `m`, writing the resulting value AST to `*out`. Returns `true` on
/// success. Implemented by re-querying `(get-value (t))` against the solver that
/// produced the model and wrapping the printed value as a fresh numeral/bool/bv
/// AST. `model_completion` is accepted; the engine always yields a total model.
///
/// # Safety
/// `c` valid context; `m` a model handle; `t` a valid `Z3_ast`; `out` writable.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_model_eval(
    c: *mut Z3rsZ3Context,
    m: *const Z3rsModel,
    t: *const Z3rsAst,
    _model_completion: bool,
    out: *mut *const Z3rsAst,
) -> bool {
    if c.is_null() || m.is_null() || t.is_null() {
        return false;
    }
    let (solver, term, sort) = {
        let model = unsafe { &*m };
        let ast = unsafe { &*t };
        (model.solver, ast.to_smt().to_string(), ast.sort().clone())
    };
    let Some(value) = (unsafe { solver_get_value(solver, &term) }) else {
        return false;
    };
    let ast = Ast::new(value, sort);
    let ptr = unsafe { &mut *c }.intern_ast(ast);
    if !out.is_null() {
        unsafe { *out = ptr };
    }
    true
}

/// `Z3_model_get_const_interp(c, m, decl)` — the value of the 0-ary declaration
/// `decl` in model `m` (via `(get-value (name))`), or NULL if unavailable.
///
/// # Safety
/// `c` valid context; `m` a model handle; `decl` a valid `Z3_func_decl`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_model_get_const_interp(
    c: *mut Z3rsZ3Context,
    m: *const Z3rsModel,
    decl: *const Z3rsFuncDecl,
) -> *const Z3rsAst {
    if c.is_null() || m.is_null() || decl.is_null() {
        return ptr::null();
    }
    let (solver, name, sort) = {
        let model = unsafe { &*m };
        let fd = unsafe { &*decl };
        let name = fd.name().to_string();
        // Prefer the sort recorded in the model; fall back to the decl's range.
        let sort = model
            .consts
            .iter()
            .find(|(n, _)| *n == name)
            .map(|(_, s)| s.clone())
            .unwrap_or_else(|| fd.range().clone());
        (model.solver, name, sort)
    };
    let Some(value) = (unsafe { solver_get_value(solver, &name) }) else {
        return ptr::null();
    };
    unsafe { &mut *c }.intern_ast(Ast::new(value, sort))
}

/// `Z3_model_get_num_consts(c, m)` — the number of 0-ary constants interpreted
/// by the model.
///
/// # Safety
/// `m` must be NULL or a valid model handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_model_get_num_consts(
    _c: *mut Z3rsZ3Context,
    m: *const Z3rsModel,
) -> u32 {
    if m.is_null() {
        return 0;
    }
    unsafe { &*m }.consts.len() as u32
}

/// `Z3_model_get_const_decl(c, m, i)` — the declaration of the `i`-th 0-ary
/// constant of the model (a synthesised `Z3_func_decl` with name and range sort).
///
/// # Safety
/// `c` valid context; `m` a model handle; `i < Z3_model_get_num_consts(c, m)`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_model_get_const_decl(
    c: *mut Z3rsZ3Context,
    m: *const Z3rsModel,
    i: u32,
) -> *const Z3rsFuncDecl {
    if c.is_null() || m.is_null() {
        return ptr::null();
    }
    let entry = {
        let model = unsafe { &*m };
        model.consts.get(i as usize).cloned()
    };
    let Some((name, sort)) = entry else {
        return ptr::null();
    };
    unsafe { &mut *c }.intern_func_decl(FuncDecl::new(name, sort))
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
    concat!(
        "z3rs ",
        env!("CARGO_PKG_VERSION"),
        " (Z3 4.17.0 compatible)\0"
    )
    .as_ptr() as *const c_char
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
pub unsafe extern "C" fn Z3_mk_int2real(
    c: *mut Z3rsZ3Context,
    a: *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe { mk_un(c, a, |x| x.int2real()) }
}
/// # Safety
/// `c` valid context; `a` a valid `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_real2int(
    c: *mut Z3rsZ3Context,
    a: *const Z3rsAst,
) -> *const Z3rsAst {
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
        pub unsafe extern "C" fn $name(c: *mut Z3rsZ3Context, a: *const Z3rsAst) -> *const Z3rsAst {
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

unsafe fn mk_numeral_val(c: *mut Z3rsZ3Context, v: i128, ty: *const Z3rsSort) -> *const Z3rsAst {
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
/// `BOOL`=1, `INT`=2, `REAL`=3, `BV`=4, `ARRAY`=5, `DATATYPE`=6).
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
        Sort::Datatype(_) => 6, // Z3_DATATYPE_SORT
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

// --- AST kind & numeral readback -------------------------------------------

/// `Z3_get_ast_kind(c, a)` — the `Z3_ast_kind` tag: `Z3_NUMERAL_AST` (0) for a
/// numeral literal, `Z3_APP_AST` (1) for everything else (constants and
/// applications), or `Z3_UNKNOWN_AST` (1000) for NULL. z3rs terms are text, so
/// bound variables / quantifiers are not distinguished — they read as `APP`.
///
/// # Safety
/// `a` must be NULL or a valid `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_get_ast_kind(_c: *mut Z3rsZ3Context, a: *const Z3rsAst) -> u32 {
    if a.is_null() {
        return 1000; // Z3_UNKNOWN_AST
    }
    if unsafe { &*a }.is_numeral() {
        0 // Z3_NUMERAL_AST
    } else {
        1 // Z3_APP_AST
    }
}

/// `Z3_is_numeral_ast(c, a)` — whether `a` is a numeral literal.
///
/// # Safety
/// `a` must be NULL or a valid `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_is_numeral_ast(_c: *mut Z3rsZ3Context, a: *const Z3rsAst) -> bool {
    !a.is_null() && unsafe { &*a }.is_numeral()
}

/// `Z3_get_numeral_string(c, a)` — the decimal (integer) or `p/q` (rational)
/// string of a numeral AST (context-owned; do not free). Returns `"0"` if `a`
/// is not a numeral literal.
///
/// # Safety
/// `c` valid context; `a` a valid `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_get_numeral_string(
    c: *mut Z3rsZ3Context,
    a: *const Z3rsAst,
) -> *const c_char {
    if c.is_null() || a.is_null() {
        return ptr::null();
    }
    let s = unsafe { &*a }
        .numeral_string()
        .unwrap_or_else(|| "0".to_string());
    let ctx = unsafe { &mut *c };
    intern_string(ctx, s)
}

/// The numeral of `a` as an integer, if it is an integer literal that fits.
///
/// # Safety
/// `a` must be NULL or a valid `Z3_ast`.
unsafe fn numeral_i128(a: *const Z3rsAst) -> Option<i128> {
    if a.is_null() {
        None
    } else {
        unsafe { &*a }.as_int()
    }
}

/// `Z3_get_numeral_int(c, v, i)` — write `v`'s value as an `int`, returning
/// `false` if it is not an integer numeral or does not fit.
///
/// # Safety
/// `v` a valid `Z3_ast`; `i` writable.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_get_numeral_int(
    _c: *mut Z3rsZ3Context,
    v: *const Z3rsAst,
    i: *mut i32,
) -> bool {
    match unsafe { numeral_i128(v) }.and_then(|n| i32::try_from(n).ok()) {
        Some(n) if !i.is_null() => {
            unsafe { *i = n };
            true
        }
        _ => false,
    }
}

/// `Z3_get_numeral_uint(c, v, u)` — as `unsigned`.
///
/// # Safety
/// `v` a valid `Z3_ast`; `u` writable.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_get_numeral_uint(
    _c: *mut Z3rsZ3Context,
    v: *const Z3rsAst,
    u: *mut u32,
) -> bool {
    match unsafe { numeral_i128(v) }.and_then(|n| u32::try_from(n).ok()) {
        Some(n) if !u.is_null() => {
            unsafe { *u = n };
            true
        }
        _ => false,
    }
}

/// `Z3_get_numeral_int64(c, v, i)` — as `int64_t`.
///
/// # Safety
/// `v` a valid `Z3_ast`; `i` writable.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_get_numeral_int64(
    _c: *mut Z3rsZ3Context,
    v: *const Z3rsAst,
    i: *mut i64,
) -> bool {
    match unsafe { numeral_i128(v) }.and_then(|n| i64::try_from(n).ok()) {
        Some(n) if !i.is_null() => {
            unsafe { *i = n };
            true
        }
        _ => false,
    }
}

/// `Z3_get_numeral_uint64(c, v, u)` — as `uint64_t`.
///
/// # Safety
/// `v` a valid `Z3_ast`; `u` writable.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_get_numeral_uint64(
    _c: *mut Z3rsZ3Context,
    v: *const Z3rsAst,
    u: *mut u64,
) -> bool {
    match unsafe { numeral_i128(v) }.and_then(|n| u64::try_from(n).ok()) {
        Some(n) if !u.is_null() => {
            unsafe { *u = n };
            true
        }
        _ => false,
    }
}

// --- Application accessors (minimum viable) ---------------------------------

/// Split an application term's source into `[head, arg1, arg2, …]`, or `None`
/// if it is a bare atom (a constant or literal, i.e. a 0-argument application).
fn app_parts(src: &str) -> Option<Vec<&str>> {
    let s = src.trim();
    let inner = s.strip_prefix('(').and_then(|r| r.strip_suffix(')'))?;
    let parts = crate::api::build::top_level_parts(inner);
    if parts.is_empty() { None } else { Some(parts) }
}

/// `Z3_to_app(c, a)` — reinterpret an AST as an application. z3rs uses one term
/// representation, so this is the identity.
///
/// # Safety
/// `a` must be NULL or a valid `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_to_app(_c: *mut Z3rsZ3Context, a: *const Z3rsAst) -> *const Z3rsAst {
    a
}

/// `Z3_get_app_num_args(c, a)` — the number of arguments of an application (0
/// for a constant or literal).
///
/// # Safety
/// `a` must be NULL or a valid `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_get_app_num_args(_c: *mut Z3rsZ3Context, a: *const Z3rsAst) -> u32 {
    if a.is_null() {
        return 0;
    }
    match app_parts(unsafe { &*a }.to_smt()) {
        Some(parts) => (parts.len() as u32).saturating_sub(1),
        None => 0,
    }
}

/// `Z3_get_app_arg(c, a, i)` — the `i`-th argument of an application, as a fresh
/// AST (its sort is sniffed from the text, best-effort). NULL if out of range.
///
/// # Safety
/// `c` valid context; `a` a valid `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_get_app_arg(
    c: *mut Z3rsZ3Context,
    a: *const Z3rsAst,
    i: u32,
) -> *const Z3rsAst {
    if c.is_null() || a.is_null() {
        return ptr::null();
    }
    let arg = {
        let parts = app_parts(unsafe { &*a }.to_smt());
        parts.and_then(|p| p.get(i as usize + 1).map(|s| s.to_string()))
    };
    match arg {
        Some(src) => {
            let sort = sniff_value_sort(&src);
            unsafe { &mut *c }.intern_ast(Ast::new(src, sort))
        }
        None => ptr::null(),
    }
}

/// `Z3_get_app_decl(c, a)` — the declaration (operator) of an application: a
/// synthesised `Z3_func_decl` whose name is the head symbol and whose range is
/// the term's sort. For a bare constant the name is the constant itself.
///
/// # Safety
/// `c` valid context; `a` a valid `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_get_app_decl(
    c: *mut Z3rsZ3Context,
    a: *const Z3rsAst,
) -> *const Z3rsFuncDecl {
    if c.is_null() || a.is_null() {
        return ptr::null();
    }
    let (name, sort) = {
        let ast = unsafe { &*a };
        let name = match app_parts(ast.to_smt()) {
            Some(parts) => parts[0].to_string(),
            None => ast.to_smt().to_string(),
        };
        (name, ast.sort().clone())
    };
    unsafe { &mut *c }.intern_func_decl(FuncDecl::new(name, sort))
}

/// `Z3_get_decl_name(c, d)` — the name symbol of a declaration.
///
/// # Safety
/// `c` valid context; `d` a valid `Z3_func_decl`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_get_decl_name(
    c: *mut Z3rsZ3Context,
    d: *const Z3rsFuncDecl,
) -> *const Z3rsSymbol {
    if c.is_null() || d.is_null() {
        return ptr::null();
    }
    let name = unsafe { &*d }.name().to_string();
    let ctx = unsafe { &mut *c };
    let cstr = match CString::new(name) {
        Ok(cs) => cs,
        Err(_) => return ptr::null(),
    };
    let ptr = cstr.as_ptr();
    ctx.symbols.push(cstr);
    ptr
}

// --- AST vectors (z3_ast_containers.h) --------------------------------------

/// `Z3_ast_vector` — a growable list of `Z3_ast` handles (owned by the context
/// arena, freed at [`Z3_del_context`]). Element pointers reference context ASTs
/// that outlive the vector.
pub struct Z3rsAstVector {
    items: alloc::vec::Vec<*const Ast>,
}

/// `Z3_mk_ast_vector(c)` — a fresh, empty AST vector.
///
/// # Safety
/// `c` must be a valid context handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_ast_vector(c: *mut Z3rsZ3Context) -> *const Z3rsAstVector {
    if c.is_null() {
        return ptr::null();
    }
    unsafe { &mut *c }.intern_ast_vector(Z3rsAstVector {
        items: alloc::vec::Vec::new(),
    })
}

/// `Z3_ast_vector_inc_ref(c, v)` — no-op (arena-owned).
#[unsafe(no_mangle)]
pub extern "C" fn Z3_ast_vector_inc_ref(_c: *mut Z3rsZ3Context, _v: *const Z3rsAstVector) {}
/// `Z3_ast_vector_dec_ref(c, v)` — no-op (arena-owned).
#[unsafe(no_mangle)]
pub extern "C" fn Z3_ast_vector_dec_ref(_c: *mut Z3rsZ3Context, _v: *const Z3rsAstVector) {}

/// `Z3_ast_vector_size(c, v)` — the number of elements.
///
/// # Safety
/// `v` must be NULL or a valid AST vector handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_ast_vector_size(
    _c: *mut Z3rsZ3Context,
    v: *const Z3rsAstVector,
) -> u32 {
    if v.is_null() {
        return 0;
    }
    unsafe { &*v }.items.len() as u32
}

/// `Z3_ast_vector_get(c, v, i)` — the `i`-th element (NULL if out of range).
///
/// # Safety
/// `v` must be NULL or a valid AST vector handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_ast_vector_get(
    _c: *mut Z3rsZ3Context,
    v: *const Z3rsAstVector,
    i: u32,
) -> *const Z3rsAst {
    if v.is_null() {
        return ptr::null();
    }
    unsafe { &*v }
        .items
        .get(i as usize)
        .copied()
        .unwrap_or(ptr::null())
}

/// `Z3_ast_vector_push(c, v, a)` — append an AST to the vector.
///
/// # Safety
/// `v` a valid AST vector handle; `a` a valid `Z3_ast`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_ast_vector_push(
    _c: *mut Z3rsZ3Context,
    v: *const Z3rsAstVector,
    a: *const Z3rsAst,
) {
    if v.is_null() || a.is_null() {
        return;
    }
    let vec = unsafe { &mut *(v as *mut Z3rsAstVector) };
    vec.items.push(a);
}

/// `Z3_ast_vector_to_string(c, v)` — the elements rendered as SMT-LIB terms, one
/// per line, wrapped in parentheses (context-owned; do not free).
///
/// # Safety
/// `c` valid context; `v` a valid AST vector handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_ast_vector_to_string(
    c: *mut Z3rsZ3Context,
    v: *const Z3rsAstVector,
) -> *const c_char {
    if c.is_null() || v.is_null() {
        return ptr::null();
    }
    let text = {
        let vec = unsafe { &*v };
        let mut s = String::from("(ast-vector");
        for &p in &vec.items {
            if !p.is_null() {
                s.push_str("\n  ");
                s.push_str(unsafe { &*p }.to_smt());
            }
        }
        s.push(')');
        s
    };
    let ctx = unsafe { &mut *c };
    intern_string(ctx, text)
}

/// `Z3_solver_get_unsat_core(c, s)` — the unsat core of the most recent
/// unsatisfiable check, as a `Z3_ast_vector` of the tracking assumption ASTs
/// registered via [`Z3_solver_assert_and_track`]. Parses `(get-unsat-core)` and
/// maps each printed `:named` label back to its tracking `Z3_ast`.
///
/// # Safety
/// `c` valid context; `s` a solver from this context.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_solver_get_unsat_core(
    c: *mut Z3rsZ3Context,
    s: *const Z3rsSolver,
) -> *const Z3rsAstVector {
    if c.is_null() {
        return ptr::null();
    }
    let items = {
        let Some(sol) = (unsafe { solver_mut(s) }) else {
            return ptr::null();
        };
        let names: alloc::vec::Vec<String> = match sol.session.eval("(get-unsat-core)") {
            Ok(lines) => lines
                .first()
                .map(|line| {
                    line.trim()
                        .trim_start_matches('(')
                        .trim_end_matches(')')
                        .split_whitespace()
                        .map(str::to_string)
                        .collect()
                })
                .unwrap_or_default(),
            Err(_) => alloc::vec::Vec::new(),
        };
        let mut items: alloc::vec::Vec<*const Ast> = alloc::vec::Vec::new();
        for name in &names {
            if let Some((_, ast)) = sol.tracked.iter().find(|(n, _)| n == name) {
                items.push(*ast);
            }
        }
        items
    };
    unsafe { &mut *c }.intern_ast_vector(Z3rsAstVector { items })
}

// --- Quantifiers ------------------------------------------------------------
//
// The `_const` builder forms real clients use: bound variables are supplied as
// constant `Z3_app`s (their name + sort), so no De-Bruijn bookkeeping is needed
// — the text front end binds them by name in the rendered `(forall/exists …)`.

/// `Z3_pattern` — a quantifier instantiation trigger, rendered as the group
/// `(t₁ … tₙ)`. Owned by the context arena (freed at [`Z3_del_context`]).
pub struct Z3rsPattern {
    src: String,
}

/// `Z3_mk_pattern(c, num_patterns, terms)` — build a (multi-)pattern from its
/// trigger terms, as a `Z3_pattern` usable in the `_const` quantifier builders.
///
/// # Safety
/// `c` valid context; `terms` points to `num_patterns` valid `Z3_ast` handles.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_pattern(
    c: *mut Z3rsZ3Context,
    num_patterns: u32,
    terms: *const *const Z3rsAst,
) -> *const Z3rsPattern {
    if c.is_null() {
        return ptr::null();
    }
    let items = if num_patterns == 0 {
        alloc::vec::Vec::new()
    } else {
        let Some(v) = (unsafe { read_args(num_patterns, terms) }) else {
            return ptr::null();
        };
        v
    };
    let src = Ast::pattern(&items);
    unsafe { &mut *c }.intern_pattern(Z3rsPattern { src })
}

/// Read `num` bound-variable `Z3_app` handles into `(name, sort)` pairs.
///
/// # Safety
/// `bound` must point to `num` valid `Z3_ast` handles (each a constant whose
/// `src` is the variable name and whose sort is the variable's sort).
unsafe fn read_bound<'a>(
    num: u32,
    bound: *const *const Z3rsAst,
) -> Option<alloc::vec::Vec<(&'a str, &'a Sort)>> {
    if num == 0 {
        return Some(alloc::vec::Vec::new());
    }
    if bound.is_null() {
        return None;
    }
    let mut out = alloc::vec::Vec::with_capacity(num as usize);
    for i in 0..num as isize {
        let p = unsafe { *bound.offset(i) };
        if p.is_null() {
            return None;
        }
        let a = unsafe { &*p };
        out.push((a.to_smt(), a.sort()));
    }
    Some(out)
}

/// Shared body of the `_const` quantifier builders: render
/// `(forall/exists ((v S)…) [(! body :pattern … :weight w)])`.
///
/// # Safety
/// `c` valid context; `bound`/`patterns` point to the given counts of valid
/// handles; `body` a valid `Z3_ast`.
#[allow(clippy::too_many_arguments)]
unsafe fn mk_quantifier_const(
    c: *mut Z3rsZ3Context,
    is_forall: bool,
    weight: u32,
    num_bound: u32,
    bound: *const *const Z3rsAst,
    num_patterns: u32,
    patterns: *const *const Z3rsPattern,
    body: *const Z3rsAst,
) -> *const Z3rsAst {
    if c.is_null() || body.is_null() {
        return ptr::null();
    }
    let Some(vars) = (unsafe { read_bound(num_bound, bound) }) else {
        return ptr::null();
    };
    let mut pats: alloc::vec::Vec<&str> = alloc::vec::Vec::new();
    if num_patterns > 0 {
        if patterns.is_null() {
            return ptr::null();
        }
        for i in 0..num_patterns as isize {
            let p = unsafe { *patterns.offset(i) };
            if p.is_null() {
                return ptr::null();
            }
            pats.push(unsafe { &*p }.src.as_str());
        }
    }
    let body_ast = unsafe { &*body };
    let q = BuildContext::quantifier(is_forall, weight, &vars, &pats, body_ast);
    unsafe { &mut *c }.intern_ast(q)
}

/// `Z3_mk_forall_const(c, weight, num_bound, bound, num_patterns, patterns,
/// body)` — a universally-quantified formula over the constant bound variables
/// `bound`, with optional instantiation `patterns` and `weight` (→ Bool).
///
/// # Safety
/// `c` valid context; `bound` points to `num_bound` valid `Z3_app` handles;
/// `patterns` to `num_patterns` valid `Z3_pattern` handles; `body` valid.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_forall_const(
    c: *mut Z3rsZ3Context,
    weight: u32,
    num_bound: u32,
    bound: *const *const Z3rsAst,
    num_patterns: u32,
    patterns: *const *const Z3rsPattern,
    body: *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe {
        mk_quantifier_const(
            c,
            true,
            weight,
            num_bound,
            bound,
            num_patterns,
            patterns,
            body,
        )
    }
}

/// `Z3_mk_exists_const(...)` — the existential variant of [`Z3_mk_forall_const`].
///
/// # Safety
/// See [`Z3_mk_forall_const`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_exists_const(
    c: *mut Z3rsZ3Context,
    weight: u32,
    num_bound: u32,
    bound: *const *const Z3rsAst,
    num_patterns: u32,
    patterns: *const *const Z3rsPattern,
    body: *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe {
        mk_quantifier_const(
            c,
            false,
            weight,
            num_bound,
            bound,
            num_patterns,
            patterns,
            body,
        )
    }
}

/// `Z3_mk_quantifier_const(c, is_forall, …)` — dispatch to
/// [`Z3_mk_forall_const`] / [`Z3_mk_exists_const`] on `is_forall`.
///
/// # Safety
/// See [`Z3_mk_forall_const`].
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_quantifier_const(
    c: *mut Z3rsZ3Context,
    is_forall: bool,
    weight: u32,
    num_bound: u32,
    bound: *const *const Z3rsAst,
    num_patterns: u32,
    patterns: *const *const Z3rsPattern,
    body: *const Z3rsAst,
) -> *const Z3rsAst {
    unsafe {
        mk_quantifier_const(
            c,
            is_forall,
            weight,
            num_bound,
            bound,
            num_patterns,
            patterns,
            body,
        )
    }
}

// --- Algebraic datatypes ----------------------------------------------------
//
// Datatypes are declared to the text front end with `(declare-datatype …)`; the
// C-API `Z3_constructor` objects capture the spec (constructor name, fields and
// their sorts, with a NULL field-sort meaning a recursive reference to the
// datatype being defined) so `Z3_query_constructor` can later hand back the
// constructor / tester / accessor function declarations.

/// One field of a datatype constructor.
#[derive(Clone)]
struct ConstructorField {
    name: String,
    /// The field's sort, or `None` for a recursive reference to the datatype
    /// being defined (`sort_ref` selects which, but z3rs defines one datatype at
    /// a time, so any `None` refers to that datatype).
    sort: Option<Sort>,
    #[allow(dead_code)]
    sort_ref: u32,
}

/// `Z3_constructor` — a captured datatype-constructor spec. Owned by the context
/// arena; [`Z3_mk_datatype`] records the datatype sort into it for later
/// [`Z3_query_constructor`] queries.
pub struct Z3rsConstructor {
    name: String,
    fields: alloc::vec::Vec<ConstructorField>,
    datatype: Option<Sort>,
}

/// `Z3_mk_constructor(c, name, recognizer, num_fields, field_names, sorts,
/// sort_refs)` — capture a constructor spec. A `NULL` entry in `sorts` (with the
/// paired `sort_refs` index) denotes a recursive reference to the datatype under
/// construction. The `recognizer` name is accepted; z3rs's tester is always the
/// standard `(_ is name)`, so it is not otherwise stored.
///
/// # Safety
/// `c` valid context; `field_names`/`sorts`/`sort_refs` point to `num_fields`
/// entries (any of the arrays may be NULL only when `num_fields == 0`).
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_constructor(
    c: *mut Z3rsZ3Context,
    name: *const Z3rsSymbol,
    _recognizer: *const Z3rsSymbol,
    num_fields: u32,
    field_names: *const *const Z3rsSymbol,
    sorts: *const *const Z3rsSort,
    sort_refs: *mut u32,
) -> *const Z3rsConstructor {
    if c.is_null() {
        return ptr::null();
    }
    let name = unsafe { c_str(name) }.unwrap_or("").to_string();
    let mut fields = alloc::vec::Vec::with_capacity(num_fields as usize);
    for i in 0..num_fields as isize {
        let fname = if field_names.is_null() {
            String::new()
        } else {
            unsafe { c_str(*field_names.offset(i)) }
                .unwrap_or("")
                .to_string()
        };
        let sort = if sorts.is_null() {
            None
        } else {
            let sp = unsafe { *sorts.offset(i) };
            if sp.is_null() {
                None
            } else {
                Some(unsafe { &*sp }.clone())
            }
        };
        let sort_ref = if sort_refs.is_null() {
            0
        } else {
            unsafe { *sort_refs.offset(i) }
        };
        fields.push(ConstructorField {
            name: fname,
            sort,
            sort_ref,
        });
    }
    unsafe { &mut *c }.intern_constructor(Z3rsConstructor {
        name,
        fields,
        datatype: None,
    })
}

/// `Z3_mk_datatype(c, name, num_constructors, constructors)` — declare an
/// algebraic datatype from its constructor specs and return its `Z3_sort`. Emits
/// `(declare-datatype name ((ctor (field sort)…)…))` into the session and
/// records the resulting sort into each `Z3_constructor` for
/// [`Z3_query_constructor`].
///
/// # Safety
/// `c` valid context; `constructors` points to `num_constructors` valid
/// `Z3_constructor` handles from this context.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_datatype(
    c: *mut Z3rsZ3Context,
    name: *const Z3rsSymbol,
    num_constructors: u32,
    constructors: *mut *const Z3rsConstructor,
) -> *const Z3rsSort {
    if c.is_null() || constructors.is_null() || num_constructors == 0 {
        return ptr::null();
    }
    let dt_name = unsafe { c_str(name) }.unwrap_or("").to_string();
    // Render the constructor list, using the datatype name for recursive fields.
    let mut body = String::new();
    for i in 0..num_constructors as isize {
        let kp = unsafe { *constructors.offset(i) };
        if kp.is_null() {
            return ptr::null();
        }
        let k = unsafe { &*kp };
        if i > 0 {
            body.push(' ');
        }
        body.push('(');
        body.push_str(&k.name);
        for f in &k.fields {
            let sort_txt = match &f.sort {
                Some(s) => s.smt(),
                None => dt_name.clone(),
            };
            body.push_str(&alloc::format!(" ({} {})", f.name, sort_txt));
        }
        body.push(')');
    }
    let sort = unsafe { &mut *c }.build.declare_datatype(&dt_name, &body);
    // Record the datatype sort into each constructor (arena-owned; safe to
    // reborrow mutably through the raw pointer, as `Z3_ast_vector_push` does).
    for i in 0..num_constructors as isize {
        let kp = unsafe { *constructors.offset(i) } as *mut Z3rsConstructor;
        unsafe { (*kp).datatype = Some(sort.clone()) };
    }
    unsafe { &mut *c }.intern_sort(sort)
}

/// `Z3_query_constructor(c, constr, num_fields, constructor, tester, accessors)`
/// — hand back the constructor's function declarations: the constructor itself
/// (range = the datatype sort), its `(_ is name)` tester (range = Bool), and one
/// accessor per field (range = the field's sort). NULL out-pointers are skipped.
///
/// # Safety
/// `c` valid context; `constr` a `Z3_constructor` already passed to
/// [`Z3_mk_datatype`]; `accessors` (if non-NULL) writable for `num_fields`
/// entries; `constructor`/`tester` writable if non-NULL.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_query_constructor(
    c: *mut Z3rsZ3Context,
    constr: *const Z3rsConstructor,
    num_fields: u32,
    constructor: *mut *const Z3rsFuncDecl,
    tester: *mut *const Z3rsFuncDecl,
    accessors: *mut *const Z3rsFuncDecl,
) {
    if c.is_null() || constr.is_null() {
        return;
    }
    let (ctor_name, dt, fields) = {
        let k = unsafe { &*constr };
        let dt = k
            .datatype
            .clone()
            .unwrap_or_else(|| Sort::Datatype(String::new()));
        (k.name.clone(), dt, k.fields.clone())
    };
    if !constructor.is_null() {
        let fd = unsafe { &mut *c }.intern_func_decl(FuncDecl::new(ctor_name.clone(), dt.clone()));
        unsafe { *constructor = fd };
    }
    if !tester.is_null() {
        let tname = alloc::format!("(_ is {ctor_name})");
        let fd = unsafe { &mut *c }.intern_func_decl(FuncDecl::new(tname, Sort::Bool));
        unsafe { *tester = fd };
    }
    if !accessors.is_null() {
        for (i, f) in fields.iter().enumerate().take(num_fields as usize) {
            let range = f.sort.clone().unwrap_or_else(|| dt.clone());
            let fd = unsafe { &mut *c }.intern_func_decl(FuncDecl::new(f.name.clone(), range));
            unsafe { *accessors.add(i) = fd };
        }
    }
}

/// `Z3_constructor_list` — an arena wrapper around a list of `Z3_constructor`s
/// (used by the mutually-recursive `Z3_mk_datatypes` surface; kept so clients
/// that build one link and run).
pub struct Z3rsConstructorList {
    #[allow(dead_code)]
    constructors: alloc::vec::Vec<*const Z3rsConstructor>,
}

/// `Z3_mk_constructor_list(c, num_constructors, constructors)` — wrap
/// constructors into a `Z3_constructor_list`.
///
/// # Safety
/// `c` valid context; `constructors` points to `num_constructors` valid handles.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_constructor_list(
    c: *mut Z3rsZ3Context,
    num_constructors: u32,
    constructors: *const *const Z3rsConstructor,
) -> *const Z3rsConstructorList {
    if c.is_null() {
        return ptr::null();
    }
    let mut items = alloc::vec::Vec::with_capacity(num_constructors as usize);
    if num_constructors > 0 {
        if constructors.is_null() {
            return ptr::null();
        }
        for i in 0..num_constructors as isize {
            items.push(unsafe { *constructors.offset(i) });
        }
    }
    unsafe { &mut *c }.intern_constructor_list(Z3rsConstructorList {
        constructors: items,
    })
}

/// `Z3_del_constructor(c, constr)` — no-op (arena-owned until
/// [`Z3_del_context`]).
#[unsafe(no_mangle)]
pub extern "C" fn Z3_del_constructor(_c: *mut Z3rsZ3Context, _constr: *const Z3rsConstructor) {}

/// `Z3_del_constructor_list(c, clist)` — no-op (arena-owned).
#[unsafe(no_mangle)]
pub extern "C" fn Z3_del_constructor_list(
    _c: *mut Z3rsZ3Context,
    _clist: *const Z3rsConstructorList,
) {
}

/// `Z3_mk_enumeration_sort(c, name, n, enum_names, enum_consts, enum_testers)` —
/// a datatype of `n` nullary constructors. Fills `enum_consts[i]` with each
/// value's constructor decl and `enum_testers[i]` with its `(_ is …)` tester.
///
/// # Safety
/// `c` valid context; `enum_names` points to `n` valid symbols; `enum_consts` /
/// `enum_testers` (if non-NULL) writable for `n` entries.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_enumeration_sort(
    c: *mut Z3rsZ3Context,
    name: *const Z3rsSymbol,
    n: u32,
    enum_names: *const *const Z3rsSymbol,
    enum_consts: *mut *const Z3rsFuncDecl,
    enum_testers: *mut *const Z3rsFuncDecl,
) -> *const Z3rsSort {
    if c.is_null() || enum_names.is_null() {
        return ptr::null();
    }
    let dt_name = unsafe { c_str(name) }.unwrap_or("").to_string();
    let mut names = alloc::vec::Vec::with_capacity(n as usize);
    for i in 0..n as isize {
        let np = unsafe { *enum_names.offset(i) };
        names.push(unsafe { c_str(np) }.unwrap_or("").to_string());
    }
    let body = names
        .iter()
        .map(|nm| alloc::format!("({nm})"))
        .collect::<alloc::vec::Vec<_>>()
        .join(" ");
    let sort = unsafe { &mut *c }.build.declare_datatype(&dt_name, &body);
    for (i, nm) in names.iter().enumerate() {
        if !enum_consts.is_null() {
            let fd = unsafe { &mut *c }.intern_func_decl(FuncDecl::new(nm.clone(), sort.clone()));
            unsafe { *enum_consts.add(i) = fd };
        }
        if !enum_testers.is_null() {
            let tname = alloc::format!("(_ is {nm})");
            let fd = unsafe { &mut *c }.intern_func_decl(FuncDecl::new(tname, Sort::Bool));
            unsafe { *enum_testers.add(i) = fd };
        }
    }
    unsafe { &mut *c }.intern_sort(sort)
}

/// `Z3_mk_tuple_sort(c, name, num_fields, field_names, field_sorts,
/// mk_tuple_decl, proj_decl)` — a single-constructor datatype (a tuple). Writes
/// the constructor decl to `*mk_tuple_decl` and the `num_fields` projection
/// (accessor) decls to `proj_decl`.
///
/// # Safety
/// `c` valid context; `field_names`/`field_sorts` point to `num_fields` entries;
/// `mk_tuple_decl`/`proj_decl` (if non-NULL) writable.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_tuple_sort(
    c: *mut Z3rsZ3Context,
    name: *const Z3rsSymbol,
    num_fields: u32,
    field_names: *const *const Z3rsSymbol,
    field_sorts: *const *const Z3rsSort,
    mk_tuple_decl: *mut *const Z3rsFuncDecl,
    proj_decl: *mut *const Z3rsFuncDecl,
) -> *const Z3rsSort {
    if c.is_null() {
        return ptr::null();
    }
    let tuple_name = unsafe { c_str(name) }.unwrap_or("").to_string();
    // Sort name: the tuple type; constructor name: `mk-<name>` to avoid clashing
    // with the sort name in the front end's namespaces.
    let ctor_name = alloc::format!("mk-{tuple_name}");
    let mut fnames = alloc::vec::Vec::with_capacity(num_fields as usize);
    let mut fsorts = alloc::vec::Vec::with_capacity(num_fields as usize);
    for i in 0..num_fields as isize {
        let fname = if field_names.is_null() {
            String::new()
        } else {
            unsafe { c_str(*field_names.offset(i)) }
                .unwrap_or("")
                .to_string()
        };
        let fsort = if field_sorts.is_null() {
            Sort::Int
        } else {
            let sp = unsafe { *field_sorts.offset(i) };
            if sp.is_null() {
                Sort::Int
            } else {
                unsafe { &*sp }.clone()
            }
        };
        fnames.push(fname);
        fsorts.push(fsort);
    }
    let mut body = alloc::format!("({ctor_name}");
    for (fname, fsort) in fnames.iter().zip(fsorts.iter()) {
        body.push_str(&alloc::format!(" ({} {})", fname, fsort.smt()));
    }
    body.push(')');
    let sort = unsafe { &mut *c }
        .build
        .declare_datatype(&tuple_name, &body);
    if !mk_tuple_decl.is_null() {
        let fd = unsafe { &mut *c }.intern_func_decl(FuncDecl::new(ctor_name, sort.clone()));
        unsafe { *mk_tuple_decl = fd };
    }
    if !proj_decl.is_null() {
        for (i, (fname, fsort)) in fnames.iter().zip(fsorts.iter()).enumerate() {
            let fd =
                unsafe { &mut *c }.intern_func_decl(FuncDecl::new(fname.clone(), fsort.clone()));
            unsafe { *proj_decl.add(i) = fd };
        }
    }
    unsafe { &mut *c }.intern_sort(sort)
}

/// `Z3_mk_set_sort(c, elem)` — the set sort over `elem`, i.e. `(Array elem
/// Bool)`.
///
/// # Safety
/// `c` valid context; `elem` a valid sort handle.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn Z3_mk_set_sort(
    c: *mut Z3rsZ3Context,
    elem: *const Z3rsSort,
) -> *const Z3rsSort {
    if c.is_null() || elem.is_null() {
        return ptr::null();
    }
    let d = unsafe { &*elem }.clone();
    let s = Sort::Array(
        alloc::boxed::Box::new(d),
        alloc::boxed::Box::new(Sort::Bool),
    );
    unsafe { &mut *c }.intern_sort(s)
}
