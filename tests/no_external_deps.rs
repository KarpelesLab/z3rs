//! Guard test enforcing the project's central invariant: z3rs pulls in NO
//! third-party or native dependency. The one permitted dependency is our own
//! pure-Rust, dependency-free numeric core `puremp`; nothing else is allowed,
//! and `puremp` must be configured on its dependency-free feature set so the
//! transitive tree stays empty (see ROADMAP.md §4).
//!
//! If this test fails, someone added a dependency — don't. Port the
//! functionality in pure Rust (or extend `puremp`) instead.

/// The exclusive allowlist of crates z3rs may depend on. Keep this tiny and
/// justified; every entry must itself be first-party and dependency-free.
const ALLOWED_DEPENDENCIES: &[&str] = &["puremp"];

/// Assert that every crate declared in a `*dependencies` table of Cargo.toml is
/// on the allowlist. This is a cheap structural check; the CI job additionally
/// runs `cargo tree -e normal` and asserts no crate outside the allowlist
/// appears transitively.
#[test]
fn cargo_manifest_only_allows_first_party_deps() {
    let manifest = include_str!("../Cargo.toml");

    let mut in_deps_table = false;
    for raw in manifest.lines() {
        let line = raw.trim();
        if line.starts_with('[') {
            // Any table whose name is or ends with `dependencies`:
            // [dependencies], [dev-dependencies], [target.*.dependencies], etc.
            let name = line.trim_start_matches('[').trim_end_matches(']');
            in_deps_table = name == "dependencies"
                || name.ends_with(".dependencies")
                || name == "dev-dependencies"
                || name == "build-dependencies";
            continue;
        }
        if !in_deps_table || line.is_empty() || line.starts_with('#') {
            continue;
        }
        // Dependency lines look like `name = ...` or `name.workspace = true`.
        let crate_name = line
            .split(['=', '.', ' '])
            .next()
            .unwrap_or("")
            .trim_matches('"');
        assert!(
            ALLOWED_DEPENDENCIES.contains(&crate_name),
            "z3rs may only depend on {ALLOWED_DEPENDENCIES:?}, but Cargo.toml declares \
             {crate_name:?}. This is a hard project invariant — port it in pure Rust \
             (or add it to puremp) instead of taking a new dependency."
        );
    }
}

/// Belt-and-suspenders: the resolved lockfile must not contain any crate outside
/// the allowlist plus z3rs itself. This catches a transitive dependency sneaking
/// in through a feature change on `puremp`.
#[test]
fn lockfile_has_no_unexpected_crates() {
    let lock = include_str!("../Cargo.lock");
    for raw in lock.lines() {
        let line = raw.trim();
        let Some(rest) = line.strip_prefix("name = ") else {
            continue;
        };
        let name = rest.trim_matches('"');
        let ok = name == "z3rs" || ALLOWED_DEPENDENCIES.contains(&name);
        assert!(
            ok,
            "Cargo.lock contains unexpected crate {name:?}. z3rs must stay free of \
             third-party dependencies; only {ALLOWED_DEPENDENCIES:?} (and z3rs) are allowed."
        );
    }
}
