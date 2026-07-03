//! Guard test enforcing the project's central invariant: z3rs depends on NO
//! external library. If this test fails, someone added a dependency — don't.
//! The port must be pure Rust / std-only (see ROADMAP.md §4).

/// Assert the `[dependencies]` and `[dev-dependencies]` tables in Cargo.toml are
/// empty. This is a cheap structural check; CI additionally runs
/// `cargo tree -e normal` to catch transitive deps.
#[test]
fn cargo_manifest_has_no_dependencies() {
    let manifest = include_str!("../Cargo.toml");

    let mut in_deps_table = false;
    for raw in manifest.lines() {
        let line = raw.trim();
        if line.starts_with('[') {
            // Any table whose name is or ends with `dependencies` must be empty:
            // [dependencies], [dev-dependencies], [target.*.dependencies], etc.
            let name = line.trim_start_matches('[').trim_end_matches(']');
            in_deps_table = name == "dependencies"
                || name.ends_with(".dependencies")
                || name == "dev-dependencies"
                || name == "build-dependencies";
            continue;
        }
        if in_deps_table && !line.is_empty() && !line.starts_with('#') {
            panic!(
                "z3rs must have zero external dependencies, but Cargo.toml declares: {line:?}\n\
                 This is a hard project invariant — port the functionality in pure Rust instead."
            );
        }
    }
}
