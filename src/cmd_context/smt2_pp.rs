//! z3's SMT-LIB2 term pretty printer: the `format` documents and their layout
//! (`z3/src/ast/format.cpp`, `z3/src/ast/pp.cpp`) and the term-to-document
//! translation of `smt2_printer` (`z3/src/ast/ast_smt2_pp.cpp`), with its
//! `let` aliases `a!N` for subterms that are too deep (`pp.max_depth`) or
//! shared and heavy (`pp.min_alias_size`).
//!
//! Terms are given as a hash-consed arena of [`PpNode`]s (equal subterms are
//! the same node), so sharing is node identity as in z3.

use alloc::boxed::Box;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

/// z3's `pp.max_width` / `pp.max_ribbon` defaults.
const MAX_WIDTH: usize = 80;
/// z3's `pp.max_depth` default.
const MAX_DEPTH: u32 = 5;
/// z3's `pp.min_alias_size` default.
const MIN_ALIAS_SIZE: u32 = 10;
/// `ast_smt2_pp.cpp`'s `MAX_INDENT` / `SMALL_INDENT`.
const MAX_INDENT: usize = 16;
const SMALL_INDENT: usize = 2;

/// A layout document (z3's `format` terms).
#[derive(Clone, Debug)]
enum Fmt {
    Str(String),
    Compose(Vec<Fmt>),
    Indent(usize, Box<Fmt>),
    /// `mk_group`: the flat rendering when it fits, else the document itself.
    Group(Box<Fmt>),
    LineBreak,
}

fn s(t: &str) -> Fmt {
    Fmt::Str(String::from(t))
}

fn indent(i: usize, f: Fmt) -> Fmt {
    Fmt::Indent(i, Box::new(f))
}

fn group(f: Fmt) -> Fmt {
    Fmt::Group(Box::new(f))
}

/// `mk_seq`: each element preceded by a line break.
fn seq(items: Vec<Fmt>) -> Fmt {
    let mut out = Vec::with_capacity(items.len() * 2);
    for f in items {
        out.push(Fmt::LineBreak);
        out.push(f);
    }
    Fmt::Compose(out)
}

/// `mk_seq1`: `(header elem_1 … elem_n)` aligned after the header.
fn seq1(items: Vec<Fmt>, header: &str) -> Fmt {
    if items.is_empty() {
        return Fmt::Compose(vec![s("("), s(header), s(")")]);
    }
    let ind = 1 + header.chars().count() + 1;
    let mut it = items.into_iter();
    let first = it.next().unwrap();
    let rest = seq(it.collect());
    let body = Fmt::Compose(vec![s(" "), first, rest, s(")")]);
    group(Fmt::Compose(vec![s("("), s(header), indent(ind, body)]))
}

/// `mk_seq5` (= `mk_seq4` with indent 1): `(elem_1 elem_2 … elem_n)`.
fn seq5(items: Vec<Fmt>) -> Fmt {
    if items.is_empty() {
        return Fmt::Compose(vec![s("("), s(")")]);
    }
    let mut it = items.into_iter();
    let first = it.next().unwrap();
    let heading = indent(1, Fmt::Compose(vec![s("("), first]));
    let rest = seq(it.collect());
    let body = indent(1, Fmt::Compose(vec![rest, s(")")]));
    group(Fmt::Compose(vec![heading, body]))
}

/// The width of `f` printed flat (line breaks as single spaces).
fn flat_width(f: &Fmt) -> usize {
    match f {
        Fmt::Str(t) => t.chars().count(),
        Fmt::Compose(fs) => fs.iter().map(flat_width).sum(),
        Fmt::Indent(_, f) | Fmt::Group(f) => flat_width(f),
        Fmt::LineBreak => 1,
    }
}

/// z3's `pp` layout: a group prints flat when its flat width fits the space
/// left on the line, otherwise its line breaks become newlines.
fn layout(f: &Fmt) -> String {
    let mut out = String::new();
    let mut pos: usize = 0;
    // (document, indentation, printing flat)
    let mut todo: Vec<(&Fmt, usize, bool)> = vec![(f, 0, false)];
    while let Some((f, ind, flat)) = todo.pop() {
        match f {
            Fmt::Str(t) => {
                pos += t.chars().count();
                out.push_str(t);
            }
            Fmt::Indent(i, g) => todo.push((g, ind + i, flat)),
            Fmt::Compose(fs) => {
                for g in fs.iter().rev() {
                    todo.push((g, ind, flat));
                }
            }
            Fmt::Group(g) => {
                let fits = flat || (pos < MAX_WIDTH && flat_width(g) <= MAX_WIDTH - pos);
                todo.push((g, ind, fits));
            }
            Fmt::LineBreak => {
                if flat {
                    pos += 1;
                    out.push(' ');
                } else {
                    pos = ind;
                    out.push('\n');
                    for _ in 0..ind {
                        out.push(' ');
                    }
                }
            }
        }
    }
    out
}

/// One term node: an application of `head` to `args` (node indices into the
/// same arena), or a constant / literal when `args` is empty. An `indexed`
/// head (`(_ re.loop 1 3)`) lays its arguments out as z3 does for indexed
/// declarations: on their own lines, indented by two.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PpNode {
    pub head: String,
    pub args: Vec<usize>,
    pub indexed: bool,
}

/// `smt2_printer`'s per-subterm summary: alias level, weight, depth.
#[derive(Clone, Copy)]
struct Info {
    lvl: u32,
    weight: u32,
    depth: u32,
}

struct Printer<'a> {
    nodes: &'a [PpNode],
    root: usize,
    shared: BTreeSet<usize>,
    assoc: &'a dyn Fn(&str) -> bool,
    alias: BTreeMap<usize, (String, u32)>,
    alias_defs: Vec<(Fmt, u32, String)>,
    next_alias: u32,
}

impl Printer<'_> {
    /// The documents (one, or several for a flattened associative child) and
    /// summaries of node `n` printed as an argument of a `parent_head` node.
    fn visit(&mut self, n: usize, parent_head: Option<&str>, out: &mut Vec<(Fmt, Info)>) {
        if let Some((name, lvl)) = self.alias.get(&n) {
            out.push((
                s(name),
                Info {
                    lvl: lvl + 1,
                    weight: 1,
                    depth: 1,
                },
            ));
            return;
        }
        let node = &self.nodes[n];
        if node.args.is_empty() {
            out.push((
                Fmt::Str(node.head.clone()),
                Info {
                    lvl: 0,
                    weight: 1,
                    depth: 1,
                },
            ));
            return;
        }
        let head = node.head.clone();
        let mut kids: Vec<(Fmt, Info)> = Vec::new();
        for &a in &node.args {
            self.visit(a, Some(&head), &mut kids);
        }
        // `flat_assoc`: an unshared associative application under the same
        // operator contributes its arguments to the parent.
        if parent_head == Some(head.as_str()) && (self.assoc)(&head) && !self.shared.contains(&n) {
            out.extend(kids);
            return;
        }
        let len = if node.indexed {
            usize::MAX
        } else {
            head.chars().count()
        };
        let heading = indent(1, Fmt::Compose(vec![s("("), Fmt::Str(head)]));
        let mut fs: Vec<Fmt> = Vec::with_capacity(kids.len());
        let mut info = Info {
            lvl: 0,
            weight: 1,
            depth: 0,
        };
        for (f, i) in kids {
            info.lvl = info.lvl.max(i.lvl);
            info.weight += i.weight;
            info.depth = info.depth.max(i.depth);
            fs.push(f);
        }
        info.depth += 1;
        let body = if len > MAX_INDENT {
            indent(SMALL_INDENT, Fmt::Compose(vec![seq(fs), s(")")]))
        } else {
            let mut it = fs.into_iter();
            let first = it.next().unwrap();
            let rest = seq(it.collect());
            indent(len + 2, Fmt::Compose(vec![s(" "), first, rest, s(")")]))
        };
        let f = group(Fmt::Compose(vec![heading, body]));
        if n != self.root
            && (info.depth >= MAX_DEPTH
                || (info.weight >= MIN_ALIAS_SIZE && self.shared.contains(&n)))
        {
            let name = alloc::format!("a!{}", self.next_alias);
            self.next_alias += 1;
            self.alias.insert(n, (name.clone(), info.lvl));
            self.alias_defs.push((f, info.lvl, name.clone()));
            out.push((
                Fmt::Str(name),
                Info {
                    lvl: info.lvl + 1,
                    weight: 1,
                    depth: 1,
                },
            ));
            return;
        }
        out.push((f, info));
    }
}

/// The subterms with arguments reached more than once in a depth-first walk
/// from `root` (z3's `shared_occs`).
fn shared_nodes(nodes: &[PpNode], root: usize) -> BTreeSet<usize> {
    let mut visited = BTreeSet::new();
    let mut shared = BTreeSet::new();
    let mut stack = vec![root];
    while let Some(n) = stack.pop() {
        if nodes[n].args.is_empty() {
            continue;
        }
        if !visited.insert(n) {
            shared.insert(n);
            continue;
        }
        stack.extend(nodes[n].args.iter().rev());
    }
    shared
}

/// Print node `root` of `nodes` as z3's `simplify`/`eval` output does:
/// 80-column layout, with `(let ((a!1 …)) …)` aliases. `assoc` tells which
/// operators are associative (their nested applications print flattened).
pub fn pp_term(nodes: &[PpNode], root: usize, assoc: &dyn Fn(&str) -> bool) -> String {
    let mut p = Printer {
        nodes,
        root,
        shared: shared_nodes(nodes, root),
        assoc,
        alias: BTreeMap::new(),
        alias_defs: Vec::new(),
        next_alias: 1,
    };
    let mut out = Vec::new();
    p.visit(root, None, &mut out);
    let body = out.pop().map(|(f, _)| f).unwrap_or_else(|| s(""));
    if p.alias_defs.is_empty() {
        return layout(&body);
    }
    // `pp_let`: one `let` per alias level, innermost level first.
    let max_lvl = p.alias_defs.iter().map(|d| d.1).max().unwrap_or(0);
    let mut buf: Vec<Fmt> = Vec::new();
    let mut num_op = 0;
    for lvl in 0..=max_lvl {
        let decls: Vec<Fmt> = p
            .alias_defs
            .iter()
            .filter(|d| d.1 == lvl)
            .map(|(f, _, name)| seq1(vec![f.clone()], name))
            .collect();
        if decls.is_empty() {
            continue;
        }
        if num_op > 0 {
            buf.push(Fmt::LineBreak);
        }
        num_op += 1;
        buf.push(s("(let "));
        buf.push(indent(5, seq5(decls)));
    }
    buf.push(indent(
        SMALL_INDENT,
        Fmt::Compose(vec![Fmt::LineBreak, body]),
    ));
    for _ in 0..num_op {
        buf.push(s(")"));
    }
    layout(&Fmt::Compose(buf))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn node(head: &str, args: &[usize]) -> PpNode {
        PpNode {
            head: String::from(head),
            args: args.to_vec(),
            indexed: false,
        }
    }

    #[test]
    fn deep_subterms_are_aliased() {
        // (= (re.++ r (re.* r)) (re.++ r (re.++ (re.* r) (re.* (re.++ r (re.* r))))))
        let nodes = vec![
            node("r", &[]),         // 0
            node("re.*", &[0]),     // 1
            node("re.++", &[0, 1]), // 2
            node("re.*", &[2]),     // 3
            node("re.++", &[1, 3]), // 4
            node("re.++", &[0, 4]), // 5
            node("=", &[2, 5]),     // 6
        ];
        assert_eq!(
            pp_term(&nodes, 6, &|_| false),
            "(let ((a!1 (re.++ (re.* r) (re.* (re.++ r (re.* r))))))\n  (= (re.++ r (re.* r)) (re.++ r a!1)))"
        );
        assert_eq!(pp_term(&nodes, 2, &|_| false), "(re.++ r (re.* r))");
    }
}
