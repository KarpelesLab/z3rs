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

/// A quantifier node's binder (the node's single argument is its body):
/// `forall` / `exists` / `lambda` and the bound `(name, sort)` pairs, both
/// already rendered.
pub struct PpBinder {
    pub header: String,
    pub vars: Vec<(String, String)>,
}

struct Printer<'a> {
    nodes: &'a [PpNode],
    root: usize,
    shared: &'a BTreeSet<usize>,
    assoc: &'a dyn Fn(&str) -> bool,
    binders: &'a BTreeMap<usize, PpBinder>,
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
        if let Some(b) = self.binders.get(&n) {
            let (f, info) = self.quantifier(b, self.nodes[n].args[0]);
            self.store(n, f, info, out);
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
        self.store(n, f, info, out);
    }

    /// `process_quantifier`: the body printed in a scope of its own (fresh
    /// aliases, `let`-wrapped), after the binder's declarations (`mk_seq3`).
    fn quantifier(&self, b: &PpBinder, body: usize) -> (Fmt, Info) {
        let (f_body, b_info, num_lets) =
            let_doc(self.nodes, body, self.shared, self.assoc, self.binders);
        let decls: Vec<Fmt> = b
            .vars
            .iter()
            .map(|(v, srt)| seq1(vec![s(srt)], v))
            .collect();
        let ind = b.header.chars().count() + 2;
        let first = group(indent(ind, Fmt::Compose(vec![s(" "), seq5(decls)])));
        let rest = indent(SMALL_INDENT, seq(vec![f_body]));
        let f = group(Fmt::Compose(vec![
            s("("),
            s(&b.header),
            first,
            rest,
            s(")"),
        ]));
        let info = Info {
            lvl: 0,
            weight: b_info.weight + 2 * b.vars.len() as u32 + 8 * num_lets,
            depth: b_info.depth + 1,
        };
        (f, info)
    }

    /// `store_result`: push `f`, or an alias for it when it is too deep, or
    /// shared and heavy.
    fn store(&mut self, n: usize, f: Fmt, info: Info, out: &mut Vec<(Fmt, Info)>) {
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
    pp_term_with(nodes, root, assoc, &BTreeMap::new(), 0)
}

/// [`pp_term`] with quantifier nodes (`binders`), laid out at indentation
/// `ind` as `ast_smt2_pp(…, indent)` does: the first line starts at the
/// current column, the following ones are indented.
pub fn pp_term_with(
    nodes: &[PpNode],
    root: usize,
    assoc: &dyn Fn(&str) -> bool,
    binders: &BTreeMap<usize, PpBinder>,
    ind: usize,
) -> String {
    let shared = shared_nodes(nodes, root);
    let (doc, _, _) = let_doc(nodes, root, &shared, assoc, binders);
    layout(&indent(ind, doc))
}

/// The document of node `root` in an alias scope of its own, wrapped in the
/// `let`s of the aliases it introduced (`pp_let`), with its summary and the
/// number of aliases.
fn let_doc(
    nodes: &[PpNode],
    root: usize,
    shared: &BTreeSet<usize>,
    assoc: &dyn Fn(&str) -> bool,
    binders: &BTreeMap<usize, PpBinder>,
) -> (Fmt, Info, u32) {
    let mut p = Printer {
        nodes,
        root,
        shared,
        assoc,
        binders,
        alias: BTreeMap::new(),
        alias_defs: Vec::new(),
        next_alias: 1,
    };
    let mut out = Vec::new();
    p.visit(root, None, &mut out);
    let leaf = Info {
        lvl: 0,
        weight: 1,
        depth: 1,
    };
    let (body, info) = out.pop().unwrap_or_else(|| (s(""), leaf));
    if p.alias_defs.is_empty() {
        return (body, info, 0);
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
    (Fmt::Compose(buf), info, p.alias_defs.len() as u32)
}

/// A function interpretation as z3's `model_smt2_pp` (`pp_funs`) prints it in
/// a model listed at indentation 2: `(define-fun f ((x!0 S) …) R` then the
/// body, which is the `else` value preceded by one `(ite cond result` per
/// entry. `params` are the rendered domain sorts, each entry is `(argument
/// values, result)` and every value is already rendered. Returns the text
/// including its leading indentation and without a trailing newline.
pub fn pp_func_interp(
    name: &str,
    params: &[String],
    range: &str,
    entries: &[(Vec<String>, String)],
    els: &str,
) -> String {
    const TAB: usize = 2;
    let vars: Vec<String> = (0..params.len()).map(|i| alloc::format!("x!{i}")).collect();
    let mut body = s(els);
    if !entries.is_empty() {
        let mut parts: Vec<Fmt> = Vec::new();
        for (i, (args, result)) in entries.iter().enumerate() {
            let mut conds: Vec<Fmt> = args
                .iter()
                .zip(&vars)
                .map(|(a, v)| seq1(vec![s(v), s(a)], "="))
                .collect();
            let cond = if conds.len() > 1 {
                seq1(conds, "and")
            } else {
                conds.pop().unwrap_or_else(|| s("true"))
            };
            if i > 0 {
                parts.push(Fmt::LineBreak);
            }
            parts.push(group(Fmt::Compose(vec![
                s("(ite "),
                indent(5, cond),
                indent(TAB, Fmt::Compose(vec![Fmt::LineBreak, s(result)])),
            ])));
        }
        parts.push(indent(TAB, Fmt::Compose(vec![Fmt::LineBreak, body])));
        for _ in entries {
            parts.push(s(")"));
        }
        body = Fmt::Compose(parts);
    }
    let decls: Vec<Fmt> = params
        .iter()
        .zip(&vars)
        .map(|(p, v)| seq5(vec![s(v), s(p)]))
        .collect();
    let def = indent(
        TAB,
        Fmt::Compose(vec![
            s("(define-fun "),
            s(name),
            s(" "),
            seq5(decls),
            s(" "),
            s(range),
            indent(TAB, Fmt::Compose(vec![Fmt::LineBreak, body, s(")")])),
        ]),
    );
    alloc::format!("  {}", layout(&def))
}

/// An already-rendered value term (an objective value such as
/// `(+ (root-obj …) (* (- 1.0) epsilon))`) laid out as z3 prints the
/// expression on its own: 80 columns from its first character. Numerals —
/// `root-obj`, `(- n)`, `(/ p q)` and their negations — are single literals
/// as in z3's printer. Text that is not a well-formed s-expression, or
/// that quotes a symbol or string, is returned unchanged.
pub fn pp_value(text: &str) -> String {
    /// Parse one s-expression from `t` at `*i` into `arena`; its index.
    fn parse(t: &[u8], i: &mut usize, src: &str, arena: &mut Vec<PpNode>) -> Option<usize> {
        while *i < t.len() && t[*i] == b' ' {
            *i += 1;
        }
        let start = *i;
        if *i >= t.len() || t[*i] == b')' {
            return None;
        }
        if t[*i] != b'(' {
            while *i < t.len() && !matches!(t[*i], b' ' | b'(' | b')') {
                *i += 1;
            }
            arena.push(PpNode {
                head: String::from(&src[start..*i]),
                args: Vec::new(),
                indexed: false,
            });
            return Some(arena.len() - 1);
        }
        *i += 1;
        let first_node = arena.len();
        let h0 = *i;
        while *i < t.len() && !matches!(t[*i], b' ' | b'(' | b')') {
            *i += 1;
        }
        let head = String::from(&src[h0..*i]);
        let mut args = Vec::new();
        loop {
            while *i < t.len() && t[*i] == b' ' {
                *i += 1;
            }
            if *i >= t.len() {
                return None;
            }
            if t[*i] == b')' {
                *i += 1;
                break;
            }
            args.push(parse(t, i, src, arena)?);
        }
        let leaf = |a: &usize| arena[*a].args.is_empty();
        let numeral = head == "root-obj"
            || (head == "/" && args.len() == 2 && args.iter().all(leaf))
            || (head == "-" && args.len() == 1 && args.iter().all(leaf));
        if numeral {
            arena.truncate(first_node);
            arena.push(PpNode {
                head: String::from(&src[start..*i]),
                args: Vec::new(),
                indexed: false,
            });
        } else {
            arena.push(PpNode {
                head,
                args,
                indexed: false,
            });
        }
        Some(arena.len() - 1)
    }
    // Quoted symbols and string literals may hold spaces: keep them as is.
    if text.contains(['"', '|']) {
        return String::from(text);
    }
    let mut arena = Vec::new();
    let mut i = 0;
    match parse(text.as_bytes(), &mut i, text, &mut arena) {
        Some(root) if i == text.len() && root + 1 == arena.len() => {
            pp_term(&arena, root, &|_| false)
        }
        _ => String::from(text),
    }
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

    #[test]
    fn long_values_wrap_with_numerals_as_literals() {
        let v =
            "(+ (root-obj (+ (* 3 (^ x 3)) (* 9 (^ x 2)) (* 9 x) (- 125)) 1) (* (- 1.0) epsilon))";
        assert_eq!(
            pp_value(v),
            "(+ (root-obj (+ (* 3 (^ x 3)) (* 9 (^ x 2)) (* 9 x) (- 125)) 1)\n   (* (- 1.0) epsilon))"
        );
        assert_eq!(pp_value("(+ 7.0 epsilon)"), "(+ 7.0 epsilon)");
        assert_eq!(pp_value("(- 2)"), "(- 2)");
        assert_eq!(pp_value("oo"), "oo");
    }
}
