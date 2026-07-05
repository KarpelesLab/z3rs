//! A finite-domain Datalog engine — the core of Z3's `-dl` frontend
//! (`z3/src/muz/rel` + `z3/src/muz/datalog_frontend`, Z3 4.17.0, MIT).
//!
//! This is the classic bottom-up least-fixpoint evaluator over a finite
//! Herbrand universe: relations are sets of ground tuples, rules are Horn
//! clauses `head :- body₁, …, bodyₙ`, and evaluation iterates the immediate
//! consequence operator to a fixpoint (naïve evaluation — correct and
//! terminating for the finite, function-free fragment Datalog targets). It backs
//! the `-dl` frontend and answers ground/open queries.
//!
//! ## Syntax accepted by [`parse`]
//! ```text
//! % line comments start with % or #
//! edge(1, 2).                       % a fact
//! path(X, Y) :- edge(X, Y).         % a rule; Uppercase = variable
//! path(X, Z) :- edge(X, Y), path(Y, Z).
//! ?- path(1, 3).                    % a query (ground or with variables)
//! ```
//! Constants are integers or lowercase identifiers; variables start uppercase.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::{String, ToString};
use alloc::vec::Vec;

/// A term in a rule: either a bound variable (by name) or a ground constant.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Term {
    Var(String),
    Const(String),
}

/// A relational atom `pred(t₁, …, tₙ)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Atom {
    pub pred: String,
    pub args: Vec<Term>,
}

/// A Horn rule `head :- body`. An empty body makes it a fact.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rule {
    pub head: Atom,
    pub body: Vec<Atom>,
}

/// A parsed Datalog program: its rules/facts and any queries.
#[derive(Clone, Debug, Default)]
pub struct Program {
    pub rules: Vec<Rule>,
    pub queries: Vec<Atom>,
}

/// A ground tuple of constant symbols.
pub type Tuple = Vec<String>;

/// The computed least model: for each predicate, its set of ground tuples.
#[derive(Clone, Debug, Default)]
pub struct Model {
    rels: BTreeMap<String, BTreeSet<Tuple>>,
}

impl Model {
    /// The tuples of `pred` (empty if the predicate is unknown/empty).
    pub fn relation(&self, pred: &str) -> Vec<Tuple> {
        self.rels
            .get(pred)
            .map(|s| s.iter().cloned().collect())
            .unwrap_or_default()
    }

    /// Answer a query atom: all substitutions of its variables making it hold,
    /// as `(var → const)` maps. A ground query yields one empty map if derivable,
    /// none otherwise.
    pub fn query(&self, atom: &Atom) -> Vec<BTreeMap<String, String>> {
        let Some(tuples) = self.rels.get(&atom.pred) else {
            return Vec::new();
        };
        let mut out = Vec::new();
        for t in tuples {
            if t.len() != atom.args.len() {
                continue;
            }
            let mut subst = BTreeMap::new();
            if unify(&atom.args, t, &mut subst) {
                out.push(subst);
            }
        }
        out
    }

    /// Is `atom` (ground) derivable?
    pub fn holds(&self, atom: &Atom) -> bool {
        !self.query(atom).is_empty()
    }
}

/// Try to match rule terms against a ground tuple, extending `subst`.
fn unify(args: &[Term], tuple: &[String], subst: &mut BTreeMap<String, String>) -> bool {
    for (a, c) in args.iter().zip(tuple) {
        match a {
            Term::Const(k) => {
                if k != c {
                    return false;
                }
            }
            Term::Var(v) => match subst.get(v) {
                Some(bound) if bound != c => return false,
                Some(_) => {}
                None => {
                    subst.insert(v.clone(), c.clone());
                }
            },
        }
    }
    true
}

/// Evaluate a program to its least fixpoint (naïve bottom-up evaluation).
pub fn evaluate(program: &Program) -> Model {
    let mut model = Model::default();
    // Ensure every head predicate exists (possibly empty).
    for r in &program.rules {
        model.rels.entry(r.head.pred.clone()).or_default();
    }
    loop {
        let mut changed = false;
        for rule in &program.rules {
            // Collect all satisfying substitutions of the body, then instantiate
            // the head.
            let substs = match_body(&model, &rule.body);
            for subst in substs {
                if let Some(tuple) = ground_head(&rule.head, &subst) {
                    let set = model.rels.entry(rule.head.pred.clone()).or_default();
                    if set.insert(tuple) {
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }
    model
}

/// All variable bindings under which every body atom holds in the current model.
fn match_body(model: &Model, body: &[Atom]) -> Vec<BTreeMap<String, String>> {
    let mut frontier = alloc::vec![BTreeMap::new()];
    for atom in body {
        let empty = BTreeSet::new();
        let tuples = model.rels.get(&atom.pred).unwrap_or(&empty);
        let mut next = Vec::new();
        for subst in &frontier {
            for t in tuples {
                if t.len() != atom.args.len() {
                    continue;
                }
                let mut s = subst.clone();
                if unify(&atom.args, t, &mut s) {
                    next.push(s);
                }
            }
        }
        frontier = next;
        if frontier.is_empty() {
            break;
        }
    }
    frontier
}

/// Instantiate a head atom under a substitution; `None` if a variable is unbound
/// (an unsafe rule — a variable in the head not covered by the body).
fn ground_head(head: &Atom, subst: &BTreeMap<String, String>) -> Option<Tuple> {
    let mut tuple = Vec::with_capacity(head.args.len());
    for a in &head.args {
        match a {
            Term::Const(k) => tuple.push(k.clone()),
            Term::Var(v) => tuple.push(subst.get(v)?.clone()),
        }
    }
    Some(tuple)
}

// --- parser ---------------------------------------------------------------

/// Parse a Datalog program in the syntax documented on this module.
pub fn parse(input: &str) -> Result<Program, String> {
    // Strip comments, then split into clauses terminated by `.`.
    let mut cleaned = String::new();
    for line in input.lines() {
        let line = match line.find(['%', '#']) {
            Some(i) => &line[..i],
            None => line,
        };
        cleaned.push_str(line);
        cleaned.push('\n');
    }
    let mut program = Program::default();
    for raw in cleaned.split('.') {
        let clause = raw.trim();
        if clause.is_empty() {
            continue;
        }
        if let Some(q) = clause.strip_prefix("?-") {
            program.queries.push(parse_atom(q.trim())?);
        } else if let Some((head, body)) = clause.split_once(":-") {
            let head = parse_atom(head.trim())?;
            let body = parse_atom_list(body.trim())?;
            program.rules.push(Rule { head, body });
        } else {
            // A bare fact.
            program.rules.push(Rule {
                head: parse_atom(clause)?,
                body: Vec::new(),
            });
        }
    }
    Ok(program)
}

/// Split a comma-separated atom list at top level (commas inside `()` are args).
fn parse_atom_list(s: &str) -> Result<Vec<Atom>, String> {
    let mut atoms = Vec::new();
    let mut depth = 0i32;
    let mut start = 0usize;
    let bytes = s.as_bytes();
    for (i, &b) in bytes.iter().enumerate() {
        match b {
            b'(' => depth += 1,
            b')' => depth -= 1,
            b',' if depth == 0 => {
                atoms.push(parse_atom(s[start..i].trim())?);
                start = i + 1;
            }
            _ => {}
        }
    }
    let tail = s[start..].trim();
    if !tail.is_empty() {
        atoms.push(parse_atom(tail)?);
    }
    Ok(atoms)
}

fn parse_atom(s: &str) -> Result<Atom, String> {
    let s = s.trim();
    let open = s.find('(').ok_or_else(|| format_err("expected '(' in atom", s))?;
    if !s.ends_with(')') {
        return Err(format_err("atom must end with ')'", s));
    }
    let pred = s[..open].trim().to_string();
    if pred.is_empty() {
        return Err(format_err("empty predicate name", s));
    }
    let inside = &s[open + 1..s.len() - 1];
    let mut args = Vec::new();
    for a in inside.split(',') {
        let a = a.trim();
        if a.is_empty() {
            return Err(format_err("empty argument", s));
        }
        args.push(parse_term(a));
    }
    Ok(Atom { pred, args })
}

fn parse_term(s: &str) -> Term {
    let first = s.chars().next().unwrap();
    if first.is_ascii_uppercase() || first == '_' {
        Term::Var(s.to_string())
    } else {
        Term::Const(s.to_string())
    }
}

fn format_err(msg: &str, ctx: &str) -> String {
    alloc::format!("datalog parse error: {msg} (in {ctx:?})")
}

#[cfg(test)]
mod tests {
    use super::*;

    const REACH: &str = "
        edge(1, 2).
        edge(2, 3).
        edge(3, 4).
        path(X, Y) :- edge(X, Y).
        path(X, Z) :- edge(X, Y), path(Y, Z).
    ";

    #[test]
    fn transitive_closure() {
        let prog = parse(REACH).unwrap();
        let model = evaluate(&prog);
        let ground = |x: &str, y: &str| Atom {
            pred: "path".into(),
            args: alloc::vec![Term::Const(x.into()), Term::Const(y.into())],
        };
        assert!(model.holds(&ground("1", "4")));
        assert!(model.holds(&ground("2", "4")));
        assert!(!model.holds(&ground("4", "1"))); // no back edges
        assert!(!model.holds(&ground("1", "1")));
    }

    #[test]
    fn open_query_enumerates_solutions() {
        let prog = parse(REACH).unwrap();
        let model = evaluate(&prog);
        // ?- path(1, Y): reachable from 1 are 2,3,4.
        let q = Atom {
            pred: "path".into(),
            args: alloc::vec![Term::Const("1".into()), Term::Var("Y".into())],
        };
        let mut ys: Vec<String> = model.query(&q).into_iter().map(|m| m["Y"].clone()).collect();
        ys.sort();
        assert_eq!(ys, alloc::vec!["2", "3", "4"]);
    }

    #[test]
    fn parses_facts_rules_and_queries() {
        let prog = parse(REACH.to_string().as_str()).unwrap();
        // 3 edges + 2 rules.
        assert_eq!(prog.rules.len(), 5);
        let prog2 = parse("p(a).\n?- p(a).\n?- p(b).").unwrap();
        assert_eq!(prog2.queries.len(), 2);
        let m = evaluate(&prog2);
        assert!(m.holds(&prog2.queries[0]));
        assert!(!m.holds(&prog2.queries[1]));
    }

    #[test]
    fn rejects_malformed() {
        assert!(parse("p(a").is_err()); // missing ')'
        assert!(parse("p()").is_err()); // empty argument list
        assert!(parse("(a)").is_err()); // empty predicate name
    }
}
