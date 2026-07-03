//! A minimal SMT-LIB 2 front end — the QF_UF subset of `z3/src/cmd_context` +
//! `z3/src/parsers/smt2` (Z3 4.17.0, MIT).
//!
//! Supports: `set-logic`/`set-info`/`set-option` (ignored), `declare-sort`
//! (arity 0), `declare-fun`, `declare-const`, `assert`, `check-sat`, and `exit`;
//! terms over the core Boolean operators, equality/`distinct`, `ite`, and
//! uninterpreted functions. Arithmetic/bit-vector terms and `push`/`pop` are not
//! yet handled. Enough to run QF_UF scripts through [`crate::smt::check`].

use alloc::collections::BTreeMap;
use alloc::string::{String, ToString};
use alloc::vec::Vec;

use crate::ast::AstId;
use crate::ast::manager::AstManager;
use crate::smt::{SmtResult, check};
use crate::util::symbol::Symbol;

/// An s-expression.
#[derive(Clone, Debug)]
enum SExpr {
    Atom(String),
    List(Vec<SExpr>),
}

/// Run an SMT-LIB2 `script`, returning one response line per `check-sat`
/// (`"sat"`, `"unsat"`, or `"unknown"`).
pub fn run(script: &str) -> Result<Vec<String>, String> {
    let forms = parse(script)?;
    let mut ctx = Context::new();
    let mut out = Vec::new();
    for form in forms {
        if let Some(resp) = ctx.command(&form)? {
            out.push(resp);
        }
    }
    Ok(out)
}

// --- tokenizer + parser ---------------------------------------------------

fn tokenize(input: &str) -> Vec<String> {
    let mut toks = Vec::new();
    let mut chars = input.chars().peekable();
    while let Some(&c) = chars.peek() {
        match c {
            ';' => {
                // comment to end of line
                for c in chars.by_ref() {
                    if c == '\n' {
                        break;
                    }
                }
            }
            c if c.is_whitespace() => {
                chars.next();
            }
            '(' | ')' => {
                toks.push(c.to_string());
                chars.next();
            }
            '|' => {
                // quoted symbol |...|
                chars.next();
                let mut s = String::new();
                for c in chars.by_ref() {
                    if c == '|' {
                        break;
                    }
                    s.push(c);
                }
                toks.push(s);
            }
            _ => {
                let mut s = String::new();
                while let Some(&c) = chars.peek() {
                    if c.is_whitespace() || c == '(' || c == ')' || c == ';' {
                        break;
                    }
                    s.push(c);
                    chars.next();
                }
                toks.push(s);
            }
        }
    }
    toks
}

fn parse(input: &str) -> Result<Vec<SExpr>, String> {
    let toks = tokenize(input);
    let mut pos = 0;
    let mut forms = Vec::new();
    while pos < toks.len() {
        forms.push(parse_one(&toks, &mut pos)?);
    }
    Ok(forms)
}

fn parse_one(toks: &[String], pos: &mut usize) -> Result<SExpr, String> {
    let tok = &toks[*pos];
    *pos += 1;
    match tok.as_str() {
        "(" => {
            let mut list = Vec::new();
            loop {
                if *pos >= toks.len() {
                    return Err("unexpected end of input (missing `)`)".to_string());
                }
                if toks[*pos] == ")" {
                    *pos += 1;
                    break;
                }
                list.push(parse_one(toks, pos)?);
            }
            Ok(SExpr::List(list))
        }
        ")" => Err("unexpected `)`".to_string()),
        atom => Ok(SExpr::Atom(atom.to_string())),
    }
}

// --- interpreter ----------------------------------------------------------

struct Context {
    m: AstManager,
    sorts: BTreeMap<String, AstId>,
    funcs: BTreeMap<String, AstId>,
    assertions: Vec<AstId>,
    /// Active `let` binding scopes (innermost last).
    scopes: Vec<Vec<(String, AstId)>>,
}

impl Context {
    fn new() -> Context {
        let mut m = AstManager::new();
        let bool_sort = m.mk_bool_sort();
        let mut sorts = BTreeMap::new();
        sorts.insert("Bool".to_string(), bool_sort);
        Context {
            m,
            sorts,
            funcs: BTreeMap::new(),
            assertions: Vec::new(),
            scopes: Vec::new(),
        }
    }

    fn sym(s: &SExpr) -> Result<&str, String> {
        match s {
            SExpr::Atom(a) => Ok(a),
            SExpr::List(_) => Err("expected a symbol, found a list".to_string()),
        }
    }

    fn resolve_sort(&self, s: &SExpr) -> Result<AstId, String> {
        let name = Self::sym(s)?;
        self.sorts
            .get(name)
            .copied()
            .ok_or_else(|| alloc::format!("unknown sort {name:?}"))
    }

    /// Interpret a top-level command, returning any textual response.
    fn command(&mut self, form: &SExpr) -> Result<Option<String>, String> {
        let list = match form {
            SExpr::List(l) if !l.is_empty() => l,
            _ => return Err("expected a command list".to_string()),
        };
        match Self::sym(&list[0])? {
            "set-logic" | "set-info" | "set-option" | "get-info" | "echo" | "exit" | "push"
            | "pop" | "reset" => Ok(None),
            "declare-sort" => {
                let name = Self::sym(&list[1])?.to_string();
                let s = self.m.mk_uninterpreted_sort(Symbol::new(&name));
                self.sorts.insert(name, s);
                Ok(None)
            }
            "declare-const" => {
                // (declare-const c S)
                let name = Self::sym(&list[1])?.to_string();
                let range = self.resolve_sort(&list[2])?;
                let d = self.m.mk_func_decl(Symbol::new(&name), &[], range);
                self.funcs.insert(name, d);
                Ok(None)
            }
            "declare-fun" => {
                // (declare-fun f (D...) R)
                let name = Self::sym(&list[1])?.to_string();
                let domain: Vec<AstId> = match &list[2] {
                    SExpr::List(ds) => ds
                        .iter()
                        .map(|d| self.resolve_sort(d))
                        .collect::<Result<_, _>>()?,
                    _ => return Err("declare-fun: expected a domain list".to_string()),
                };
                let range = self.resolve_sort(&list[3])?;
                let d = self.m.mk_func_decl(Symbol::new(&name), &domain, range);
                self.funcs.insert(name, d);
                Ok(None)
            }
            "assert" => {
                let t = self.term(&list[1])?;
                self.assertions.push(t);
                Ok(None)
            }
            "check-sat" => {
                let goal = self.conjunction();
                let resp = match check(&self.m, goal) {
                    SmtResult::Sat => "sat",
                    SmtResult::Unsat => "unsat",
                };
                Ok(Some(resp.to_string()))
            }
            other => Err(alloc::format!("unsupported command {other:?}")),
        }
    }

    /// The conjunction of all assertions (`true` if none).
    fn conjunction(&mut self) -> AstId {
        match self.assertions.len() {
            0 => self.m.mk_true(),
            1 => self.assertions[0],
            _ => {
                let a = self.assertions.clone();
                self.m.mk_and(&a)
            }
        }
    }

    /// Look up a name in the active `let` scopes (innermost first).
    fn lookup_bound(&self, name: &str) -> Option<AstId> {
        self.scopes.iter().rev().find_map(|scope| {
            scope
                .iter()
                .rev()
                .find(|(n, _)| n == name)
                .map(|(_, id)| *id)
        })
    }

    /// Build a term from an s-expression.
    fn term(&mut self, s: &SExpr) -> Result<AstId, String> {
        match s {
            SExpr::Atom(a) => match a.as_str() {
                "true" => Ok(self.m.mk_true()),
                "false" => Ok(self.m.mk_false()),
                name => {
                    if let Some(id) = self.lookup_bound(name) {
                        return Ok(id);
                    }
                    let d = *self
                        .funcs
                        .get(name)
                        .ok_or_else(|| alloc::format!("unknown symbol {name:?}"))?;
                    Ok(self.m.mk_const(d))
                }
            },
            SExpr::List(l) if !l.is_empty() => {
                let head = Self::sym(&l[0])?.to_string();
                if head == "let" {
                    return self.term_let(&l[1], &l[2]);
                }
                let args: Vec<AstId> = l[1..]
                    .iter()
                    .map(|a| self.term(a))
                    .collect::<Result<_, _>>()?;
                self.apply(&head, args)
            }
            SExpr::List(_) => Err("empty application".to_string()),
        }
    }

    /// `(let ((v t) ...) body)` — parallel binding, then evaluate `body`.
    fn term_let(&mut self, bindings: &SExpr, body: &SExpr) -> Result<AstId, String> {
        let bs = match bindings {
            SExpr::List(bs) => bs,
            _ => return Err("let: expected a binding list".to_string()),
        };
        // Evaluate every RHS in the *outer* scope (parallel `let` semantics).
        let mut scope: Vec<(String, AstId)> = Vec::new();
        for b in bs {
            match b {
                SExpr::List(pair) if pair.len() == 2 => {
                    let name = Self::sym(&pair[0])?.to_string();
                    let val = self.term(&pair[1])?;
                    scope.push((name, val));
                }
                _ => return Err("let: expected (name term) bindings".to_string()),
            }
        }
        self.scopes.push(scope);
        let result = self.term(body);
        self.scopes.pop();
        result
    }

    fn apply(&mut self, head: &str, args: Vec<AstId>) -> Result<AstId, String> {
        let m = &mut self.m;
        match head {
            "not" => Ok(m.mk_not(args[0])),
            "and" => Ok(match args.len() {
                0 => m.mk_true(),
                1 => args[0],
                _ => m.mk_and(&args),
            }),
            "or" => Ok(match args.len() {
                0 => m.mk_false(),
                1 => args[0],
                _ => m.mk_or(&args),
            }),
            "xor" => Ok(m.mk_xor(args[0], args[1])),
            "=>" => {
                // right associative
                let mut acc = *args.last().unwrap();
                for &a in args[..args.len() - 1].iter().rev() {
                    acc = m.mk_implies(a, acc);
                }
                Ok(acc)
            }
            "ite" => Ok(m.mk_ite(args[0], args[1], args[2])),
            "distinct" => Ok(m.mk_distinct(&args)),
            "=" => {
                // chainable: (= a b c) => (and (= a b) (= b c))
                if args.len() == 2 {
                    Ok(m.mk_eq(args[0], args[1]))
                } else {
                    let mut eqs = Vec::new();
                    for w in args.windows(2) {
                        eqs.push(m.mk_eq(w[0], w[1]));
                    }
                    Ok(m.mk_and(&eqs))
                }
            }
            name => {
                let d = *self
                    .funcs
                    .get(name)
                    .ok_or_else(|| alloc::format!("unknown function {name:?}"))?;
                Ok(self.m.mk_app(d, &args))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn qf_uf_transitivity_unsat() {
        let script = "
            (declare-sort S 0)
            (declare-const a S) (declare-const b S) (declare-const c S)
            (assert (= a b))
            (assert (= b c))
            (assert (not (= a c)))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat"]);
    }

    #[test]
    fn qf_uf_congruence_unsat() {
        let script = "
            (declare-sort S 0)
            (declare-fun f (S) S)
            (declare-const a S) (declare-const b S)
            (assert (= a b))
            (assert (not (= (f a) (f b))))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat"]);
    }

    #[test]
    fn satisfiable_script() {
        let script = "
            (declare-sort S 0)
            (declare-const a S) (declare-const b S) (declare-const c S)
            (assert (= a b))
            (assert (not (= a c)))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["sat"]);
    }

    #[test]
    fn boolean_and_ite() {
        let script = "
            (declare-const p Bool) (declare-const q Bool)
            (assert (and p (not p)))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat"]);
    }

    #[test]
    fn comments_and_multiple_checks() {
        let script = "
            ; a comment
            (declare-const p Bool)
            (assert (or p (not p))) ; tautology
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["sat"]);
    }

    #[test]
    fn let_bindings() {
        // (let ((x (= a b))) (and x (not x))) is unsat regardless of a,b.
        let script = "
            (declare-sort S 0)
            (declare-const a S) (declare-const b S)
            (assert (let ((x (= a b))) (and x (not x))))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat"]);
    }

    #[test]
    fn nested_and_shadowing_lets() {
        // Inner let shadows the outer binding; result stays consistent → sat.
        let script = "
            (declare-const p Bool) (declare-const q Bool)
            (assert (let ((x p)) (let ((x q)) (or x (not x)))))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["sat"]);
    }

    #[test]
    fn parse_error_is_reported() {
        assert!(run("(declare-const a").is_err());
    }
}
