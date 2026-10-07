//! Displayed frozen-Oracle expression shape and lexical identity only.
//! No scheme, typed capture, runtime closure, or semantic acceptance comparison.
use super::*;
use crate::shadow::*;
use std::collections::{HashMap, HashSet};

// Exact captured input bytes; SHA-256 is recorded in the frozen probe note.
const SOURCE: &str = "my apply f = { my step x = f x; step }\n";
// Frozen Oracle a58eefc31e22141574b6f20c6a5748151c6d79f1, recorded in
// notes/progress/2026-10-06-frozen-oracle-rebuild-and-source-probes.md:70–79.
const DUMP: &str = "my d0:apply: ('a -> ['b] 'c) -> 'a -> ['b] 'c = e6:(fn p0:d1:f -> e5:block { let my p1:d2:step = e3:(fn p2:d3:x -> e2:(e0:r0:f->d1:f e1:r1:x->d3:x)); e4:r2:step->d2:step })\n";
const HEADER: &str = "my d0:apply: ('a -> ['b] 'c) -> 'a -> ['b] 'c = ";

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
enum Lexical {
    Apply,
    F,
    Step,
    X,
}
fn lexical(name: &str) -> Result<Lexical, String> {
    match name {
        "apply" => Ok(Lexical::Apply),
        "f" => Ok(Lexical::F),
        "step" => Ok(Lexical::Step),
        "x" => Ok(Lexical::X),
        _ => Err(format!("unsupported name {name}")),
    }
}
#[derive(Debug, Eq, PartialEq)]
enum Tree {
    Lambda(Lexical, Box<Tree>),
    Bind(Lexical, Box<Tree>, Box<Tree>),
    Apply(Box<Tree>, Box<Tree>),
    Use(Lexical),
}

// This restricted reader consumes the old expression independently. Allocation
// labels are retained for uniqueness/edge checks, then replaced by lexical roles.
struct Legacy<'a> {
    rest: &'a str,
    binders: HashMap<&'a str, Lexical>,
    parameters: HashSet<&'a str>,
    expressions: HashSet<&'a str>,
    uses: HashSet<&'a str>,
}
impl<'a> Legacy<'a> {
    fn eat(&mut self, text: &str) -> Result<(), String> {
        self.rest = self
            .rest
            .strip_prefix(text)
            .ok_or_else(|| format!("expected {text:?} at {:?}", self.rest))?;
        Ok(())
    }
    fn id(&mut self, prefix: char) -> Result<&'a str, String> {
        let n = self
            .rest
            .bytes()
            .skip(1)
            .take_while(u8::is_ascii_digit)
            .count();
        if !self.rest.starts_with(prefix) || n == 0 {
            return Err(format!("expected {prefix} identity"));
        }
        let (id, rest) = self.rest.split_at(n + 1);
        self.rest = rest;
        Ok(id)
    }
    fn name(&mut self) -> Result<Lexical, String> {
        let n = self
            .rest
            .bytes()
            .take_while(u8::is_ascii_alphabetic)
            .count();
        let (name, rest) = self.rest.split_at(n);
        self.rest = rest;
        lexical(name)
    }
    fn declaration(&mut self) -> Result<Lexical, String> {
        let p = self.id('p')?;
        if !self.parameters.insert(p) {
            return Err("duplicate parameter identity".into());
        }
        self.eat(":")?;
        let d = self.id('d')?;
        self.eat(":")?;
        let name = self.name()?;
        if self.binders.values().any(|&old| old == name) || self.binders.insert(d, name).is_some() {
            return Err("duplicate binder identity".into());
        }
        Ok(name)
    }
    fn expression(&mut self) -> Result<Tree, String> {
        let e = self.id('e')?;
        if !self.expressions.insert(e) {
            return Err("duplicate expression identity".into());
        }
        self.eat(":")?;
        if self.rest.starts_with("(fn ") {
            self.eat("(fn ")?;
            let parameter = self.declaration()?;
            self.eat(" -> ")?;
            let body = self.expression()?;
            self.eat(")")?;
            Ok(Tree::Lambda(parameter, Box::new(body)))
        } else if self.rest.starts_with("block ") {
            self.eat("block { let my ")?;
            let binder = self.declaration()?;
            self.eat(" = ")?;
            let value = self.expression()?;
            self.eat("; ")?;
            let body = self.expression()?;
            self.eat(" }")?;
            Ok(Tree::Bind(binder, Box::new(value), Box::new(body)))
        } else if self.rest.starts_with('(') {
            self.eat("(")?;
            let callee = self.expression()?;
            self.eat(" ")?;
            let argument = self.expression()?;
            self.eat(")")?;
            Ok(Tree::Apply(Box::new(callee), Box::new(argument)))
        } else {
            let r = self.id('r')?;
            if !self.uses.insert(r) {
                return Err("duplicate use identity".into());
            }
            self.eat(":")?;
            let name = self.name()?;
            self.eat("->")?;
            let target = self.id('d')?;
            self.eat(":")?;
            if self.name()? != name || self.binders.get(target) != Some(&name) {
                return Err("unresolved or inconsistent use edge".into());
            }
            Ok(Tree::Use(name))
        }
    }
}
fn legacy(dump: &str) -> Result<Tree, String> {
    // Require the captured output's one line ending. The entire pinned header
    // is consumed, without interpreting its scheme.
    let dump = dump
        .strip_suffix('\n')
        .ok_or("missing captured output LF")?;
    let mut reader = Legacy {
        rest: dump.strip_prefix(HEADER).ok_or("unsupported dump header")?,
        binders: HashMap::from([("d0", Lexical::Apply)]),
        parameters: HashSet::new(),
        expressions: HashSet::new(),
        uses: HashSet::new(),
    };
    let tree = reader.expression()?;
    if !reader.rest.is_empty() {
        return Err("trailing dump material".into());
    }
    if (
        reader.binders.len(),
        reader.parameters.len(),
        reader.expressions.len(),
        reader.uses.len(),
    ) != (4, 3, 7, 3)
    {
        return Err("unexpected identity cardinalities".into());
    }
    Ok(tree)
}

fn shadow_tree(
    skeleton: &Skeleton,
    id: &ExprId,
    binders: &[(BinderId, Lexical)],
    expressions: &mut Vec<ExprId>,
    uses: &mut Vec<UseId>,
) -> Tree {
    assert!(!expressions.contains(id), "distinct expression identity");
    expressions.push(id.clone());
    let role = |id: &BinderId| binders.iter().find(|(key, _)| key == id).unwrap().1;
    match skeleton.expression(id).unwrap().form() {
        Form::Lambda {
            binding,
            parameter,
            body,
            ..
        } => {
            let parameter = role(parameter);
            assert_eq!(
                role(binding),
                match parameter {
                    Lexical::F => Lexical::Apply,
                    Lexical::X => Lexical::Step,
                    _ => panic!("unsupported lambda"),
                }
            );
            Tree::Lambda(
                parameter,
                Box::new(shadow_tree(skeleton, body, binders, expressions, uses)),
            )
        }
        Form::Bind {
            binder,
            value,
            body,
        } => Tree::Bind(
            role(binder),
            Box::new(shadow_tree(skeleton, value, binders, expressions, uses)),
            Box::new(shadow_tree(skeleton, body, binders, expressions, uses)),
        ),
        Form::Apply {
            callee, argument, ..
        } => Tree::Apply(
            Box::new(shadow_tree(skeleton, callee, binders, expressions, uses)),
            Box::new(shadow_tree(skeleton, argument, binders, expressions, uses)),
        ),
        Form::Use { binder, occurrence } => {
            assert!(!uses.contains(occurrence), "distinct use identity");
            uses.push(occurrence.clone());
            assert!(std::ptr::eq(
                skeleton.use_expression(occurrence).unwrap(),
                skeleton.expression(id).unwrap()
            ));
            Tree::Use(role(binder))
        }
        _ => panic!("unsupported shadow expression"),
    }
}

#[test]
fn shadow_legacy_apply_structure_matches_displayed_shape_and_lexical_identity_only() {
    assert_eq!(
        SOURCE.as_bytes(),
        b"my apply f = { my step x = f x; step }\n"
    );
    let old = legacy(DUMP).unwrap();
    let call = Tree::Apply(
        Box::new(Tree::Use(Lexical::F)),
        Box::new(Tree::Use(Lexical::X)),
    );
    let local = Tree::Lambda(Lexical::X, Box::new(call));
    let block = Tree::Bind(
        Lexical::Step,
        Box::new(local),
        Box::new(Tree::Use(Lexical::Step)),
    );
    let expected = Tree::Lambda(Lexical::F, Box::new(block));
    assert_eq!(old, expected);
    assert!(legacy(&format!("{DUMP} trailing\n")).is_err());
    assert!(legacy(&DUMP.replace("e2:(", "e2:unsupported(")).is_err());
    assert!(legacy(&DUMP.replace("r1:x->d3:x", "r1:x->d1:f")).is_err());
    assert!(legacy(&DUMP.replace("e1:r1", "e0:r1")).is_err());
    assert!(legacy(&DUMP.replace("e1:r1", "e1:r0")).is_err());
    let artifact = ShadowArtifact::from_parsed(parsed(SOURCE)).unwrap();
    assert_eq!(artifact.source().as_bytes(), SOURCE.as_bytes());
    let skeleton = artifact.skeleton().unwrap();
    let binders = skeleton
        .binder_ids()
        .into_iter()
        .map(|id| {
            let name = lexical(skeleton.binder(&id).unwrap().name()).unwrap();
            (id, name)
        })
        .collect::<Vec<_>>();
    assert_eq!(binders.len(), 4);
    assert_eq!(
        binders
            .iter()
            .map(|(_, role)| *role)
            .collect::<HashSet<_>>(),
        HashSet::from([Lexical::Apply, Lexical::F, Lexical::Step, Lexical::X])
    );
    let mut expressions = Vec::new();
    let mut uses = Vec::new();
    assert_eq!(
        shadow_tree(
            skeleton,
            skeleton.body(),
            &binders,
            &mut expressions,
            &mut uses
        ),
        old
    );
    assert_eq!(expressions.len(), 7);
    assert_eq!(skeleton.expressions().len(), 7);
    assert_eq!(uses.len(), 3);
    assert_eq!(skeleton.uses().len(), 3);
    // Inner f is structurally free relative to x. The dump has no explicit
    // capture list; no typed capture or runtime evidence is inferred here.
    assert_eq!(
        skeleton
            .pending()
            .iter()
            .map(|p| p.premise())
            .collect::<Vec<_>>(),
        vec![
            Premise::CallableRole,
            Premise::FullFunctionMembership,
            Premise::CallViewRealization,
            Premise::QIndependentSourceCallViewFormation,
            Premise::SourceEventContributionAndTypedOutputObservation,
            Premise::JointArgumentTypingAndActualReturnedProviderCarrierCompatibility,
            Premise::SourceFormalUseRuleApplicabilityAndInterpretation,
            Premise::SourceDirectionalOutputEffectProtectionIntroduction
        ]
    );
    // Provider/receiver, receipts, O/A, Q registration and nu/K/D remain open.
}
