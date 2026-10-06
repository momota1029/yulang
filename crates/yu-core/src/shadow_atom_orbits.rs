//! Bounded, pointwise equality-only atom projection; no source semantic authority.
//!
//! Atoms range over an infinite uninterpreted set. Public labels are opaque:
//! only their equality matters. Quantifiers retain their original positions,
//! and every occurrence of a binder uses its one current value. This module
//! admits no world predicates, callbacks, recursive operators, or type rules.

/// Maximum formula nodes inspected during prevalidation.
pub const MAX_NODES: usize = 128;
/// Maximum formula depth, counting the root as one.
pub const MAX_DEPTH: usize = 32;
/// Maximum total binders, including binders in separate branches.
pub const MAX_BINDERS: usize = 16;
/// Maximum public ports (including duplicate labels).
pub const MAX_PUBLIC: usize = 16;

/// A public port index or a lexically enclosing binder's globally unique ID.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AtomRef {
    Public(usize),
    Variable(u64),
}

/// The entire admitted observer language. No quantifier reordering is done.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Formula {
    Bool(bool),
    Eq(AtomRef, AtomRef),
    Ne(AtomRef, AtomRef),
    Not(Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Exists { binder: u64, body: Box<Formula> },
    ForAll { binder: u64, body: Box<Formula> },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Resource {
    Nodes,
    Depth,
    Binders,
    PublicPorts,
    EvaluationSteps,
}

/// Exhaustion never represents a logical false result.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    InvalidPublicReference(usize),
    OutOfScopeVariable(u64),
    RepeatedBinder(u64),
    Exhausted(Resource),
}

/// Evaluate one supplied public equality valuation exactly when successful.
///
/// Each visited evaluation node consumes one step, including every quantified
/// branch's body visit. Prevalidation is separately bounded by the constants
/// above and examines even subtrees that Boolean evaluation could skip. If a
/// resource bound is reached, no truth value is returned. Invalid inputs over
/// a structural bound may report exhaustion before a later invalid reference.
/// Caller-owned formula construction and destruction are outside this bound.
pub fn evaluate(formula: &Formula, public_labels: &[u64], step_budget: u64) -> Result<bool, Error> {
    if public_labels.len() > MAX_PUBLIC {
        return Err(Error::Exhausted(Resource::PublicPorts));
    }
    validate(
        formula,
        public_labels.len(),
        1,
        &mut 0,
        &mut Vec::new(),
        &mut Vec::new(),
    )?;
    let mut distinct = Vec::new();
    let public: Vec<usize> = public_labels
        .iter()
        .map(|label| {
            if let Some(index) = distinct.iter().position(|old| old == label) {
                index
            } else {
                distinct.push(*label);
                distinct.len() - 1
            }
        })
        .collect();
    let mut remaining = step_budget;
    eval(
        formula,
        &public,
        &mut Vec::new(),
        distinct.len(),
        &mut remaining,
    )
}

fn validate(
    formula: &Formula,
    public_count: usize,
    depth: usize,
    nodes: &mut usize,
    scope: &mut Vec<u64>,
    seen: &mut Vec<u64>,
) -> Result<(), Error> {
    if depth > MAX_DEPTH {
        return Err(Error::Exhausted(Resource::Depth));
    }
    if *nodes == MAX_NODES {
        return Err(Error::Exhausted(Resource::Nodes));
    }
    *nodes += 1;
    let check = |atom: AtomRef| match atom {
        AtomRef::Public(index) if index >= public_count => {
            Err(Error::InvalidPublicReference(index))
        }
        AtomRef::Variable(id) if !scope.contains(&id) => Err(Error::OutOfScopeVariable(id)),
        _ => Ok(()),
    };
    match formula {
        Formula::Bool(_) => Ok(()),
        Formula::Eq(a, b) | Formula::Ne(a, b) => {
            check(*a)?;
            check(*b)
        }
        Formula::Not(body) => validate(body, public_count, depth + 1, nodes, scope, seen),
        Formula::And(a, b) | Formula::Or(a, b) => {
            validate(a, public_count, depth + 1, nodes, scope, seen)?;
            validate(b, public_count, depth + 1, nodes, scope, seen)
        }
        Formula::Exists { binder, body } | Formula::ForAll { binder, body } => {
            if seen.contains(binder) {
                return Err(Error::RepeatedBinder(*binder));
            }
            if seen.len() == MAX_BINDERS {
                return Err(Error::Exhausted(Resource::Binders));
            }
            seen.push(*binder);
            scope.push(*binder);
            let result = validate(body, public_count, depth + 1, nodes, scope, seen);
            scope.pop();
            result
        }
    }
}

fn value(atom: AtomRef, public: &[usize], bound: &[(u64, usize)]) -> usize {
    match atom {
        AtomRef::Public(index) => public[index],
        AtomRef::Variable(id) => {
            bound
                .iter()
                .find(|(binder, _)| *binder == id)
                .expect("prevalidated lexical reference")
                .1
        }
    }
}

fn eval(
    formula: &Formula,
    public: &[usize],
    bound: &mut Vec<(u64, usize)>,
    classes: usize,
    remaining: &mut u64,
) -> Result<bool, Error> {
    if *remaining == 0 {
        return Err(Error::Exhausted(Resource::EvaluationSteps));
    }
    *remaining -= 1;
    match formula {
        Formula::Bool(result) => Ok(*result),
        Formula::Eq(a, b) => Ok(value(*a, public, bound) == value(*b, public, bound)),
        Formula::Ne(a, b) => Ok(value(*a, public, bound) != value(*b, public, bound)),
        Formula::Not(body) => Ok(!eval(body, public, bound, classes, remaining)?),
        Formula::And(a, b) => Ok(eval(a, public, bound, classes, remaining)?
            && eval(b, public, bound, classes, remaining)?),
        Formula::Or(a, b) => Ok(eval(a, public, bound, classes, remaining)?
            || eval(b, public, bound, classes, remaining)?),
        Formula::Exists { binder, body } | Formula::ForAll { binder, body } => {
            let existential = matches!(formula, Formula::Exists { .. });
            // All current singleton classes, then one representative outside
            // their finite support. No actual finite atom universe is imposed.
            for candidate in 0..=classes {
                bound.push((*binder, candidate));
                let result = eval(
                    body,
                    public,
                    bound,
                    classes + usize::from(candidate == classes),
                    remaining,
                );
                bound.pop();
                if result? == existential {
                    return Ok(existential);
                }
            }
            Ok(!existential)
        }
    }
}
