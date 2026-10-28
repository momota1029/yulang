//! Exhaustive alpha-isomorphism of caller-supplied finite incidence records.
//!
//! This shadow-only utility implements CI_ALPHA's structural slice. It neither
//! constructs a complete interface nor certifies semantic equality, Generalize,
//! primitive covariance, source generation, or production inference. Callers
//! must retain every observable scope, binder mode/order, origin, direction,
//! provider policy, primitive identity and external input in the supplied records.
//! Only `Local` names are renamed; rigid values and immutable sort labels are not.

/// Research envelope, unrelated to the production supported-input boundary.
pub const MAX_LOCAL_NODES: usize = 8;

/// Explicitly separates immutable observations from alpha-local references.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Field<R> {
    Rigid(R),
    Local(usize),
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Node<S, R> {
    pub sort: S,
    /// Operand order is observable. Binder trees/scopes can be represented here.
    pub fields: Vec<Field<R>>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Presentation<S, R> {
    /// The complete caller-supplied rigid/external context, in observable order.
    pub context: Vec<R>,
    pub exports: Vec<Field<R>>,
    /// Vector positions are local names, not source/provider identities.
    pub nodes: Vec<Node<S, R>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReferenceSite {
    Export { field: usize },
    Node { node: usize, field: usize },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InvalidReference {
    pub site: ReferenceSite,
    pub target: usize,
    pub node_count: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Exhaustion {
    NodeLimit { node_count: usize, limit: usize },
    CandidateBudget { examined: usize, budget: usize },
}

/// Unforgeable completed canonical form; no partial minimum is published.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CanonicalForm<S, R>(Presentation<S, R>);

impl<S, R> CanonicalForm<S, R> {
    pub fn presentation(&self) -> &Presentation<S, R> {
        &self.0
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Completed<S, R> {
    pub canonical: CanonicalForm<S, R>,
    /// Original local name -> canonical local name.
    pub renaming: Vec<usize>,
    pub examined_candidates: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Canonicalization<S, R> {
    Completed(Completed<S, R>),
    Exhausted(Exhaustion),
}

fn validate<S, R>(p: &Presentation<S, R>) -> Result<(), InvalidReference> {
    let check = |field: &Field<R>, site| {
        if let Field::Local(target) = field {
            if *target >= p.nodes.len() {
                return Err(InvalidReference {
                    site,
                    target: *target,
                    node_count: p.nodes.len(),
                });
            }
        }
        Ok(())
    };
    for (field, value) in p.exports.iter().enumerate() {
        check(value, ReferenceSite::Export { field })?;
    }
    for (node, value) in p.nodes.iter().enumerate() {
        for (field, value) in value.fields.iter().enumerate() {
            check(value, ReferenceSite::Node { node, field })?;
        }
    }
    Ok(())
}

fn renamed<S: Clone, R: Clone>(p: &Presentation<S, R>, map: &[usize]) -> Presentation<S, R> {
    let field = |f: &Field<R>| match f {
        Field::Rigid(r) => Field::Rigid(r.clone()),
        Field::Local(id) => Field::Local(map[*id]),
    };
    let mut nodes = p.nodes.clone();
    for (old, node) in p.nodes.iter().enumerate() {
        nodes[map[old]] = Node {
            sort: node.sort.clone(),
            fields: node.fields.iter().map(&field).collect(),
        };
    }
    Presentation {
        context: p.context.clone(),
        exports: p.exports.iter().map(field).collect(),
        nodes,
    }
}

/// Exhausts all bijections to canonical slots whose sort labels are sorted.
/// Rust structural `Ord` compares complete records, with no string encoding.
/// Invalid references are errors even when the resource envelope is exceeded.
pub fn canonicalize<S: Ord + Clone, R: Ord + Clone>(
    p: &Presentation<S, R>,
    candidate_budget: usize,
) -> Result<Canonicalization<S, R>, InvalidReference> {
    validate(p)?;
    let n = p.nodes.len();
    if n > MAX_LOCAL_NODES {
        return Ok(Canonicalization::Exhausted(Exhaustion::NodeLimit {
            node_count: n,
            limit: MAX_LOCAL_NODES,
        }));
    }
    let mut sorts: Vec<_> = p.nodes.iter().map(|node| node.sort.clone()).collect();
    sorts.sort();
    let mut map = vec![0; n];
    let mut used = vec![false; n];
    let mut best: Option<(Presentation<S, R>, Vec<usize>)> = None;
    let mut examined = 0;
    // Returns false only when a further candidate exists beyond the budget.
    fn visit<S: Ord + Clone, R: Ord + Clone>(
        p: &Presentation<S, R>,
        sorts: &[S],
        depth: usize,
        map: &mut [usize],
        used: &mut [bool],
        budget: usize,
        examined: &mut usize,
        best: &mut Option<(Presentation<S, R>, Vec<usize>)>,
    ) -> bool {
        if depth == map.len() {
            if *examined == budget {
                return false;
            }
            *examined += 1;
            let candidate = renamed(p, map);
            if best
                .as_ref()
                .is_none_or(|(current, _)| candidate < *current)
            {
                *best = Some((candidate, map.to_vec()));
            }
            return true;
        }
        for slot in 0..map.len() {
            if !used[slot] && p.nodes[depth].sort == sorts[slot] {
                map[depth] = slot;
                used[slot] = true;
                if !visit(p, sorts, depth + 1, map, used, budget, examined, best) {
                    return false;
                }
                used[slot] = false;
            }
        }
        true
    }
    if !visit(
        p,
        &sorts,
        0,
        &mut map,
        &mut used,
        candidate_budget,
        &mut examined,
        &mut best,
    ) {
        return Ok(Canonicalization::Exhausted(Exhaustion::CandidateBudget {
            examined,
            budget: candidate_budget,
        }));
    }
    // Every finite sort multiset has a bijection to its sorted slots, including empty.
    let (canonical, renaming) =
        best.expect("exhaustive sort-preserving enumeration has a candidate");
    Ok(Canonicalization::Completed(Completed {
        canonical: CanonicalForm(canonical),
        renaming,
        examined_candidates: examined,
    }))
}

/// Both directions are explicit so a consumer can inspect and verify inverses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AlphaCertificate {
    pub left_to_right: Vec<usize>,
    pub right_to_left: Vec<usize>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Side {
    Left,
    Right,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Comparison {
    StructurallyAlphaEqual(AlphaCertificate),
    StructurallyDifferent,
    Exhausted { side: Side, reason: Exhaustion },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InvalidInput {
    pub side: Side,
    pub reference: InvalidReference,
}

/// Each side receives the stated budget independently. A difference is returned
/// only after both enumerations finish; exhaustion carries no partial certificate.
pub fn compare<S: Ord + Clone, R: Ord + Clone>(
    left: &Presentation<S, R>,
    right: &Presentation<S, R>,
    candidate_budget: usize,
) -> Result<Comparison, InvalidInput> {
    // Validate both inputs before any resource-status return.
    validate(left).map_err(|reference| InvalidInput {
        side: Side::Left,
        reference,
    })?;
    validate(right).map_err(|reference| InvalidInput {
        side: Side::Right,
        reference,
    })?;
    let left = match canonicalize(left, candidate_budget).expect("already validated") {
        Canonicalization::Completed(value) => value,
        Canonicalization::Exhausted(reason) => {
            return Ok(Comparison::Exhausted {
                side: Side::Left,
                reason,
            });
        }
    };
    let right = match canonicalize(right, candidate_budget).expect("already validated") {
        Canonicalization::Completed(value) => value,
        Canonicalization::Exhausted(reason) => {
            return Ok(Comparison::Exhausted {
                side: Side::Right,
                reason,
            });
        }
    };
    if left.canonical != right.canonical {
        return Ok(Comparison::StructurallyDifferent);
    }
    let n = left.renaming.len();
    let mut canonical_to_right = vec![0; n];
    for (old, canonical) in right.renaming.iter().enumerate() {
        canonical_to_right[*canonical] = old;
    }
    let left_to_right: Vec<_> = left
        .renaming
        .iter()
        .map(|canonical| canonical_to_right[*canonical])
        .collect();
    let mut right_to_left = vec![0; n];
    for (old, target) in left_to_right.iter().enumerate() {
        right_to_left[*target] = old;
    }
    Ok(Comparison::StructurallyAlphaEqual(AlphaCertificate {
        left_to_right,
        right_to_left,
    }))
}

/// Checks the complete ordered graph and inverse bijection, independently of
/// canonical search. A false result says only that this supplied certificate fails.
pub fn verify_certificate<S: Ord + Clone, R: Ord + Clone>(
    left: &Presentation<S, R>,
    right: &Presentation<S, R>,
    certificate: &AlphaCertificate,
) -> Result<bool, InvalidInput> {
    validate(left).map_err(|reference| InvalidInput {
        side: Side::Left,
        reference,
    })?;
    validate(right).map_err(|reference| InvalidInput {
        side: Side::Right,
        reference,
    })?;
    let n = left.nodes.len();
    if right.nodes.len() != n
        || certificate.left_to_right.len() != n
        || certificate.right_to_left.len() != n
    {
        return Ok(false);
    }
    for (old, target) in certificate.left_to_right.iter().enumerate() {
        if *target >= n || certificate.right_to_left[*target] != old {
            return Ok(false);
        }
    }
    Ok(renamed(left, &certificate.left_to_right) == *right)
}
