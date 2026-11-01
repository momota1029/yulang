//! Private scoped-effect transformer candidate; no source semantics are adopted here.
//!
//! A transformer changes only route tags and protection scopes. Effect members
//! and capture grants are deliberately outside its state.

use crate::{SolveAvailabilityError, checked_fixed_capacity_bytes};

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct EffectScopeId(pub(crate) u32);

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub(crate) struct InputRouteId(pub(crate) u32);

/// `Missing(tags)` denotes the disjunction of missing initial route tags.
/// The empty disjunction is false.
#[derive(Debug, Eq, Hash, PartialEq)]
enum AddCondition {
    Missing(Vec<InputRouteId>),
}

#[derive(Debug, Eq, Hash, PartialEq)]
struct ScopeEntry {
    scope: EffectScopeId,
    keep_initial: bool,
    add: AddCondition,
}

/// Canonical finite transformer. Identity entries are omitted; releases retain
/// their `keep_initial = false` tombstone even without an added protection.
#[derive(Debug, Default, Eq, Hash, PartialEq)]
pub(crate) struct ScopeTransformer {
    stamped: Vec<InputRouteId>,
    scopes: Vec<ScopeEntry>,
}

#[derive(Debug, Eq, PartialEq)]
pub(crate) struct ScopeState {
    pub(crate) inputs: Vec<InputRouteId>,
    pub(crate) protections: Vec<EffectScopeId>,
}

fn reserve<T>(values: &mut Vec<T>, additional: usize) -> Result<(), SolveAvailabilityError> {
    values.try_reserve(additional).map_err(|_| SolveAvailabilityError::IdentityExhausted)
}

fn singleton<T>(value: T) -> Result<Vec<T>, SolveAvailabilityError> {
    let mut result = Vec::new();
    reserve(&mut result, 1)?;
    result.push(value);
    Ok(result)
}

fn sorted_copy<T: Copy + Ord>(values: &[T]) -> Result<Vec<T>, SolveAvailabilityError> {
    let mut result = Vec::new();
    reserve(&mut result, values.len())?;
    result.extend_from_slice(values);
    result.sort_unstable();
    result.dedup();
    Ok(result)
}

/// Merge canonical sets with a fallible upper-bound allocation.
fn union<T: Copy + Ord>(left: &[T], right: &[T]) -> Result<Vec<T>, SolveAvailabilityError> {
    let capacity = left.len().checked_add(right.len())
        .ok_or(SolveAvailabilityError::IdentityExhausted)?;
    let mut result = Vec::new();
    reserve(&mut result, capacity)?;
    let (mut i, mut j) = (0, 0);
    while i < left.len() || j < right.len() {
        if j == right.len() || (i < left.len() && left[i] < right[j]) {
            result.push(left[i]);
            i += 1;
        } else if i == left.len() || right[j] < left[i] {
            result.push(right[j]);
            j += 1;
        } else {
            result.push(left[i]);
            i += 1;
            j += 1;
        }
    }
    Ok(result)
}

impl AddCondition {
    fn is_false(&self) -> bool {
        matches!(self, Self::Missing(tags) if tags.is_empty())
    }

    fn holds(&self, initial: &[InputRouteId]) -> bool {
        match self {
            Self::Missing(tags) => tags.iter().any(|tag| initial.binary_search(tag).is_err()),
        }
    }
}

impl ScopeTransformer {
    pub(crate) fn identity() -> Self {
        Self::default()
    }

    pub(crate) fn stamp_input(input: InputRouteId) -> Result<Self, SolveAvailabilityError> {
        Ok(Self { stamped: singleton(input)?, scopes: Vec::new() })
    }

    pub(crate) fn protect_body(
        scope: EffectScopeId,
        input: InputRouteId,
    ) -> Result<Self, SolveAvailabilityError> {
        Ok(Self {
            stamped: Vec::new(),
            scopes: singleton(ScopeEntry {
                scope,
                keep_initial: true,
                add: AddCondition::Missing(singleton(input)?),
            })?,
        })
    }

    pub(crate) fn release(scope: EffectScopeId) -> Result<Self, SolveAvailabilityError> {
        Ok(Self {
            stamped: Vec::new(),
            scopes: singleton(ScopeEntry {
                scope,
                keep_initial: false,
                add: AddCondition::Missing(Vec::new()),
            })?,
        })
    }

    /// Execute `self` first, then `second`. Predicates always refer to the
    /// initial state: stamps from `self` make corresponding second predicates
    /// false, while a second release erases the first addition.
    pub(crate) fn then(&self, second: &Self) -> Result<Self, SolveAvailabilityError> {
        let stamped = union(&self.stamped, &second.stamped)?;
        let capacity = self.scopes.len().checked_add(second.scopes.len())
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let mut scopes = Vec::new();
        reserve(&mut scopes, capacity)?;
        let (mut i, mut j) = (0, 0);
        while i < self.scopes.len() || j < second.scopes.len() {
            let left = self.scopes.get(i);
            let right = second.scopes.get(j);
            let scope = match (left, right) {
                (Some(a), Some(b)) => a.scope.min(b.scope),
                (Some(a), None) => a.scope,
                (None, Some(b)) => b.scope,
                (None, None) => break,
            };
            let first_entry = left.filter(|entry| entry.scope == scope);
            let second_entry = right.filter(|entry| entry.scope == scope);
            let keep_second = second_entry.is_none_or(|entry| entry.keep_initial);
            let keep_initial = keep_second && first_entry.is_none_or(|entry| entry.keep_initial);
            let first_add = first_entry.filter(|_| keep_second).map(|entry| &entry.add);
            let second_add = second_entry.map(|entry| &entry.add);
            let first_tags = match first_add {
                Some(AddCondition::Missing(tags)) => tags.as_slice(),
                None => &[],
            };
            let second_tags = match second_add {
                Some(AddCondition::Missing(tags)) => tags.as_slice(),
                None => &[],
            };
            let mut retained = Vec::new();
            reserve(&mut retained, second_tags.len())?;
            retained.extend(second_tags.iter().copied()
                .filter(|tag| self.stamped.binary_search(tag).is_err()));
            let add = AddCondition::Missing(union(first_tags, &retained)?);
            if !keep_initial || !add.is_false() {
                scopes.push(ScopeEntry { scope, keep_initial, add });
            }
            i += usize::from(first_entry.is_some());
            j += usize::from(second_entry.is_some());
        }
        Ok(Self { stamped, scopes })
    }

    /// Input slices may be unsorted and contain duplicates. The result is a
    /// canonical set state, built privately before it is returned.
    pub(crate) fn evaluate(
        &self,
        initial_inputs: &[InputRouteId],
        initial_protections: &[EffectScopeId],
    ) -> Result<ScopeState, SolveAvailabilityError> {
        let initial_inputs = sorted_copy(initial_inputs)?;
        let initial_protections = sorted_copy(initial_protections)?;
        let inputs = union(&initial_inputs, &self.stamped)?;
        let capacity = initial_protections.len().checked_add(self.scopes.len())
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let mut protections = Vec::new();
        reserve(&mut protections, capacity)?;
        let (mut i, mut j) = (0, 0);
        while i < initial_protections.len() || j < self.scopes.len() {
            if j == self.scopes.len()
                || (i < initial_protections.len() && initial_protections[i] < self.scopes[j].scope)
            {
                protections.push(initial_protections[i]);
                i += 1;
            } else {
                let entry = &self.scopes[j];
                let inherited = initial_protections.get(i) == Some(&entry.scope);
                if (entry.keep_initial && inherited) || entry.add.holds(&initial_inputs) {
                    protections.push(entry.scope);
                }
                i += usize::from(inherited);
                j += 1;
            }
        }
        Ok(ScopeState { inputs, protections })
    }

    /// Rename the finite support. Each closure is called once per distinct ID.
    /// Both maps must be injective on that support; collisions are rejected.
    pub(crate) fn remap(
        &self,
        mut scope_map: impl FnMut(EffectScopeId) -> EffectScopeId,
        mut input_map: impl FnMut(InputRouteId) -> InputRouteId,
    ) -> Result<Self, SolveAvailabilityError> {
        let mut input_ids = Vec::new();
        reserve(&mut input_ids, self.stamped.len())?;
        input_ids.extend_from_slice(&self.stamped);
        for entry in &self.scopes {
            let AddCondition::Missing(tags) = &entry.add;
            reserve(&mut input_ids, tags.len())?;
            input_ids.extend_from_slice(tags);
        }
        input_ids.sort_unstable();
        input_ids.dedup();
        let mut mapped_inputs = Vec::new();
        reserve(&mut mapped_inputs, input_ids.len())?;
        mapped_inputs.extend(input_ids.iter().copied().map(&mut input_map));
        let unique_inputs = sorted_copy(&mapped_inputs)?;
        if unique_inputs.len() != mapped_inputs.len() {
            return Err(SolveAvailabilityError::ReceiptMismatch);
        }
        let lookup = |id: &InputRouteId| {
            mapped_inputs[input_ids.binary_search(id).expect("input support includes every predicate")]
        };
        let mut stamped = Vec::new();
        reserve(&mut stamped, self.stamped.len())?;
        stamped.extend(self.stamped.iter().map(lookup));
        stamped.sort_unstable();
        let mut scopes = Vec::new();
        reserve(&mut scopes, self.scopes.len())?;
        for entry in &self.scopes {
            let add = match &entry.add {
                AddCondition::Missing(tags) => {
                    let mut renamed = Vec::new();
                    reserve(&mut renamed, tags.len())?;
                    renamed.extend(tags.iter().map(lookup));
                    renamed.sort_unstable();
                    AddCondition::Missing(renamed)
                }
            };
            scopes.push(ScopeEntry {
                scope: scope_map(entry.scope),
                keep_initial: entry.keep_initial,
                add,
            });
        }
        scopes.sort_unstable_by_key(|entry| entry.scope);
        if scopes.windows(2).any(|pair| pair[0].scope == pair[1].scope) {
            return Err(SolveAvailabilityError::ReceiptMismatch);
        }
        Ok(Self { stamped, scopes })
    }

    /// Retained heap capacity only, matching the solver's capacity accounting.
    pub(crate) fn checked_retained_bytes(&self) -> Result<usize, SolveAvailabilityError> {
        checked_fixed_capacity_bytes(
            [
                (self.stamped.capacity(), std::mem::size_of::<InputRouteId>()),
                (self.scopes.capacity(), std::mem::size_of::<ScopeEntry>()),
            ].into_iter().chain(self.scopes.iter().map(|entry| match &entry.add {
                AddCondition::Missing(tags) => (tags.capacity(), std::mem::size_of::<InputRouteId>()),
            })),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::{EffectScopeId, InputRouteId, ScopeState, ScopeTransformer};
    use crate::SolveAvailabilityError;
    use std::collections::{BTreeMap, BTreeSet};

    #[derive(Clone, Copy, Debug)]
    enum Primitive {
        Stamp(InputRouteId),
        Protect(EffectScopeId, InputRouteId),
        Release(EffectScopeId),
    }

    #[derive(Clone, Debug, Eq, PartialEq)]
    struct OracleState {
        inputs: BTreeSet<InputRouteId>,
        protections: BTreeSet<EffectScopeId>,
    }

    impl OracleState {
        fn new(inputs: &[InputRouteId], protections: &[EffectScopeId]) -> Self {
            Self {
                inputs: inputs.iter().copied().collect(),
                protections: protections.iter().copied().collect(),
            }
        }

        fn apply(&mut self, operation: Primitive) {
            match operation {
                Primitive::Stamp(input) => { self.inputs.insert(input); }
                Primitive::Protect(scope, input) => {
                    if !self.inputs.contains(&input) { self.protections.insert(scope); }
                }
                Primitive::Release(scope) => { self.protections.remove(&scope); }
            }
        }

        fn as_scope_state(&self) -> ScopeState {
            ScopeState {
                inputs: self.inputs.iter().copied().collect(),
                protections: self.protections.iter().copied().collect(),
            }
        }
    }

    fn transformer(operation: Primitive) -> ScopeTransformer {
        match operation {
            Primitive::Stamp(input) => ScopeTransformer::stamp_input(input).unwrap(),
            Primitive::Protect(scope, input) => ScopeTransformer::protect_body(scope, input).unwrap(),
            Primitive::Release(scope) => ScopeTransformer::release(scope).unwrap(),
        }
    }

    fn oracle(initial_inputs: &[InputRouteId], initial_protections: &[EffectScopeId], operations: &[Primitive]) -> OracleState {
        let mut state = OracleState::new(initial_inputs, initial_protections);
        for operation in operations.iter().copied() { state.apply(operation); }
        state
    }

    fn compose(operations: &[Primitive]) -> ScopeTransformer {
        operations.iter().copied().try_fold(ScopeTransformer::identity(), |acc, operation| {
            acc.then(&transformer(operation))
        }).unwrap()
    }

    fn short_sequences(alphabet: &[Primitive], max_len: usize) -> Vec<Vec<Primitive>> {
        let mut sequences = vec![Vec::new()];
        let mut frontier = vec![Vec::new()];
        for _ in 0..max_len {
            let mut next = Vec::new();
            for prefix in &frontier {
                for operation in alphabet {
                    let mut sequence = prefix.clone();
                    sequence.push(*operation);
                    next.push(sequence);
                }
            }
            sequences.extend(next.iter().cloned());
            frontier = next;
        }
        sequences
    }

    fn subsets<T: Copy>(values: &[T]) -> Vec<Vec<T>> {
        (0..(1usize << values.len())).map(|mask| {
            values.iter().enumerate().filter_map(|(bit, value)| {
                ((mask & (1 << bit)) != 0).then_some(*value)
            }).collect()
        }).collect()
    }

    fn assert_state_eq(actual: ScopeState, expected: ScopeState) {
        assert_eq!(actual.inputs, expected.inputs);
        assert_eq!(actual.protections, expected.protections);
    }

    #[test]
    fn finite_short_compositions_match_sequential_primitive_oracle() {
        let a = InputRouteId(0);
        let b = InputRouteId(1);
        let x = EffectScopeId(0);
        let y = EffectScopeId(1);
        let alphabet = [
            Primitive::Stamp(a), Primitive::Stamp(b),
            Primitive::Protect(x, a), Primitive::Protect(x, b),
            Primitive::Protect(y, a), Primitive::Protect(y, b),
            Primitive::Release(x), Primitive::Release(y),
        ];
        let inputs = subsets(&[a, b]);
        let protections = subsets(&[x, y]);
        for operations in short_sequences(&alphabet, 3) {
            let composed = compose(&operations);
            for initial_inputs in &inputs {
                for initial_protections in &protections {
                    let expected = oracle(initial_inputs, initial_protections, &operations).as_scope_state();
                    let actual = composed.evaluate(initial_inputs, initial_protections).unwrap();
                    assert_state_eq(actual, expected);

                    for split in 0..=operations.len() {
                        let first = compose(&operations[..split]);
                        let second = compose(&operations[split..]);
                        let joined = first.then(&second).unwrap();
                        let after_first = first.evaluate(initial_inputs, initial_protections).unwrap();
                        let sequential = second.evaluate(&after_first.inputs, &after_first.protections).unwrap();
                        let joined_state = joined.evaluate(initial_inputs, initial_protections).unwrap();
                        assert_state_eq(joined_state, sequential);
                    }
                }
            }
        }
    }

    #[test]
    fn operation_order_and_release_tombstones_remain_observable() {
        let input = InputRouteId(3);
        let scope = EffectScopeId(7);
        let orders = [
            [Primitive::Stamp(input), Primitive::Protect(scope, input)],
            [Primitive::Protect(scope, input), Primitive::Stamp(input)],
            [Primitive::Protect(scope, input), Primitive::Release(scope)],
            [Primitive::Release(scope), Primitive::Protect(scope, input)],
        ];
        let outcomes: Vec<_> = orders.iter().map(|operations| {
            compose(operations).evaluate(&[], &[]).unwrap()
        }).collect();
        assert_ne!(outcomes[0], outcomes[1]);
        assert_ne!(outcomes[2], outcomes[3]);
        assert!(outcomes[0].protections.is_empty());
        assert_eq!(outcomes[1].protections, vec![scope]);
        assert!(outcomes[2].protections.is_empty());
        assert_eq!(outcomes[3].protections, vec![scope]);

        let released = ScopeTransformer::release(scope).unwrap();
        assert!(released.evaluate(&[], &[]).unwrap().protections.is_empty());
        assert!(released.evaluate(&[], &[scope]).unwrap().protections.is_empty());
        let retained_unrelated = released.evaluate(&[], &[EffectScopeId(8)]).unwrap();
        assert_eq!(retained_unrelated.protections, vec![EffectScopeId(8)]);
    }

    #[test]
    fn inputs_and_protections_are_set_like_and_keep_unrelated_protections() {
        let a = InputRouteId(1);
        let b = InputRouteId(2);
        let x = EffectScopeId(4);
        let y = EffectScopeId(5);
        let transformer = ScopeTransformer::protect_body(x, b).unwrap();
        let actual = transformer.evaluate(&[b, a, b], &[y, x, y]).unwrap();
        assert_eq!(actual.inputs, vec![a, b]);
        assert_eq!(actual.protections, vec![x, y]);

        let no_add = ScopeTransformer::protect_body(x, a).unwrap();
        let actual = no_add.evaluate(&[b, a, b], &[y, x, y]).unwrap();
        assert_eq!(actual.inputs, vec![a, b]);
        assert_eq!(actual.protections, vec![x, y]);
    }

    #[test]
    fn injective_remap_commutes_with_evaluation_on_finite_support() {
        let a = InputRouteId(1);
        let b = InputRouteId(2);
        let x = EffectScopeId(4);
        let y = EffectScopeId(5);
        let operations = [
            Primitive::Protect(x, a), Primitive::Stamp(b),
            Primitive::Release(y), Primitive::Protect(y, b),
        ];
        let original = compose(&operations);
        let remapped = original.remap(
            |scope| EffectScopeId(scope.0 + 20),
            |input| InputRouteId(input.0 + 30),
        ).unwrap();
        for initial_inputs in [&[][..], &[a][..]] {
            let before = original.evaluate(initial_inputs, &[]).unwrap();
            let mapped_inputs = initial_inputs.iter().map(|id| InputRouteId(id.0 + 30)).collect::<Vec<_>>();
            let after = remapped.evaluate(&mapped_inputs, &[]).unwrap();
            assert_eq!(
                after.inputs,
                before.inputs.iter().map(|id| InputRouteId(id.0 + 30)).collect::<Vec<_>>(),
            );
            assert_eq!(
                after.protections,
                before.protections.iter().map(|id| EffectScopeId(id.0 + 20)).collect::<Vec<_>>(),
            );
        }
    }

    #[test]
    fn remap_rejects_scope_and_input_collisions_separately() {
        let x = EffectScopeId(1);
        let y = EffectScopeId(2);
        let a = InputRouteId(3);
        let b = InputRouteId(4);
        let two_scopes = ScopeTransformer::release(x).unwrap()
            .then(&ScopeTransformer::release(y).unwrap()).unwrap();
        assert_eq!(
            two_scopes.remap(|_| EffectScopeId(9), |input| input).unwrap_err(),
            SolveAvailabilityError::ReceiptMismatch,
        );
        let two_inputs = ScopeTransformer::stamp_input(a).unwrap()
            .then(&ScopeTransformer::stamp_input(b).unwrap()).unwrap();
        assert_eq!(
            two_inputs.remap(|scope| scope, |_| InputRouteId(9)).unwrap_err(),
            SolveAvailabilityError::ReceiptMismatch,
        );
    }

    #[test]
    fn remap_calls_each_map_once_per_distinct_support_id() {
        let x = EffectScopeId(1);
        let y = EffectScopeId(2);
        let a = InputRouteId(3);
        let b = InputRouteId(4);
        let transformer = ScopeTransformer::protect_body(x, a).unwrap()
            .then(&ScopeTransformer::stamp_input(a).unwrap()).unwrap()
            .then(&ScopeTransformer::protect_body(y, b).unwrap()).unwrap();
        let mut scope_calls = BTreeMap::new();
        let mut input_calls = BTreeMap::new();
        transformer.remap(
            |scope| { *scope_calls.entry(scope).or_insert(0usize) += 1; EffectScopeId(scope.0 + 10) },
            |input| { *input_calls.entry(input).or_insert(0usize) += 1; InputRouteId(input.0 + 10) },
        ).unwrap();
        assert_eq!(scope_calls, BTreeMap::from([(x, 1), (y, 1)]));
        assert_eq!(input_calls, BTreeMap::from([(a, 1), (b, 1)]));
    }
}
