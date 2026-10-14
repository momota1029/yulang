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
