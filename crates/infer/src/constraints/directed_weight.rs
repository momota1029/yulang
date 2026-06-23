#![allow(dead_code)]

use poly::types::{StackWeight, SubtractId, Subtractability};

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub(crate) struct DirectedWeights {
    pub(crate) left: LeftStackWeight,
    pub(crate) right: RightStackWeight,
}

impl DirectedWeights {
    pub(crate) fn empty() -> Self {
        Self::default()
    }

    pub(crate) fn mix(&self) -> Self {
        if self.left.is_empty() || self.right.is_empty() {
            return self.clone();
        }

        let mut left = self.left.clone();
        let mut right = RightStackWeight::empty();
        for entry in self.right.entries() {
            let before = left.entry(entry.id).cloned();
            left = left.compose(&LeftStackWeight::pops(entry.id, entry.pops));
            let after = left.entry(entry.id);
            if before.is_some() && after.is_none() {
                continue;
            }
            if let Some(after) = after
                && after.pushes > 0
            {
                continue;
            }
            let after_pops = after.map(|entry| entry.leading_pops).unwrap_or(0);
            if after_pops > 0 {
                right = right.compose(&RightStackWeight::pops(entry.id, after_pops));
                left.remove(entry.id);
            }
        }

        Self { left, right }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub(crate) struct LeftStackWeight {
    entries: Vec<LeftStackWeightEntry>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct LeftStackWeightEntry {
    pub(crate) id: SubtractId,
    pub(crate) leading_pops: u32,
    pub(crate) family: Option<Subtractability>,
    pub(crate) pushes: u32,
}

impl LeftStackWeight {
    pub(crate) fn empty() -> Self {
        Self::default()
    }

    pub(crate) fn pop(id: SubtractId) -> Self {
        Self::pops(id, 1)
    }

    pub(crate) fn pops(id: SubtractId, count: u32) -> Self {
        let mut out = Self::empty();
        if count > 0 {
            out.entries.push(LeftStackWeightEntry {
                id,
                leading_pops: count,
                family: None,
                pushes: 0,
            });
        }
        out
    }

    pub(crate) fn take(id: SubtractId, family: Subtractability) -> Self {
        let mut out = Self::empty();
        out.entries.push(LeftStackWeightEntry {
            id,
            leading_pops: 0,
            family: Some(family),
            pushes: 1,
        });
        out
    }

    pub(crate) fn from_stack_weight(weight: &StackWeight) -> Self {
        let mut out = Self::empty();
        for entry in weight.entries() {
            out = out.compose(&Self::pops(entry.id, entry.pops));
            for family in &entry.stack {
                out = out.compose(&Self::take(entry.id, family.clone()));
            }
        }
        out
    }

    pub(crate) fn from_right_weight(weight: &RightStackWeight) -> Self {
        let mut out = Self::empty();
        for entry in weight.entries() {
            out = out.compose(&Self::pops(entry.id, entry.pops));
        }
        out
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub(crate) fn entries(&self) -> &[LeftStackWeightEntry] {
        &self.entries
    }

    pub(crate) fn to_stack_weight(&self) -> StackWeight {
        let mut out = StackWeight::empty();
        for entry in &self.entries {
            out = out.compose(&StackWeight::pops(entry.id, entry.leading_pops));
            if entry.pushes > 0 {
                let family = entry.family.clone().unwrap_or(Subtractability::All);
                for _ in 0..entry.pushes {
                    out = out.compose(&StackWeight::push(entry.id, family.clone()));
                }
            }
        }
        out
    }

    pub(crate) fn entry(&self, id: SubtractId) -> Option<&LeftStackWeightEntry> {
        self.entries.iter().find(|entry| entry.id == id)
    }

    pub(crate) fn compose(&self, other: &Self) -> Self {
        let mut out = self.clone();
        for entry in &other.entries {
            out.push_entry(entry.clone());
        }
        out
    }

    fn push_entry(&mut self, incoming: LeftStackWeightEntry) {
        let Some(index) = self.entry_index(incoming.id) else {
            self.entries.push(incoming);
            self.entries.sort_by_key(|entry| entry.id.0);
            return;
        };

        let current = self.entries[index].clone();
        let family = merge_same_id_family(current.family.clone(), incoming.family.clone());
        let (leading_pops, pushes) = compose_same_id_counts(
            current.leading_pops,
            current.pushes,
            incoming.leading_pops,
            incoming.pushes,
        );
        if leading_pops == 0 && pushes == 0 {
            self.entries.remove(index);
            return;
        }
        self.entries[index] = LeftStackWeightEntry {
            id: current.id,
            leading_pops,
            family: (pushes > 0).then_some(family),
            pushes,
        };
    }

    fn remove(&mut self, id: SubtractId) {
        if let Some(index) = self.entry_index(id) {
            self.entries.remove(index);
        }
    }

    fn entry_index(&self, id: SubtractId) -> Option<usize> {
        self.entries.iter().position(|entry| entry.id == id)
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct LeftConstraintWeight {
    filter: Subtractability,
    weight: LeftStackWeight,
}

impl LeftConstraintWeight {
    pub fn empty() -> Self {
        Self::default()
    }

    pub fn filter(filter: Subtractability) -> Self {
        Self {
            filter,
            weight: LeftStackWeight::empty(),
        }
    }

    pub fn pop(id: SubtractId) -> Self {
        Self::pops(id, 1)
    }

    pub fn pops(id: SubtractId, count: u32) -> Self {
        Self {
            filter: Subtractability::All,
            weight: LeftStackWeight::pops(id, count),
        }
    }

    pub fn push(id: SubtractId, family: Subtractability) -> Self {
        Self {
            filter: Subtractability::All,
            weight: LeftStackWeight::take(id, family),
        }
    }

    pub fn from_ids(ids: impl IntoIterator<Item = SubtractId>) -> Self {
        let mut out = Self::empty();
        for id in ids {
            out = out.compose(&Self::pop(id));
        }
        out
    }

    pub(crate) fn from_stack_weight(weight: &StackWeight) -> Self {
        Self {
            filter: weight.filter_set().clone(),
            weight: LeftStackWeight::from_stack_weight(weight),
        }
    }

    pub(crate) fn from_right_weight(weight: &RightStackWeight) -> Self {
        Self {
            filter: Subtractability::All,
            weight: LeftStackWeight::from_right_weight(weight),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.filter == Subtractability::All && self.weight.is_empty()
    }

    pub fn has_filter(&self) -> bool {
        self.filter != Subtractability::All
    }

    pub fn filter_set(&self) -> &Subtractability {
        &self.filter
    }

    pub fn with_filter(&self, filter: Subtractability) -> Self {
        Self {
            filter,
            weight: self.weight.clone(),
        }
    }

    pub(crate) fn without_filter(&self) -> Self {
        self.with_filter(Subtractability::All)
    }

    pub(crate) fn entries(&self) -> &[LeftStackWeightEntry] {
        self.weight.entries()
    }

    pub fn contains(&self, id: SubtractId) -> bool {
        self.weight.entry(id).is_some()
    }

    pub fn iter(&self) -> impl Iterator<Item = SubtractId> + '_ {
        self.weight.entries().iter().map(|entry| entry.id)
    }

    pub(crate) fn active_stack_items(&self) -> impl Iterator<Item = &Subtractability> + '_ {
        self.weight
            .entries()
            .iter()
            .filter(|entry| entry.pushes > 0)
            .filter_map(|entry| entry.family.as_ref())
    }

    pub(crate) fn to_stack_weight(&self) -> StackWeight {
        self.weight
            .to_stack_weight()
            .with_filter(self.filter.clone())
    }

    pub(crate) fn compose(&self, other: &Self) -> Self {
        Self {
            filter: self.filter.clone().intersect(other.filter.clone()),
            weight: self.weight.compose(&other.weight),
        }
    }

    pub(crate) fn union(&self, other: &StackWeight) -> StackWeight {
        self.to_stack_weight().union(other)
    }

    pub(crate) fn directed(&self) -> &LeftStackWeight {
        &self.weight
    }

    pub(crate) fn with_directed_weight(&self, weight: LeftStackWeight) -> Self {
        Self {
            filter: self.filter.clone(),
            weight,
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq, Hash)]
pub struct RightStackWeight {
    entries: Vec<RightStackWeightEntry>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct RightStackWeightEntry {
    pub(crate) id: SubtractId,
    pub(crate) pops: u32,
}

impl RightStackWeight {
    pub(crate) fn empty() -> Self {
        Self::default()
    }

    pub(crate) fn pop(id: SubtractId) -> Self {
        Self::pops(id, 1)
    }

    pub(crate) fn pops(id: SubtractId, count: u32) -> Self {
        let mut out = Self::empty();
        if count > 0 {
            out.entries.push(RightStackWeightEntry { id, pops: count });
        }
        out
    }

    pub(crate) fn from_ids(ids: impl IntoIterator<Item = SubtractId>) -> Self {
        let mut out = Self::empty();
        for id in ids {
            out = out.compose(&Self::pop(id));
        }
        out
    }

    pub(crate) fn from_stack_weight_pops(weight: &StackWeight) -> Self {
        let mut out = Self::empty();
        for entry in weight.entries() {
            out = out.compose(&Self::pops(entry.id, entry.pops));
        }
        out
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub(crate) fn entries(&self) -> &[RightStackWeightEntry] {
        &self.entries
    }

    pub(crate) fn contains(&self, id: SubtractId) -> bool {
        self.entries.iter().any(|entry| entry.id == id)
    }

    pub(crate) fn to_stack_weight(&self) -> StackWeight {
        let mut out = StackWeight::empty();
        for entry in &self.entries {
            out = out.compose(&StackWeight::pops(entry.id, entry.pops));
        }
        out
    }

    pub(crate) fn compose(&self, other: &Self) -> Self {
        let mut out = self.clone();
        for entry in &other.entries {
            out.push_entry(*entry);
        }
        out
    }

    fn push_entry(&mut self, incoming: RightStackWeightEntry) {
        let Some(index) = self.entry_index(incoming.id) else {
            self.entries.push(incoming);
            self.entries.sort_by_key(|entry| entry.id.0);
            return;
        };
        self.entries[index].pops = self.entries[index].pops.saturating_add(incoming.pops);
    }

    fn entry_index(&self, id: SubtractId) -> Option<usize> {
        self.entries.iter().position(|entry| entry.id == id)
    }
}

fn compose_same_id_counts(m: u32, n: u32, p: u32, q: u32) -> (u32, u32) {
    if p <= n {
        (m, n - p + q)
    } else {
        (m.saturating_add(p - n), q)
    }
}

fn merge_same_id_family(
    left: Option<Subtractability>,
    right: Option<Subtractability>,
) -> Subtractability {
    match (left, right) {
        (Some(left), Some(right)) => {
            debug_assert_eq!(left, right, "one stack id must not use multiple families");
            left
        }
        (Some(family), None) | (None, Some(family)) => family,
        (None, None) => Subtractability::All,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn io() -> Subtractability {
        Subtractability::Set(vec!["io".into()], Vec::new())
    }

    #[test]
    fn same_id_take_then_pop_cancels() {
        let id = SubtractId(0);
        let weight = LeftStackWeight::take(id, io()).compose(&LeftStackWeight::pop(id));

        assert!(weight.is_empty());
    }

    #[test]
    fn same_id_pop_then_take_survives() {
        let id = SubtractId(0);
        let weight = LeftStackWeight::pop(id).compose(&LeftStackWeight::take(id, io()));
        let [entry] = weight.entries() else {
            panic!("expected one directed weight entry, got {weight:?}");
        };

        assert_eq!(entry.leading_pops, 1);
        assert_eq!(entry.family, Some(io()));
        assert_eq!(entry.pushes, 1);
    }

    #[test]
    fn mixed_projection_keeps_remaining_active_push_on_left() {
        let id = SubtractId(0);
        let left = LeftStackWeight::take(id, io()).compose(&LeftStackWeight::take(id, io()));
        let right = RightStackWeight::pop(id);
        let mixed = DirectedWeights { left, right }.mix();
        let [entry] = mixed.left.entries() else {
            panic!("expected one left entry, got {:?}", mixed.left);
        };

        assert_eq!(entry.leading_pops, 0);
        assert_eq!(entry.family, Some(io()));
        assert_eq!(entry.pushes, 1);
        assert!(mixed.right.is_empty());
    }

    #[test]
    fn mixed_projection_moves_pure_pop_to_right() {
        let id = SubtractId(0);
        let mixed = DirectedWeights {
            left: LeftStackWeight::take(id, io()),
            right: RightStackWeight::pops(id, 2),
        }
        .mix();
        let [entry] = mixed.right.entries() else {
            panic!("expected one right entry, got {:?}", mixed.right);
        };

        assert!(mixed.left.is_empty());
        assert_eq!(entry.id, id);
        assert_eq!(entry.pops, 1);
    }

    #[test]
    fn mixed_projection_does_not_move_single_sided_pop() {
        let id = SubtractId(0);
        let mixed = DirectedWeights {
            left: LeftStackWeight::empty(),
            right: RightStackWeight::pop(id),
        }
        .mix();
        let [entry] = mixed.right.entries() else {
            panic!("expected one right entry, got {:?}", mixed.right);
        };

        assert!(mixed.left.is_empty());
        assert_eq!(entry.id, id);
        assert_eq!(entry.pops, 1);
    }

    #[test]
    fn mixed_projection_moves_existing_left_pure_pop_to_right() {
        let id = SubtractId(0);
        let mixed = DirectedWeights {
            left: LeftStackWeight::pop(id),
            right: RightStackWeight::pop(id),
        }
        .mix();
        let [entry] = mixed.right.entries() else {
            panic!("expected one right entry, got {:?}", mixed.right);
        };

        assert!(mixed.left.is_empty());
        assert_eq!(entry.id, id);
        assert_eq!(entry.pops, 2);
    }
}
