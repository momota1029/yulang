#[cfg(test)]
use super::f5c_draft::{FlatDraft, NegativeId, NegativeNode, NodeRef, PositiveId, PositiveNode};
use super::{
    ConstraintStore, F5cComponentExpansionMemo, F5cNegative, F5cPositive, F5cWalkerLaneKind,
    Polarity, SolveAvailabilityError, Term, TermView,
};
use std::collections::HashSet;

pub(super) enum Task<'tree> {
    Positive(&'tree F5cPositive, bool),
    Negative(&'tree F5cNegative, bool),
    Term(Term),
    #[cfg(test)]
    FlatPositive(PositiveId, bool),
    #[cfg(test)]
    FlatNegative(NegativeId, bool),
}

enum Event {
    Value(u32, Polarity, bool),
    TermRow(u32),
}

/// Reusable explicit-stack visitor for producer-side F5c trees and Term DAGs.
/// The task lane remains live for this object's lifetime and is released when
/// the bounded analysis scope ends.
pub(super) struct Walker<'memo, 'tree> {
    pub(super) memo: &'memo mut F5cComponentExpansionMemo,
    tasks: Vec<Task<'tree>>,
}

impl<'memo, 'tree> Walker<'memo, 'tree> {
    pub(super) fn new(memo: &'memo mut F5cComponentExpansionMemo) -> Self {
        Self {
            memo,
            tasks: Vec::new(),
        }
    }

    fn push(&mut self, task: Task<'tree>) -> Result<(), SolveAvailabilityError> {
        self.memo.work_meter.charge(1)?; // scheduled analysis task
        self.memo
            .reserve_walker(&mut self.tasks, F5cWalkerLaneKind::AnalysisTasks)?;
        self.tasks.push(task);
        Ok(())
    }

    fn walk(
        &mut self,
        first: Task<'tree>,
        store: Option<&ConstraintStore>,
        #[cfg(test)] flat: Option<&FlatDraft>,
        mut visit: impl FnMut(
            Event,
            &mut F5cComponentExpansionMemo,
        ) -> Result<bool, SolveAvailabilityError>,
    ) -> Result<(), SolveAvailabilityError> {
        self.tasks.clear();
        let result = (|| {
            self.push(first)?;
            while !self.tasks.is_empty() {
                self.memo.work_meter.charge(1)?; // visited source node or Term
                let task = self.tasks.pop().expect("nonempty analysis tasks");
                match task {
                    Task::Positive(value, guarded) => match value {
                        F5cPositive::Variable(owner) => {
                            if !visit(Event::Value(*owner, Polarity::Positive, guarded), self.memo)?
                            {
                                break;
                            }
                        }
                        F5cPositive::Function {
                            argument, result, ..
                        } => {
                            self.memo.work_meter.charge(1)?; // result edge
                            self.push(Task::Positive(result, true))?;
                            self.memo.work_meter.charge(1)?; // argument edge
                            self.push(Task::Negative(argument, true))?;
                        }
                        F5cPositive::Union(values) => {
                            for value in values.iter().rev() {
                                self.memo.work_meter.charge(1)?; // union incidence
                                self.push(Task::Positive(value, guarded))?;
                            }
                        }
                        _ => {}
                    },
                    Task::Negative(value, guarded) => match value {
                        F5cNegative::Variable(owner) => {
                            if !visit(Event::Value(*owner, Polarity::Negative, guarded), self.memo)?
                            {
                                break;
                            }
                        }
                        F5cNegative::Function {
                            argument, result, ..
                        } => {
                            self.memo.work_meter.charge(1)?; // result edge
                            self.push(Task::Negative(result, true))?;
                            self.memo.work_meter.charge(1)?; // argument edge
                            self.push(Task::Positive(argument, true))?;
                        }
                        F5cNegative::Intersection(values) => {
                            for value in values.iter().rev() {
                                self.memo.work_meter.charge(1)?; // intersection incidence
                                self.push(Task::Negative(value, guarded))?;
                            }
                        }
                        _ => {}
                    },
                    Task::Term(term) => {
                        let Some(store) = store else {
                            return Err(SolveAvailabilityError::IdentityExhausted);
                        };
                        let Ok(view) = store.term_view(term) else {
                            continue;
                        };
                        match view {
                            TermView::LiveVariable(view) => {
                                if !visit(Event::TermRow(view.ordinal()), self.memo)? {
                                    break;
                                }
                            }
                            TermView::PositiveFunction {
                                argument, result, ..
                            }
                            | TermView::NegativeFunction {
                                argument, result, ..
                            } => {
                                self.memo.work_meter.charge(1)?; // result edge
                                self.push(Task::Term(result))?;
                                self.memo.work_meter.charge(1)?; // argument edge
                                self.push(Task::Term(argument))?;
                            }
                            _ => {}
                        }
                    }
                    #[cfg(test)]
                    Task::FlatPositive(id, guarded) => {
                        let flat = flat.ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        let node = flat
                            .positive_nodes
                            .get(
                                usize::try_from(id.0)
                                    .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
                            )
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        match *node {
                            PositiveNode::Variable(owner) => {
                                if !visit(
                                    Event::Value(owner, Polarity::Positive, guarded),
                                    self.memo,
                                )? {
                                    break;
                                }
                            }
                            PositiveNode::Function { argument, result } => {
                                self.memo.work_meter.charge(1)?;
                                self.push(Task::FlatPositive(result, true))?;
                                self.memo.work_meter.charge(1)?;
                                self.push(Task::FlatNegative(argument, true))?;
                            }
                            PositiveNode::Union(span) => {
                                let start = usize::try_from(span.start)
                                    .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
                                let end = usize::try_from(
                                    span.start
                                        .checked_add(span.len)
                                        .ok_or(SolveAvailabilityError::IdentityExhausted)?,
                                )
                                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
                                let children = flat
                                    .positive_children
                                    .get(start..end)
                                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                                for child in children.iter().rev() {
                                    self.memo.work_meter.charge(1)?;
                                    self.push(Task::FlatPositive(*child, guarded))?;
                                }
                            }
                            _ => {}
                        }
                    }
                    #[cfg(test)]
                    Task::FlatNegative(id, guarded) => {
                        let flat = flat.ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        let node = flat
                            .negative_nodes
                            .get(
                                usize::try_from(id.0)
                                    .map_err(|_| SolveAvailabilityError::IdentityExhausted)?,
                            )
                            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                        match *node {
                            NegativeNode::Variable(owner) => {
                                if !visit(
                                    Event::Value(owner, Polarity::Negative, guarded),
                                    self.memo,
                                )? {
                                    break;
                                }
                            }
                            NegativeNode::Function { argument, result } => {
                                self.memo.work_meter.charge(1)?;
                                self.push(Task::FlatNegative(result, true))?;
                                self.memo.work_meter.charge(1)?;
                                self.push(Task::FlatPositive(argument, true))?;
                            }
                            NegativeNode::Intersection(span) => {
                                let start = usize::try_from(span.start)
                                    .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
                                let end = usize::try_from(
                                    span.start
                                        .checked_add(span.len)
                                        .ok_or(SolveAvailabilityError::IdentityExhausted)?,
                                )
                                .map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
                                let children = flat
                                    .negative_children
                                    .get(start..end)
                                    .ok_or(SolveAvailabilityError::IdentityExhausted)?;
                                for child in children.iter().rev() {
                                    self.memo.work_meter.charge(1)?;
                                    self.push(Task::FlatNegative(*child, guarded))?;
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            Ok(())
        })();
        self.tasks.clear();
        result
    }

    pub(super) fn has_guarded_owner_positive(
        &mut self,
        value: &'tree F5cPositive,
        owner: u32,
    ) -> Result<bool, SolveAvailabilityError> {
        let mut found = false;
        self.walk(
            Task::Positive(value, false),
            None,
            #[cfg(test)]
            None,
            |event, _memo| {
                Ok({
                    if matches!(event, Event::Value(row, _, true) if row == owner) {
                        found = true;
                        false
                    } else {
                        true
                    }
                })
            },
        )?;
        Ok(found)
    }

    pub(super) fn has_guarded_owner_negative(
        &mut self,
        value: &'tree F5cNegative,
        owner: u32,
    ) -> Result<bool, SolveAvailabilityError> {
        let mut found = false;
        self.walk(
            Task::Negative(value, false),
            None,
            #[cfg(test)]
            None,
            |event, _memo| {
                Ok({
                    if matches!(event, Event::Value(row, _, true) if row == owner) {
                        found = true;
                        false
                    } else {
                        true
                    }
                })
            },
        )?;
        Ok(found)
    }

    pub(super) fn guarded_bound_survives(
        &mut self,
        owner: u32,
        lower: &'tree F5cPositive,
        upper: &'tree F5cNegative,
    ) -> Result<bool, SolveAvailabilityError> {
        if matches!(lower, F5cPositive::Bottom) && matches!(upper, F5cNegative::Top) {
            return Ok(false);
        }
        Ok(self.has_guarded_owner_positive(lower, owner)?
            || self.has_guarded_owner_negative(upper, owner)?)
    }

    pub(super) fn references_positive(
        &mut self,
        value: &'tree F5cPositive,
        owners: &HashSet<u32>,
        out: &mut HashSet<u32>,
    ) -> Result<(), SolveAvailabilityError> {
        self.walk(
            Task::Positive(value, false),
            None,
            #[cfg(test)]
            None,
            |event, _memo| {
                Ok({
                    if let Event::Value(owner, _, _) = event
                        && owners.contains(&owner)
                    {
                        out.insert(owner);
                    }
                    true
                })
            },
        )
    }

    pub(super) fn references_negative(
        &mut self,
        value: &'tree F5cNegative,
        owners: &HashSet<u32>,
        out: &mut HashSet<u32>,
    ) -> Result<(), SolveAvailabilityError> {
        self.walk(
            Task::Negative(value, false),
            None,
            #[cfg(test)]
            None,
            |event, _memo| {
                Ok({
                    if let Event::Value(owner, _, _) = event
                        && owners.contains(&owner)
                    {
                        out.insert(owner);
                    }
                    true
                })
            },
        )
    }

    pub(super) fn incidences_positive(
        &mut self,
        value: &'tree F5cPositive,
        positive: &mut HashSet<u32>,
        negative: &mut HashSet<u32>,
    ) -> Result<(), SolveAvailabilityError> {
        self.walk(
            Task::Positive(value, false),
            None,
            #[cfg(test)]
            None,
            |event, memo| {
                Ok({
                    if let Event::Value(owner, polarity, _) = event {
                        match polarity {
                            Polarity::Positive => {
                                memo.insert_physical_set(
                                    positive,
                                    owner,
                                    F5cWalkerLaneKind::RawPositiveIncidences,
                                )?;
                            }
                            Polarity::Negative => {
                                memo.insert_physical_set(
                                    negative,
                                    owner,
                                    F5cWalkerLaneKind::RawNegativeIncidences,
                                )?;
                            }
                        }
                    }
                    true
                })
            },
        )
    }

    pub(super) fn incidences_negative(
        &mut self,
        value: &'tree F5cNegative,
        positive: &mut HashSet<u32>,
        negative: &mut HashSet<u32>,
    ) -> Result<(), SolveAvailabilityError> {
        self.walk(
            Task::Negative(value, false),
            None,
            #[cfg(test)]
            None,
            |event, memo| {
                Ok({
                    if let Event::Value(owner, polarity, _) = event {
                        match polarity {
                            Polarity::Positive => {
                                memo.insert_physical_set(
                                    positive,
                                    owner,
                                    F5cWalkerLaneKind::RawPositiveIncidences,
                                )?;
                            }
                            Polarity::Negative => {
                                memo.insert_physical_set(
                                    negative,
                                    owner,
                                    F5cWalkerLaneKind::RawNegativeIncidences,
                                )?;
                            }
                        }
                    }
                    true
                })
            },
        )
    }

    pub(super) fn occurrences_positive(
        &mut self,
        value: &'tree F5cPositive,
        ordered: &mut Vec<u32>,
        seen: &mut HashSet<u32>,
    ) -> Result<(), SolveAvailabilityError> {
        self.walk(
            Task::Positive(value, false),
            None,
            #[cfg(test)]
            None,
            |event, _memo| {
                Ok({
                    if let Event::Value(owner, _, _) = event
                        && seen.insert(owner)
                    {
                        ordered.push(owner);
                    }
                    true
                })
            },
        )
    }

    pub(super) fn occurrences_negative(
        &mut self,
        value: &'tree F5cNegative,
        ordered: &mut Vec<u32>,
        seen: &mut HashSet<u32>,
    ) -> Result<(), SolveAvailabilityError> {
        self.walk(
            Task::Negative(value, false),
            None,
            #[cfg(test)]
            None,
            |event, _memo| {
                Ok({
                    if let Event::Value(owner, _, _) = event
                        && seen.insert(owner)
                    {
                        ordered.push(owner);
                    }
                    true
                })
            },
        )
    }

    #[cfg(test)]
    pub(super) fn term_rows(
        &mut self,
        store: &ConstraintStore,
        term: Term,
        rows: &mut HashSet<u32>,
    ) -> Result<(), SolveAvailabilityError> {
        self.term_rows_with_lane(store, term, rows, None)
    }

    pub(super) fn term_rows_with_lane(
        &mut self,
        store: &ConstraintStore,
        term: Term,
        rows: &mut HashSet<u32>,
        lane: Option<F5cWalkerLaneKind>,
    ) -> Result<(), SolveAvailabilityError> {
        self.walk(
            Task::Term(term),
            Some(store),
            #[cfg(test)]
            None,
            |event, memo| {
                Ok({
                    if let Event::TermRow(row) = event {
                        if let Some(kind) = lane {
                            memo.insert_physical_set(rows, row, kind)?;
                        } else {
                            rows.insert(row);
                        }
                    }
                    true
                })
            },
        )
    }
    #[cfg(test)]
    fn flat_events(
        &mut self,
        draft: &FlatDraft,
        root: NodeRef,
        mut visit: impl FnMut(u32, Polarity, bool) -> bool,
    ) -> Result<(), SolveAvailabilityError> {
        self.flat_events_checked(draft, root, |owner, polarity, guarded, _memo| {
            Ok(visit(owner, polarity, guarded))
        })
    }

    #[cfg(test)]
    fn flat_events_checked(
        &mut self,
        draft: &FlatDraft,
        root: NodeRef,
        mut visit: impl FnMut(
            u32,
            Polarity,
            bool,
            &mut F5cComponentExpansionMemo,
        ) -> Result<bool, SolveAvailabilityError>,
    ) -> Result<(), SolveAvailabilityError> {
        let first = match root {
            NodeRef::Positive(id) => Task::FlatPositive(id, false),
            NodeRef::Negative(id) => Task::FlatNegative(id, false),
        };
        self.walk(first, None, Some(draft), |event, memo| match event {
            Event::Value(owner, polarity, guarded) => visit(owner, polarity, guarded, memo),
            Event::TermRow(_) => Ok(true),
        })
    }

    #[cfg(test)]
    pub(super) fn trace_values(
        &mut self,
        draft: Option<&FlatDraft>,
        root: Task<'tree>,
        limit: usize,
    ) -> Result<Vec<(u32, Polarity, bool)>, SolveAvailabilityError> {
        let mut trace = Vec::new();
        self.walk(root, None, draft, |event, _memo| {
            Ok({
                if let Event::Value(owner, polarity, guarded) = event {
                    trace.push((owner, polarity, guarded));
                    trace.len() < limit
                } else {
                    true
                }
            })
        })?;
        Ok(trace)
    }

    #[cfg(test)]
    pub(super) fn tasks_are_clear_for_test(&self) -> bool {
        self.tasks.is_empty()
    }

    #[cfg(test)]
    pub(super) fn flat_guarded_bound_survives(
        &mut self,
        draft: &FlatDraft,
        owner: u32,
        lower: PositiveId,
        upper: NegativeId,
    ) -> Result<bool, SolveAvailabilityError> {
        let lower_index =
            usize::try_from(lower.0).map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let upper_index =
            usize::try_from(upper.0).map_err(|_| SolveAvailabilityError::IdentityExhausted)?;
        let lower_node = draft
            .positive_nodes
            .get(lower_index)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        let upper_node = draft
            .negative_nodes
            .get(upper_index)
            .ok_or(SolveAvailabilityError::IdentityExhausted)?;
        if matches!(lower_node, PositiveNode::Bottom) && matches!(upper_node, NegativeNode::Top) {
            return Ok(false);
        }
        let mut found = false;
        self.flat_events(draft, NodeRef::Positive(lower), |row, _, guarded| {
            found = guarded && row == owner;
            !found
        })?;
        if !found {
            self.flat_events(draft, NodeRef::Negative(upper), |row, _, guarded| {
                found = guarded && row == owner;
                !found
            })?;
        }
        Ok(found)
    }

    #[cfg(test)]
    pub(super) fn flat_references(
        &mut self,
        draft: &FlatDraft,
        root: NodeRef,
        owners: &HashSet<u32>,
        out: &mut HashSet<u32>,
    ) -> Result<(), SolveAvailabilityError> {
        self.flat_events(draft, root, |owner, _, _| {
            if owners.contains(&owner) {
                out.insert(owner);
            }
            true
        })
    }

    #[cfg(test)]
    pub(super) fn flat_incidences(
        &mut self,
        draft: &FlatDraft,
        root: NodeRef,
        positive: &mut HashSet<u32>,
        negative: &mut HashSet<u32>,
    ) -> Result<(), SolveAvailabilityError> {
        self.flat_events_checked(draft, root, |owner, polarity, _, memo| {
            match polarity {
                Polarity::Positive => {
                    memo.insert_physical_set(
                        positive,
                        owner,
                        F5cWalkerLaneKind::RawPositiveIncidences,
                    )?;
                }
                Polarity::Negative => {
                    memo.insert_physical_set(
                        negative,
                        owner,
                        F5cWalkerLaneKind::RawNegativeIncidences,
                    )?;
                }
            }
            Ok(true)
        })
    }

    #[cfg(test)]
    pub(super) fn flat_occurrences(
        &mut self,
        draft: &FlatDraft,
        root: NodeRef,
        ordered: &mut Vec<u32>,
        seen: &mut HashSet<u32>,
    ) -> Result<(), SolveAvailabilityError> {
        self.flat_events(draft, root, |owner, _, _| {
            if seen.insert(owner) {
                ordered.push(owner);
            }
            true
        })
    }

    #[cfg(test)]
    pub(super) fn flat_occurrences_checked(
        &mut self,
        draft: &FlatDraft,
        root: NodeRef,
        ordered: &mut Vec<u32>,
        seen: &mut HashSet<u32>,
        mut reserve: impl FnMut(
            &mut F5cComponentExpansionMemo,
            &mut Vec<u32>,
            &mut HashSet<u32>,
        ) -> Result<(), SolveAvailabilityError>,
    ) -> Result<(), SolveAvailabilityError> {
        self.flat_events_checked(draft, root, |owner, _, _, memo| {
            if !seen.contains(&owner) {
                reserve(memo, ordered, seen)?;
                seen.insert(owner);
                ordered.push(owner);
            }
            Ok(true)
        })
    }
}

impl Drop for Walker<'_, '_> {
    fn drop(&mut self) {
        self.memo
            .walker_resources
            .release(F5cWalkerLaneKind::AnalysisTasks);
    }
}
