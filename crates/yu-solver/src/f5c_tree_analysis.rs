use super::{
    ConstraintStore, F5cComponentExpansionMemo, F5cNegative, F5cPositive, F5cWalkerLaneKind,
    Polarity, SolveAvailabilityError, Term, TermView,
};
use std::collections::HashSet;

pub(super) enum Task<'tree> {
    Positive(&'tree F5cPositive, bool),
    Negative(&'tree F5cNegative, bool),
    Term(Term),
}

enum Event {
    Value(u32, Polarity, bool),
    TermRow(u32),
}

/// Reusable explicit-stack visitor for producer-side F5c trees and Term DAGs.
/// The task lane remains live for this object's lifetime and is released when
/// the bounded analysis scope ends.
pub(super) struct Walker<'memo, 'tree> {
    memo: &'memo mut F5cComponentExpansionMemo,
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
        self.memo
            .reserve_walker(&mut self.tasks, F5cWalkerLaneKind::AnalysisTasks)?;
        self.tasks.push(task);
        Ok(())
    }

    fn walk(
        &mut self,
        first: Task<'tree>,
        store: Option<&ConstraintStore>,
        mut visit: impl FnMut(Event) -> bool,
    ) -> Result<(), SolveAvailabilityError> {
        self.tasks.clear();
        let result = (|| {
            self.push(first)?;
            while let Some(task) = self.tasks.pop() {
                match task {
                    Task::Positive(value, guarded) => match value {
                        F5cPositive::Variable(owner) => {
                            if !visit(Event::Value(*owner, Polarity::Positive, guarded)) {
                                break;
                            }
                        }
                        F5cPositive::Function {
                            argument, result, ..
                        } => {
                            self.push(Task::Positive(result, true))?;
                            self.push(Task::Negative(argument, true))?;
                        }
                        F5cPositive::Union(values) => {
                            for value in values.iter().rev() {
                                self.push(Task::Positive(value, guarded))?;
                            }
                        }
                        _ => {}
                    },
                    Task::Negative(value, guarded) => match value {
                        F5cNegative::Variable(owner) => {
                            if !visit(Event::Value(*owner, Polarity::Negative, guarded)) {
                                break;
                            }
                        }
                        F5cNegative::Function {
                            argument, result, ..
                        } => {
                            self.push(Task::Negative(result, true))?;
                            self.push(Task::Positive(argument, true))?;
                        }
                        F5cNegative::Intersection(values) => {
                            for value in values.iter().rev() {
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
                                if !visit(Event::TermRow(view.ordinal())) {
                                    break;
                                }
                            }
                            TermView::PositiveFunction {
                                argument, result, ..
                            }
                            | TermView::NegativeFunction {
                                argument, result, ..
                            } => {
                                self.push(Task::Term(result))?;
                                self.push(Task::Term(argument))?;
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
        self.walk(Task::Positive(value, false), None, |event| {
            if matches!(event, Event::Value(row, _, true) if row == owner) {
                found = true;
                false
            } else {
                true
            }
        })?;
        Ok(found)
    }

    pub(super) fn has_guarded_owner_negative(
        &mut self,
        value: &'tree F5cNegative,
        owner: u32,
    ) -> Result<bool, SolveAvailabilityError> {
        let mut found = false;
        self.walk(Task::Negative(value, false), None, |event| {
            if matches!(event, Event::Value(row, _, true) if row == owner) {
                found = true;
                false
            } else {
                true
            }
        })?;
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
        self.walk(Task::Positive(value, false), None, |event| {
            if let Event::Value(owner, _, _) = event
                && owners.contains(&owner)
            {
                out.insert(owner);
            }
            true
        })
    }

    pub(super) fn references_negative(
        &mut self,
        value: &'tree F5cNegative,
        owners: &HashSet<u32>,
        out: &mut HashSet<u32>,
    ) -> Result<(), SolveAvailabilityError> {
        self.walk(Task::Negative(value, false), None, |event| {
            if let Event::Value(owner, _, _) = event
                && owners.contains(&owner)
            {
                out.insert(owner);
            }
            true
        })
    }

    pub(super) fn incidences_positive(
        &mut self,
        value: &'tree F5cPositive,
        positive: &mut HashSet<u32>,
        negative: &mut HashSet<u32>,
    ) -> Result<(), SolveAvailabilityError> {
        self.walk(Task::Positive(value, false), None, |event| {
            if let Event::Value(owner, polarity, _) = event {
                match polarity {
                    Polarity::Positive => {
                        positive.insert(owner);
                    }
                    Polarity::Negative => {
                        negative.insert(owner);
                    }
                }
            }
            true
        })
    }

    pub(super) fn incidences_negative(
        &mut self,
        value: &'tree F5cNegative,
        positive: &mut HashSet<u32>,
        negative: &mut HashSet<u32>,
    ) -> Result<(), SolveAvailabilityError> {
        self.walk(Task::Negative(value, false), None, |event| {
            if let Event::Value(owner, polarity, _) = event {
                match polarity {
                    Polarity::Positive => {
                        positive.insert(owner);
                    }
                    Polarity::Negative => {
                        negative.insert(owner);
                    }
                }
            }
            true
        })
    }

    pub(super) fn occurrences_positive(
        &mut self,
        value: &'tree F5cPositive,
        ordered: &mut Vec<u32>,
        seen: &mut HashSet<u32>,
    ) -> Result<(), SolveAvailabilityError> {
        self.walk(Task::Positive(value, false), None, |event| {
            if let Event::Value(owner, _, _) = event
                && seen.insert(owner)
            {
                ordered.push(owner);
            }
            true
        })
    }

    pub(super) fn occurrences_negative(
        &mut self,
        value: &'tree F5cNegative,
        ordered: &mut Vec<u32>,
        seen: &mut HashSet<u32>,
    ) -> Result<(), SolveAvailabilityError> {
        self.walk(Task::Negative(value, false), None, |event| {
            if let Event::Value(owner, _, _) = event
                && seen.insert(owner)
            {
                ordered.push(owner);
            }
            true
        })
    }

    pub(super) fn term_rows(
        &mut self,
        store: &ConstraintStore,
        term: Term,
        rows: &mut HashSet<u32>,
    ) -> Result<(), SolveAvailabilityError> {
        self.walk(Task::Term(term), Some(store), |event| {
            if let Event::TermRow(row) = event {
                rows.insert(row);
            }
            true
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
