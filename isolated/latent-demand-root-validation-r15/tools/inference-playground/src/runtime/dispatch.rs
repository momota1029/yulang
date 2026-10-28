//! Static member dictionaries and immutable substitutions of initializer scopes.
//! These carry no runtime value tags or receiving/effect authority.
use super::program::RuntimeUnavailable;
use std::collections::HashMap;
use yu_hir::{HirOccurrenceId, SourceRootId};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(super) struct Site {
    pub owner: SourceRootId,
    pub occurrence: HirOccurrenceId,
}
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub(super) enum Kind {
    Name,
    Operator,
    Member,
}
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub(super) struct Step {
    pub kind: Kind,
    pub site: Site,
}
#[derive(Clone, Copy, Debug, Default)]
pub(super) struct Context {
    base: Option<usize>,
    word: Option<usize>,
}
#[derive(Clone, Copy, Debug, Default)]
pub(super) struct State {
    pub context: Context,
    pub substitution: Option<usize>,
}
enum Word {
    Step(Option<usize>, Step),
    Join(usize, usize),
}
#[derive(Clone, Copy)]
enum Substitution {
    Assign(usize, Context),
    Then(usize, usize),
}
#[derive(Default)]
pub(super) struct Machine {
    words: Vec<Word>,
    substitutions: Vec<Substitution>,
    defaults: HashMap<usize, Context>,
}
const WORK_LIMIT: usize = 32_768;
impl Machine {
    fn join_words(
        &mut self,
        a: Option<usize>,
        b: Option<usize>,
    ) -> Result<Option<usize>, RuntimeUnavailable> {
        Ok(match (a, b) {
            (None, word) | (word, None) => word,
            (Some(a), Some(b)) => {
                self.words
                    .try_reserve(1)
                    .map_err(|_| RuntimeUnavailable::IdentityExhausted)?;
                let id = self.words.len();
                self.words.push(Word::Join(a, b));
                Some(id)
            }
        })
    }
    pub fn append(&mut self, context: Context, step: Step) -> Result<Context, RuntimeUnavailable> {
        self.words
            .try_reserve(1)
            .map_err(|_| RuntimeUnavailable::IdentityExhausted)?;
        let id = self.words.len();
        self.words.push(Word::Step(context.word, step));
        Ok(Context {
            base: context.base,
            word: Some(id),
        })
    }
    pub fn then(
        &mut self,
        first: Option<usize>,
        second: Option<usize>,
    ) -> Result<Option<usize>, RuntimeUnavailable> {
        Ok(match (first, second) {
            (None, substitution) | (substitution, None) => substitution,
            (Some(a), Some(b)) => {
                self.substitutions
                    .try_reserve(1)
                    .map_err(|_| RuntimeUnavailable::IdentityExhausted)?;
                let id = self.substitutions.len();
                self.substitutions.push(Substitution::Then(a, b));
                Some(id)
            }
        })
    }
    #[cfg(test)]
    fn apply(
        &mut self,
        context: Context,
        substitution: Option<usize>,
    ) -> Result<Context, RuntimeUnavailable> {
        self.apply_bounded(context, substitution, &mut 0)
    }
    fn apply_bounded(
        &mut self,
        mut context: Context,
        substitution: Option<usize>,
        work: &mut usize,
    ) -> Result<Context, RuntimeUnavailable> {
        let mut pending = Vec::new();
        pending
            .try_reserve(1)
            .map_err(|_| RuntimeUnavailable::IdentityExhausted)?;
        if let Some(id) = substitution {
            pending.push(id);
        }
        while let Some(id) = pending.pop() {
            charge(work)?;
            match *self
                .substitutions
                .get(id)
                .ok_or(RuntimeUnavailable::InvalidSourceReference)?
            {
                Substitution::Then(a, b) => {
                    if a >= id || b >= id {
                        return Err(RuntimeUnavailable::InvalidSourceReference);
                    }
                    pending
                        .try_reserve(2)
                        .map_err(|_| RuntimeUnavailable::IdentityExhausted)?;
                    pending.extend([b, a]);
                }
                Substitution::Assign(scope, replacement) if context.base == Some(scope) => {
                    context = Context {
                        base: replacement.base,
                        word: self.join_words(replacement.word, context.word)?,
                    };
                }
                Substitution::Assign(_, _) => {}
            }
        }
        Ok(context)
    }
    pub fn initializer(&mut self, cell: usize, parent: State) -> Result<State, RuntimeUnavailable> {
        self.defaults
            .try_reserve(1)
            .map_err(|_| RuntimeUnavailable::IdentityExhausted)?;
        // The initializer inherits parent.substitution below. Retain the raw
        // parent context so resolving this default applies that substitution
        // once, including when it is deliberately non-idempotent.
        if self.defaults.insert(cell, parent.context).is_some() {
            return Err(RuntimeUnavailable::InvalidSourceReference);
        }
        Ok(State {
            context: Context {
                base: Some(cell),
                word: None,
            },
            substitution: parent.substitution,
        })
    }
    pub fn name(
        &mut self,
        value: Option<usize>,
        current: State,
        cell: usize,
        instantiate: Option<Step>,
    ) -> Result<Option<usize>, RuntimeUnavailable> {
        let mut result = value;
        if let Some(step) = instantiate {
            if !self.defaults.contains_key(&cell) {
                return Err(RuntimeUnavailable::InvalidSourceReference);
            }
            // Applying the caller substitution here as well as in `then`
            // below would duplicate it. Substitution is ordered, not assumed
            // idempotent; retain the symbolic caller context in the assignment.
            let replacement = self.append(current.context, step)?;
            self.substitutions
                .try_reserve(1)
                .map_err(|_| RuntimeUnavailable::IdentityExhausted)?;
            let id = self.substitutions.len();
            self.substitutions
                .push(Substitution::Assign(cell, replacement));
            result = self.then(result, Some(id))?;
        }
        self.then(result, current.substitution)
    }
    pub fn word(&mut self, state: State) -> Result<Vec<Step>, RuntimeUnavailable> {
        let mut work = 0usize;
        let mut context = self.apply_bounded(state.context, state.substitution, &mut work)?;
        while let Some(scope) = context.base {
            charge(&mut work)?;
            let default = *self
                .defaults
                .get(&scope)
                .ok_or(RuntimeUnavailable::InvalidSourceReference)?;
            let default = self.apply_bounded(default, state.substitution, &mut work)?;
            context = Context {
                base: default.base,
                word: self.join_words(default.word, context.word)?,
            };
        }
        let mut result = Vec::new();
        let mut pending = Vec::new();
        pending
            .try_reserve(1)
            .map_err(|_| RuntimeUnavailable::IdentityExhausted)?;
        if let Some(word) = context.word {
            pending.push((word, false));
        }
        while let Some((id, emit)) = pending.pop() {
            charge(&mut work)?;
            match self
                .words
                .get(id)
                .ok_or(RuntimeUnavailable::InvalidSourceReference)?
            {
                Word::Step(_, step) if emit => {
                    result
                        .try_reserve(1)
                        .map_err(|_| RuntimeUnavailable::IdentityExhausted)?;
                    result.push(step.clone());
                }
                Word::Step(previous, _) => {
                    if previous.is_some_and(|previous| previous >= id) {
                        return Err(RuntimeUnavailable::InvalidSourceReference);
                    }
                    pending
                        .try_reserve(2)
                        .map_err(|_| RuntimeUnavailable::IdentityExhausted)?;
                    pending.push((id, true));
                    if let Some(previous) = previous {
                        pending.push((*previous, false));
                    }
                }
                Word::Join(a, b) => {
                    if *a >= id || *b >= id {
                        return Err(RuntimeUnavailable::InvalidSourceReference);
                    }
                    pending
                        .try_reserve(2)
                        .map_err(|_| RuntimeUnavailable::IdentityExhausted)?;
                    pending.extend([(*b, false), (*a, false)]);
                }
            }
        }
        Ok(result)
    }
}

fn charge(work: &mut usize) -> Result<(), RuntimeUnavailable> {
    *work += 1;
    if *work > WORK_LIMIT {
        Err(RuntimeUnavailable::IdentityExhausted)
    } else {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn name_and_initializer_apply_nonidempotent_caller_substitution_once() {
        let source = "my add x = x + x\nmy main = (add 3, add \"a\")\n";
        let (_, candidate, _, _) =
            crate::prepare_with_world(source, "dictionary-order.yu", false).unwrap();
        let selected = candidate
            .selected_field_tail_uses()
            .unwrap()
            .next()
            .unwrap();
        let step = Step {
            kind: Kind::Name,
            site: Site {
                owner: selected.source_owner.clone(),
                occurrence: selected.occurrence.clone(),
            },
        };
        let mut machine = Machine::default();
        for cell in 0..3 {
            machine.initializer(cell, State::default()).unwrap();
        }
        // Ordered [1 := empty; 0 := 1] is intentionally not idempotent:
        // applying it once to 0 gives 1; twice gives empty.
        machine
            .substitutions
            .push(Substitution::Assign(1, Context::default()));
        machine.substitutions.push(Substitution::Assign(
            0,
            Context {
                base: Some(1),
                word: None,
            },
        ));
        let substitution = machine.then(Some(0), Some(1)).unwrap();
        let caller = State {
            context: Context {
                base: Some(0),
                word: None,
            },
            substitution,
        };
        let inner = machine.initializer(3, caller).unwrap();
        assert_eq!(machine.defaults[&3].base, Some(0));
        assert_eq!(inner.substitution, substitution);
        let use_ = machine.name(None, caller, 2, Some(step.clone())).unwrap();
        let result = machine
            .apply(
                Context {
                    base: Some(2),
                    word: None,
                },
                use_,
            )
            .unwrap();
        assert_eq!(result.base, Some(1));
        assert_eq!(
            machine
                .word(State {
                    context: result,
                    substitution: None
                })
                .unwrap(),
            vec![step]
        );
    }

    #[test]
    fn substitutions_are_ordered_and_initializer_defaults_remain_symbolic() {
        let mut machine = Machine::default();
        let outer = machine.initializer(0, State::default()).unwrap();
        let inner = machine.initializer(1, outer).unwrap();
        assert_eq!(machine.defaults[&1].base, Some(0));
        machine.substitutions.push(Substitution::Assign(
            1,
            Context {
                base: Some(0),
                word: None,
            },
        ));
        machine
            .substitutions
            .push(Substitution::Assign(0, Context::default()));
        let ordered = machine.then(Some(0), Some(1)).unwrap();
        let reversed = machine.then(Some(1), Some(0)).unwrap();
        assert_eq!(machine.apply(inner.context, ordered).unwrap().base, None);
        assert_eq!(
            machine.apply(inner.context, reversed).unwrap().base,
            Some(0)
        );
        assert!(machine.word(inner).unwrap().is_empty());
        assert!(matches!(
            machine.initializer(1, outer),
            Err(RuntimeUnavailable::InvalidSourceReference)
        ));
    }

    #[test]
    fn compact_dags_bound_expanded_work_and_reject_invalid_edges() {
        let mut machine = Machine::default();
        machine
            .substitutions
            .push(Substitution::Assign(0, Context::default()));
        let mut substitution = Some(0);
        for _ in 0..16 {
            substitution = machine.then(substitution, substitution).unwrap();
        }
        assert!(matches!(
            machine.apply(Context::default(), substitution),
            Err(RuntimeUnavailable::IdentityExhausted)
        ));
        let bad = machine.substitutions.len();
        machine.substitutions.push(Substitution::Then(bad, 0));
        assert!(matches!(
            machine.apply(Context::default(), Some(bad)),
            Err(RuntimeUnavailable::InvalidSourceReference)
        ));
        machine.defaults.insert(
            0,
            Context {
                base: Some(0),
                word: None,
            },
        );
        assert!(matches!(
            machine.word(State {
                context: Context {
                    base: Some(0),
                    word: None
                },
                substitution: None
            }),
            Err(RuntimeUnavailable::IdentityExhausted)
        ));
        machine.words.push(Word::Join(0, 0));
        assert!(matches!(
            machine.word(State {
                context: Context {
                    base: None,
                    word: Some(0)
                },
                substitution: None
            }),
            Err(RuntimeUnavailable::InvalidSourceReference)
        ));
    }
}
