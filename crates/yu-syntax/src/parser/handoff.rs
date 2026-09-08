//! Shared completion and unread-Item handoff; grammar owners retain their own admission policy.
use crate::parser::input::{current_item::LineEntry, item::Item};
#[derive(Debug, Eq, PartialEq)]
pub(super) enum Either<L, R> {
    Left(L),
    Right(R),
}

#[derive(Debug, Eq, PartialEq)]
pub(super) struct End {
    pub(super) item: Item,
}

/// `Ok(())` lets the caller scan its successor after it closes its own node.
pub(super) type TailExit = Result<(), Either<Item, End>>;

#[derive(Clone, Copy)]
pub(super) enum MlMode {
    All,
    LayoutOnly,
    None,
}

pub(super) enum NormalizedExit {
    Complete(TailExit, LineEntry),
    #[allow(
        dead_code,
        reason = "normalized-exit frontier contract retains effect-free deferral"
    )]
    Deferred(Item, LineEntry),
}

pub(super) fn complete(exit: TailExit, line_entry: LineEntry) -> NormalizedExit {
    NormalizedExit::Complete(exit, line_entry)
}

#[cfg(test)]
pub(super) fn ordinary_exit(exit: NormalizedExit) -> TailExit {
    match exit {
        NormalizedExit::Complete(exit, _) => exit,
        NormalizedExit::Deferred(_, _) => {
            unreachable!("ordinary expressions enter every direct-parser owner")
        }
    }
}

pub(super) fn handoff(item: Item) -> TailExit {
    if item.payload_view().is_eof() {
        Err(Either::Right(End { item }))
    } else {
        Err(Either::Left(item))
    }
}
