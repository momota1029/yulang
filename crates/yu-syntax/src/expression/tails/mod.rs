//! Fixed continuations dispatched by the expression operator chain.

mod colon;
mod delimited_tail;
mod fixed_access;
mod inline_slot;
mod with_body;

pub(crate) use colon::colon_tail_normalized;
pub(crate) use delimited_tail::{call_tail_normalized, index_tail_normalized};
pub(crate) use fixed_access::{dot_tail_normalized, path_tail_normalized};
pub(crate) use with_body::with_tail_normalized;
