//! A small experimental core for recoverable, procedure-oriented parsing.
//!
//! `None` means non-match without input consumption. Recovered syntax is a
//! normal `Some` output chosen by the grammar. See `DESIGN-0.2.md` in the
//! crate root for the transaction and composition rules.

pub mod input;
pub mod parser;

pub use input::{In, Input, Recover, Recoverable};
pub use parser::ParserOnce;
