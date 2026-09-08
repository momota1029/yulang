//! Syntax parser ownership, lexical input, and committed output.
//!
//! Source is borrowed only by the live `In<&str, ..>` cursor.  Logical items,
//! boundaries, and accepted trivia own every retained byte.

use chasa_recover::In;

mod context;
mod declaration;
mod expression;
mod handoff;
pub(crate) mod header;
mod input;
mod literal;
mod output;
mod pattern;
pub(crate) mod root;
mod rule;
mod statement;
mod type_expr;
mod virtual_statement_block;

#[cfg(test)]
mod tests;

type ParserIn<'a, 'source, 'recover, 'operators, 'output, 'frozen> = In<
    'a,
    &'source str,
    &'recover mut context::state::Recover<'operators>,
    &'output mut output::ParserOutput<'frozen>,
>;

type LexIn<'a, 'source, 'recover, 'operators> =
    In<'a, &'source str, &'recover mut context::state::Recover<'operators>, ()>;

type Stops = u16;
