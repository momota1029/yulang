//! Isolated source-free direct parser foundation.
//!
//! Source is borrowed only by the live `In<&str, ..>` cursor.  Logical items,
//! boundaries, and accepted trivia own every retained byte.

use chasa_recover::In;
use rowan::GreenNodeBuilder;

mod delimited;
mod driver;
mod emit;
mod item;
mod lexer;
mod operator;
mod pattern;
mod state;
mod statement;
mod tails;
mod type_expr;

#[cfg(test)]
mod tests;

type RewriteIn<'a, 'source, 'recover, 'operators, 'builder> = In<
    'a,
    &'source str,
    &'recover mut state::Recover<'operators>,
    &'builder mut GreenNodeBuilder<'static>,
>;

type LexIn<'a, 'source, 'recover, 'operators> =
    In<'a, &'source str, &'recover mut state::Recover<'operators>, ()>;
