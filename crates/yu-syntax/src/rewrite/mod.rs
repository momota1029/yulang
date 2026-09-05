//! Isolated source-free direct parser foundation.
//!
//! Source is borrowed only by the live `In<&str, ..>` cursor.  Logical items,
//! boundaries, and accepted trivia own every retained byte.

use chasa_recover::In;
use rowan::GreenNodeBuilder;

mod binding;
mod case_like;
mod current_item;
mod delimited;
mod derives;
mod driver;
mod emit;
mod for_decl;
mod if_expr;
mod item;
mod lexer;
mod literal;
mod mod_decl;
mod operator;
mod pattern;
mod rule;
mod state;
mod statement;
mod struct_decl;
mod tails;
mod type_decl;
mod type_expr;
mod use_decl;
mod yumark;
#[cfg(test)]
mod yumark_cell;

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

type Stops = u16;
