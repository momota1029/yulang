//! Isolated source-free direct parser foundation.
//!
//! Source is borrowed only by the live `In<&str, ..>` cursor.  Logical items,
//! boundaries, and accepted trivia own every retained byte.

use chasa_recover::In;

mod act_decl;
mod binding;
mod case_like;
mod cast_decl;
mod current_item;
mod declaration_companion;
mod declaration_variant;
mod delimited;
mod derives;
mod driver;
mod emit;
mod enum_decl;
mod error_decl;
mod for_decl;
mod if_expr;
mod impl_decl;
mod item;
mod lexer;
mod literal;
mod mod_decl;
mod operator;
mod output;
mod pattern;
mod role_decl;
mod rule;
mod state;
mod statement;
mod struct_decl;
mod tails;
mod type_decl;
mod type_expr;
mod use_decl;
mod virtual_statement_block;
mod yumark;
#[cfg(test)]
mod yumark_cell;

#[cfg(test)]
mod tests;

type RewriteIn<'a, 'source, 'recover, 'operators, 'output, 'frozen> = In<
    'a,
    &'source str,
    &'recover mut state::Recover<'operators>,
    &'output mut output::RewriteOutput<'frozen>,
>;

type LexIn<'a, 'source, 'recover, 'operators> =
    In<'a, &'source str, &'recover mut state::Recover<'operators>, ()>;

type Stops = u16;
