//! Isolated source-free direct parser foundation.
//!
//! Source is borrowed only by the live `In<&str, ..>` cursor.  Logical items,
//! boundaries, and accepted trivia own every retained byte.

mod driver;
mod item;
mod state;

#[cfg(test)]
mod tests;
