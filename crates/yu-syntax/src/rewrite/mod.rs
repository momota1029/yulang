//! Isolated direct expression/tail pilot for the recursive-descent rewrite.
//!
//! Nothing in this module is connected to production parser dispatch. Grammar
//! owners emit through `PilotOutput` as soon as they accept a branch, while an
//! unread tail item is handed directly to the enclosing level without replay.

mod driver;
mod item;
mod state;

#[cfg(test)]
mod tests;
