//! Canonical compiled-interface closure and alpha-equivalence support.
//!
//! This module is intentionally read-only.  It inventories finalized `poly`
//! structures for cache-interface tests without resolving roles, instantiating
//! schemes, or mutating the inference constraint machine.

mod alpha;
mod closure;

pub use alpha::*;
pub use closure::*;

#[cfg(test)]
mod tests;
