//! Canonical type and effect boundary for Yulang3.

/// A type whose representation is fixed across the collection boundary.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum CanonicalType {
    Int,
}
