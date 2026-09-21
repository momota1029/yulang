//! Canonical type and effect boundary for Yulang3.
//!
//! This first slice intentionally contains leaves only. Constraint ownership,
//! component identities, and solved projections stay in `yu-solver`.

/// The two independently solved component families.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ComponentKind {
    Value,
    Effect,
}

/// The direction in which a leaf bounds a component.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Polarity {
    Positive,
    Negative,
}

/// The complete leaf set admitted by the directed-subtyping integer slice.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Leaf {
    IntPositive,
    IntNegative,
    EffectBottomPositive,
    EmptyEffectNegative,
}

/// A closed positive value produced by component generalization.
///
/// This intentionally has no variables or error sentinel: the current F4
/// integer slice only generalizes ordinary bottom and `Int`.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum ClosedPositiveValue {
    Bottom,
    Int,
}

/// The canonical closed value scheme for one finalized definition root.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct ClosedValueScheme {
    body: ClosedPositiveValue,
}

impl ClosedValueScheme {
    pub const fn new(body: ClosedPositiveValue) -> Self {
        Self { body }
    }

    pub const fn body(self) -> ClosedPositiveValue {
        self.body
    }
}

impl Leaf {
    pub const fn component_kind(self) -> ComponentKind {
        match self {
            Self::IntPositive | Self::IntNegative => ComponentKind::Value,
            Self::EffectBottomPositive | Self::EmptyEffectNegative => ComponentKind::Effect,
        }
    }

    pub const fn polarity(self) -> Polarity {
        match self {
            Self::IntPositive | Self::EffectBottomPositive => Polarity::Positive,
            Self::IntNegative | Self::EmptyEffectNegative => Polarity::Negative,
        }
    }
}
