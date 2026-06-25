use serde::{Deserialize, Serialize};

use crate::lowering::BodyLowering;

/// Lowered per-unit runtime surface.
///
/// The namespace/typed surfaces are enough for parsing and type lookup, but not
/// for executing cached dependency values. Runtime import needs the lowered
/// poly body graph and the labels that keep diagnostics/dumps readable. The
/// remap/merge step is intentionally separate from this serialized surface.
#[derive(Clone, Serialize, Deserialize)]
pub struct CompiledRuntimeSurface {
    pub arena: poly::expr::Arena,
    pub labels: poly::dump::DumpLabels,
}

impl CompiledRuntimeSurface {
    pub fn from_lowering(lowering: &BodyLowering) -> Self {
        Self {
            arena: lowering.session.poly.clone(),
            labels: lowering.labels.clone(),
        }
    }
}
