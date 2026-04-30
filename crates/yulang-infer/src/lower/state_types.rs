use crate::ids::{NegId, PosId, TypeVar};
use crate::symbols::Path;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FunctionSigEffectHint {
    Pure,
    Through,
    LowerBound(PosId),
    Bounds(PosId, NegId),
}

#[derive(Debug, Clone)]
pub struct EnumVariantPatternShape {
    pub enum_path: Path,
    pub type_param_names: Vec<String>,
    pub payload_sig: Option<crate::lower::signature::SigType>,
}

#[derive(Debug, Clone, Copy)]
pub struct ActiveRecursiveSelfInstance {
    pub tv: TypeVar,
    pub eff_tv: TypeVar,
}
