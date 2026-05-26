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
    pub payload: EnumVariantPatternPayload,
}

#[derive(Debug, Clone)]
pub enum EnumVariantPatternPayload {
    Source {
        type_param_names: Vec<String>,
        payload_sig: Option<crate::lower::signature::SigType>,
    },
    Imported {
        type_params: Vec<yulang_typed_ir::TypeVar>,
        payload: Option<yulang_typed_ir::Type>,
    },
}

#[derive(Debug, Clone, Copy)]
pub struct ActiveRecursiveSelfInstance {
    pub tv: TypeVar,
    pub eff_tv: TypeVar,
}
