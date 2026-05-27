use crate::ids::{NegId, PosId, TypeVar};
use crate::symbols::{Name, Path};

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

#[derive(Debug, Clone)]
pub struct CaseCheckSite {
    pub span: rowan::TextRange,
    pub arms: Vec<CaseArmCheckSite>,
}

#[derive(Debug, Clone)]
pub struct CaseArmCheckSite {
    pub span: rowan::TextRange,
    pub guarded: bool,
    pub patterns: Vec<CaseArmPattern>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CaseArmPattern {
    EnumVariant { enum_path: Path, variant: Name },
    CoversAll,
}

#[derive(Debug, Clone, Copy)]
pub struct ActiveRecursiveSelfInstance {
    pub tv: TypeVar,
    pub eff_tv: TypeVar,
}
