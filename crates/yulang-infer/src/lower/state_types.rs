use crate::diagnostic::TypeOrigin;
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
    pub file_span: Option<crate::lower::state::FileSpan>,
    pub arms: Vec<CaseArmCheckSite>,
}

#[derive(Debug, Clone)]
pub struct CaseArmCheckSite {
    pub span: rowan::TextRange,
    pub file_span: Option<crate::lower::state::FileSpan>,
    pub guarded: bool,
    pub patterns: Vec<CaseArmPattern>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CaseArmPattern {
    EnumVariant {
        enum_path: Path,
        variant: Name,
        payload_covers_all: bool,
    },
    CoversAll,
}

#[derive(Debug, Clone)]
pub struct CatchCheckSite {
    pub span: rowan::TextRange,
    pub file_span: Option<crate::lower::state::FileSpan>,
    pub body_tv: TypeVar,
    pub body_eff_tv: TypeVar,
    pub result_tv: TypeVar,
    pub result_eff_tv: TypeVar,
    pub arms: Vec<CatchArmCheckSite>,
}

#[derive(Debug, Clone)]
pub struct CatchArmCheckSite {
    pub span: rowan::TextRange,
    pub file_span: Option<crate::lower::state::FileSpan>,
    pub guard_span: Option<rowan::TextRange>,
    pub guard_file_span: Option<crate::lower::state::FileSpan>,
    pub active: bool,
    pub kind: CatchArmCheckKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CatchArmCheckKind {
    Value {
        pattern_span: Option<rowan::TextRange>,
        pattern_file_span: Option<crate::lower::state::FileSpan>,
        pattern_covers_all: bool,
    },
    Effect {
        op_path: Path,
        effect_path: Option<Path>,
        payload_covers_all: bool,
        effect_pattern_span: Option<rowan::TextRange>,
        effect_pattern_file_span: Option<crate::lower::state::FileSpan>,
        continuation_span: Option<rowan::TextRange>,
        continuation_file_span: Option<crate::lower::state::FileSpan>,
    },
}

#[derive(Debug, Clone)]
pub struct RoleImplMemberCheckSite {
    pub span: rowan::TextRange,
    pub origins: Vec<TypeOrigin>,
}

#[derive(Debug, Clone, Copy)]
pub struct ActiveRecursiveSelfInstance {
    pub tv: TypeVar,
    pub eff_tv: TypeVar,
}
