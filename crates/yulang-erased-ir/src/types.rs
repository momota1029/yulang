use serde::{Deserialize, Serialize};

use crate::{Name, Path, RefId, TypeClassObligation};

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Scheme {
    pub body: Type,
    pub quantified_types: Vec<TypeVar>,
    pub quantified_effects: Vec<EffectVar>,
    pub quantified_refs: Vec<RefId>,
    pub typeclass_obligations: Vec<TypeClassObligation>,
    pub requirements: Vec<RoleRequirement>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TypeSubstitution {
    pub var: TypeVar,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RecordType {
    pub fields: Vec<RecordField<Type>>,
    pub spread: Option<RecordSpread>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct VariantType {
    pub cases: Vec<VariantCase>,
    pub tail: Option<Box<Type>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Type {
    Unknown,
    Never,
    Any,
    Var(TypeVar),
    Named {
        path: Path,
        args: Vec<TypeArg>,
    },
    Fun {
        param: Box<Type>,
        param_effect: Box<Type>,
        ret_effect: Box<Type>,
        ret: Box<Type>,
    },
    Tuple(Vec<Type>),
    Record(RecordType),
    Variant(VariantType),
    Row {
        items: Vec<Type>,
        tail: Box<Type>,
    },
    Union(Vec<Type>),
    Inter(Vec<Type>),
    Recursive {
        var: TypeVar,
        body: Box<Type>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct TypeVar(pub String);

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct EffectVar(pub String);

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RoleRequirement {
    pub role: Path,
    pub args: Vec<RoleRequirementArg>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum RoleRequirementArg {
    Input(TypeBounds),
    Associated { name: Name, bounds: TypeBounds },
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TypeArg {
    Type(Type),
    Bounds(TypeBounds),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default, Serialize, Deserialize)]
pub struct TypeBounds {
    pub lower: Option<Box<Type>>,
    pub upper: Option<Box<Type>>,
}

impl TypeBounds {
    pub fn exact(ty: Type) -> Self {
        Self {
            lower: Some(Box::new(ty.clone())),
            upper: Some(Box::new(ty)),
        }
    }

    pub fn lower(ty: Type) -> Self {
        Self {
            lower: Some(Box::new(ty)),
            upper: None,
        }
    }

    pub fn upper(ty: Type) -> Self {
        Self {
            lower: None,
            upper: Some(Box::new(ty)),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct RecordField<T> {
    pub name: Name,
    pub value: T,
    pub optional: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum RecordSpread {
    Head(Box<Type>),
    Tail(Box<Type>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct VariantCase {
    pub name: Name,
    pub payloads: Vec<Type>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum PrimitiveOp {
    YadaYada,
    BoolNot,
    BoolEq,
    ListEmpty,
    ListSingleton,
    ListLen,
    ListMerge,
    ListIndex,
    ListIndexRange,
    ListSplice,
    ListIndexRangeRaw,
    ListSpliceRaw,
    ListViewRaw,
    StringLen,
    StringIndex,
    StringIndexRange,
    StringSplice,
    StringIndexRangeRaw,
    StringSpliceRaw,
    StringLineCount,
    StringLineRange,
    IntAdd,
    IntSub,
    IntMul,
    IntDiv,
    IntMod,
    IntEq,
    IntLt,
    IntLe,
    IntGt,
    IntGe,
    FloatAdd,
    FloatSub,
    FloatMul,
    FloatDiv,
    FloatEq,
    FloatLt,
    FloatLe,
    FloatGt,
    FloatGe,
    StringEq,
    StringConcat,
    StringToBytes,
    CharEq,
    CharToString,
    CharIsWhitespace,
    CharIsPunctuation,
    CharIsWord,
    BytesLen,
    BytesEq,
    BytesConcat,
    BytesIndex,
    BytesIndexRange,
    BytesToUtf8Raw,
    BytesToPath,
    PathToBytes,
    IntToString,
    IntToHex,
    IntToUpperHex,
    FloatToString,
    BoolToString,
}
