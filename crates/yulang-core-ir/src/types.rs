use crate::names::{Name, Path};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Scheme {
    pub requirements: Vec<RoleRequirement>,
    pub body: Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeSubstitution {
    pub var: TypeVar,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordType {
    pub fields: Vec<RecordField<Type>>,
    pub spread: Option<RecordSpread>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VariantType {
    pub cases: Vec<VariantCase>,
    pub tail: Option<Box<Type>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
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

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TypeVar(pub String);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RoleRequirement {
    pub role: Path,
    pub args: Vec<RoleRequirementArg>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RoleRequirementArg {
    Input(TypeBounds),
    Associated { name: Name, bounds: TypeBounds },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeArg {
    Type(Type),
    Bounds(TypeBounds),
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordField<T> {
    pub name: Name,
    pub value: T,
    pub optional: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RecordSpread {
    Head(Box<Type>),
    Tail(Box<Type>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VariantCase {
    pub name: Name,
    pub payloads: Vec<Type>,
}
