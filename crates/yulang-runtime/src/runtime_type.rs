use serde::{Deserialize, Serialize};
use yulang_typed_ir as typed_ir;

#[derive(Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Type {
    Unknown,
    Core(typed_ir::Type),
    Fun {
        param: Box<Type>,
        ret: Box<Type>,
    },
    Thunk {
        effect: typed_ir::Type,
        value: Box<Type>,
    },
}

impl Type {
    pub fn unknown() -> Self {
        Self::Unknown
    }

    pub fn core(ty: typed_ir::Type) -> Self {
        Self::Core(ty)
    }

    pub fn fun(param: Type, ret: Type) -> Self {
        Self::Fun {
            param: Box::new(param),
            ret: Box::new(ret),
        }
    }

    pub fn thunk(effect: typed_ir::Type, value: Type) -> Self {
        Self::Thunk {
            effect,
            value: Box::new(value),
        }
    }

    pub fn as_core(&self) -> Option<&typed_ir::Type> {
        match self {
            Type::Core(ty) => Some(ty),
            Type::Unknown | Type::Fun { .. } | Type::Thunk { .. } => None,
        }
    }
}

impl Clone for Type {
    fn clone(&self) -> Self {
        clone_type_without_fun_spine_recursion(self)
    }
}

fn clone_type_without_fun_spine_recursion(ty: &Type) -> Type {
    enum Frame<'a> {
        Fun { param: &'a Type },
        Thunk { effect: &'a typed_ir::Type },
    }

    let mut current = ty;
    let mut frames = Vec::new();
    loop {
        match current {
            Type::Fun { param, ret } => {
                frames.push(Frame::Fun { param });
                current = ret;
            }
            Type::Thunk { effect, value } => {
                frames.push(Frame::Thunk { effect });
                current = value;
            }
            Type::Unknown => {
                let mut cloned = Type::Unknown;
                for frame in frames.into_iter().rev() {
                    cloned = match frame {
                        Frame::Fun { param } => Type::fun(param.clone(), cloned),
                        Frame::Thunk { effect } => Type::thunk(effect.clone(), cloned),
                    };
                }
                return cloned;
            }
            Type::Core(core) => {
                let mut cloned = Type::Core(core.clone());
                for frame in frames.into_iter().rev() {
                    cloned = match frame {
                        Frame::Fun { param } => Type::fun(param.clone(), cloned),
                        Frame::Thunk { effect } => Type::thunk(effect.clone(), cloned),
                    };
                }
                return cloned;
            }
        }
    }
}

impl From<typed_ir::Type> for Type {
    fn from(ty: typed_ir::Type) -> Self {
        Type::Core(ty)
    }
}
