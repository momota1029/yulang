use std::collections::HashMap;

use yulang_erased_ir::{Name, Path};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeId(u32);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct MonoVarId(u32);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeKind {
    Never,
    Any,
    Var(MonoVarId),
    Named {
        path: Path,
        args: Vec<TypeId>,
    },
    Fun {
        param: TypeId,
        param_effect: TypeId,
        ret_effect: TypeId,
        ret: TypeId,
    },
    EffectiveThunk {
        effect: TypeId,
        value: TypeId,
    },
    Tuple(Vec<TypeId>),
    Record(RecordShape),
    Variant(VariantShape),
    Row(RowShape),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RecordShape {
    pub fields: Vec<RecordField>,
    pub spread: Option<RecordSpread>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RecordField {
    pub name: Name,
    pub value: TypeId,
    pub optional: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RecordSpread {
    Head(TypeId),
    Tail(TypeId),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VariantShape {
    pub cases: Vec<VariantCase>,
    pub tail: Option<TypeId>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VariantCase {
    pub name: Name,
    pub payloads: Vec<TypeId>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct RowShape {
    pub items: Vec<TypeId>,
    pub tail: TypeId,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeVarKind {
    Value,
    Effect,
}

#[derive(Debug, Default)]
pub struct TypeArena {
    kinds: Vec<TypeKind>,
    interned: HashMap<TypeKind, TypeId>,
    var_kinds: Vec<TypeVarKind>,
    var_types: Vec<TypeId>,
}

impl TypeArena {
    pub fn new() -> Self {
        let mut arena = Self::default();
        arena.intern(TypeKind::Never);
        arena.intern(TypeKind::Any);
        arena
    }

    pub fn never(&self) -> TypeId {
        TypeId(0)
    }

    pub fn any(&self) -> TypeId {
        TypeId(1)
    }

    pub fn fresh_var(&mut self, kind: TypeVarKind) -> (MonoVarId, TypeId) {
        let var = MonoVarId(self.var_kinds.len() as u32);
        self.var_kinds.push(kind);
        let ty = self.intern(TypeKind::Var(var));
        self.var_types.push(ty);
        (var, ty)
    }

    pub fn named(&mut self, path: Path, args: Vec<TypeId>) -> TypeId {
        self.intern(TypeKind::Named { path, args })
    }

    pub fn fun(
        &mut self,
        param: TypeId,
        param_effect: TypeId,
        ret_effect: TypeId,
        ret: TypeId,
    ) -> TypeId {
        self.intern(TypeKind::Fun {
            param,
            param_effect,
            ret_effect,
            ret,
        })
    }

    pub fn effective_thunk(&mut self, effect: TypeId, value: TypeId) -> TypeId {
        self.intern(TypeKind::EffectiveThunk { effect, value })
    }

    pub fn tuple(&mut self, items: Vec<TypeId>) -> TypeId {
        self.intern(TypeKind::Tuple(items))
    }

    pub fn record(&mut self, shape: RecordShape) -> TypeId {
        self.intern(TypeKind::Record(shape))
    }

    pub fn variant(&mut self, shape: VariantShape) -> TypeId {
        self.intern(TypeKind::Variant(shape))
    }

    pub fn row(&mut self, shape: RowShape) -> TypeId {
        self.intern(TypeKind::Row(shape))
    }

    pub fn kind(&self, id: TypeId) -> &TypeKind {
        &self.kinds[id.0 as usize]
    }

    pub fn var_kind(&self, id: MonoVarId) -> TypeVarKind {
        self.var_kinds[id.0 as usize]
    }

    pub fn var_type(&self, id: MonoVarId) -> TypeId {
        self.var_types[id.0 as usize]
    }

    fn intern(&mut self, kind: TypeKind) -> TypeId {
        if let Some(id) = self.interned.get(&kind) {
            return *id;
        }
        let id = TypeId(self.kinds.len() as u32);
        self.kinds.push(kind.clone());
        self.interned.insert(kind, id);
        id
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn path(name: &str) -> Path {
        Path::from_name(Name(name.to_string()))
    }

    #[test]
    fn nominal_type_arguments_are_plain_type_ids() {
        let mut arena = TypeArena::new();
        let int = arena.named(path("int"), Vec::new());

        let first = arena.named(path("list"), vec![int]);
        let second = arena.named(path("list"), vec![int]);

        assert_eq!(first, second);
        assert_eq!(
            arena.kind(first),
            &TypeKind::Named {
                path: path("list"),
                args: vec![int],
            }
        );
    }
}
