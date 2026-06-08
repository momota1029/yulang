use std::collections::{HashMap, HashSet};

use super::types::{
    MonoVarId, RecordField, RecordShape, RecordSpread, RowShape, TypeArena, TypeId, TypeKind,
    TypeVarKind, VariantCase, VariantShape,
};
use yulang_erased_ir::{
    EffectVar, RecordSpread as ErasedRecordSpread, Scheme, Type, TypeArg, TypeVar,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrincipalTypeInstance {
    pub body: TypeId,
    pub type_vars: HashMap<TypeVar, MonoVarId>,
    pub effect_vars: HashMap<EffectVar, MonoVarId>,
}

impl PrincipalTypeInstance {
    pub fn body_kind<'a>(&self, arena: &'a TypeArena) -> &'a TypeKind {
        arena.kind(self.body)
    }

    pub fn body_matches_kind(&self, arena: &TypeArena, expected: &TypeKind) -> bool {
        self.body_kind(arena) == expected
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PrincipalImportError {
    ConflictingQuantifiedVarName { name: String },
    FreeTypeVar(TypeVar),
    UnknownType,
    BoundsTypeArgInType,
    UnsupportedTypeForm(PrincipalTypeForm),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrincipalTypeForm {
    Union,
    Inter,
    Recursive,
}

pub struct PrincipalTypeInstantiator<'a> {
    arena: &'a mut TypeArena,
    type_vars: HashMap<TypeVar, MonoVarId>,
    effect_vars: HashMap<EffectVar, MonoVarId>,
    effect_var_names: HashMap<String, EffectVar>,
}

impl<'a> PrincipalTypeInstantiator<'a> {
    pub fn instantiate_scheme_body(
        arena: &'a mut TypeArena,
        scheme: &Scheme,
    ) -> Result<PrincipalTypeInstance, PrincipalImportError> {
        let mut instantiator = Self::new(arena, scheme)?;
        let body = instantiator.import_type(&scheme.body)?;
        Ok(PrincipalTypeInstance {
            body,
            type_vars: instantiator.type_vars,
            effect_vars: instantiator.effect_vars,
        })
    }

    fn new(arena: &'a mut TypeArena, scheme: &Scheme) -> Result<Self, PrincipalImportError> {
        let mut type_names = HashSet::new();
        let mut type_vars = HashMap::new();
        for var in &scheme.quantified_types {
            type_names.insert(var.0.clone());
            let (mono, _) = arena.fresh_var(TypeVarKind::Value);
            type_vars.insert(var.clone(), mono);
        }

        let mut effect_vars = HashMap::new();
        let mut effect_var_names = HashMap::new();
        for var in &scheme.quantified_effects {
            if type_names.contains(&var.0) {
                return Err(PrincipalImportError::ConflictingQuantifiedVarName {
                    name: var.0.clone(),
                });
            }
            let (mono, _) = arena.fresh_var(TypeVarKind::Effect);
            effect_vars.insert(var.clone(), mono);
            effect_var_names.insert(var.0.clone(), var.clone());
        }

        Ok(Self {
            arena,
            type_vars,
            effect_vars,
            effect_var_names,
        })
    }

    fn import_type(&mut self, ty: &Type) -> Result<TypeId, PrincipalImportError> {
        match ty {
            Type::Unknown => Err(PrincipalImportError::UnknownType),
            Type::Never => Ok(self.arena.never()),
            Type::Any => Ok(self.arena.any()),
            Type::Var(var) => self.import_var(var),
            Type::Named { path, args } => {
                let args = args
                    .iter()
                    .map(|arg| self.import_type_arg(arg))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.arena.named(path.clone(), args))
            }
            Type::Fun {
                param,
                param_effect,
                ret_effect,
                ret,
            } => {
                let param = self.import_type(param)?;
                let param_effect = self.import_type(param_effect)?;
                let ret_effect = self.import_type(ret_effect)?;
                let ret = self.import_type(ret)?;
                Ok(self.arena.fun(param, param_effect, ret_effect, ret))
            }
            Type::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|item| self.import_type(item))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.arena.tuple(items))
            }
            Type::Record(record) => {
                let fields = record
                    .fields
                    .iter()
                    .map(|field| {
                        Ok(RecordField {
                            name: field.name.clone(),
                            value: self.import_type(&field.value)?,
                            optional: field.optional,
                        })
                    })
                    .collect::<Result<Vec<_>, PrincipalImportError>>()?;
                let spread = record
                    .spread
                    .as_ref()
                    .map(|spread| self.import_record_spread(spread))
                    .transpose()?;
                Ok(self.arena.record(RecordShape { fields, spread }))
            }
            Type::Variant(variant) => {
                let cases = variant
                    .cases
                    .iter()
                    .map(|case| {
                        Ok(VariantCase {
                            name: case.name.clone(),
                            payloads: case
                                .payloads
                                .iter()
                                .map(|payload| self.import_type(payload))
                                .collect::<Result<Vec<_>, _>>()?,
                        })
                    })
                    .collect::<Result<Vec<_>, PrincipalImportError>>()?;
                let tail = variant
                    .tail
                    .as_ref()
                    .map(|tail| self.import_type(tail))
                    .transpose()?;
                Ok(self.arena.variant(VariantShape { cases, tail }))
            }
            Type::Row { items, tail } => {
                let items = items
                    .iter()
                    .map(|item| self.import_type(item))
                    .collect::<Result<Vec<_>, _>>()?;
                let tail = self.import_type(tail)?;
                Ok(self.arena.row(RowShape { items, tail }))
            }
            Type::Union(_) => Err(PrincipalImportError::UnsupportedTypeForm(
                PrincipalTypeForm::Union,
            )),
            Type::Inter(_) => Err(PrincipalImportError::UnsupportedTypeForm(
                PrincipalTypeForm::Inter,
            )),
            Type::Recursive { .. } => Err(PrincipalImportError::UnsupportedTypeForm(
                PrincipalTypeForm::Recursive,
            )),
        }
    }

    fn import_var(&self, var: &TypeVar) -> Result<TypeId, PrincipalImportError> {
        if let Some(mono) = self.type_vars.get(var) {
            return Ok(self.arena.var_type(*mono));
        }
        if let Some(effect_var) = self.effect_var_names.get(&var.0)
            && let Some(mono) = self.effect_vars.get(effect_var)
        {
            return Ok(self.arena.var_type(*mono));
        }
        Err(PrincipalImportError::FreeTypeVar(var.clone()))
    }

    fn import_type_arg(&mut self, arg: &TypeArg) -> Result<TypeId, PrincipalImportError> {
        match arg {
            TypeArg::Type(ty) => self.import_type(ty),
            TypeArg::Bounds(_) => Err(PrincipalImportError::BoundsTypeArgInType),
        }
    }

    fn import_record_spread(
        &mut self,
        spread: &ErasedRecordSpread,
    ) -> Result<RecordSpread, PrincipalImportError> {
        match spread {
            ErasedRecordSpread::Head(ty) => self.import_type(ty).map(RecordSpread::Head),
            ErasedRecordSpread::Tail(ty) => self.import_type(ty).map(RecordSpread::Tail),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use yulang_erased_ir::{Name, Path, RecordType, TypeBounds};

    fn path(name: &str) -> Path {
        Path::from_name(Name(name.to_string()))
    }

    fn var(name: &str) -> TypeVar {
        TypeVar(name.to_string())
    }

    fn effect_var(name: &str) -> EffectVar {
        EffectVar(name.to_string())
    }

    fn scheme(body: Type) -> Scheme {
        Scheme {
            body,
            quantified_types: Vec::new(),
            quantified_effects: Vec::new(),
            quantified_refs: Vec::new(),
            typeclass_obligations: Vec::new(),
            requirements: Vec::new(),
        }
    }

    #[test]
    fn instantiates_quantified_type_vars_to_fresh_mono_vars() {
        let mut scheme = scheme(Type::Fun {
            param: Box::new(Type::Var(var("a"))),
            param_effect: Box::new(Type::Never),
            ret_effect: Box::new(Type::Never),
            ret: Box::new(Type::Var(var("a"))),
        });
        scheme.quantified_types.push(var("a"));
        let mut arena = TypeArena::new();

        let instance =
            PrincipalTypeInstantiator::instantiate_scheme_body(&mut arena, &scheme).unwrap();

        let TypeKind::Fun { param, ret, .. } = arena.kind(instance.body) else {
            panic!("scheme body should import as a function");
        };
        assert_eq!(param, ret);
        let mono = instance.type_vars[&var("a")];
        assert_eq!(arena.kind(*param), &TypeKind::Var(mono));
        assert_eq!(arena.var_kind(mono), TypeVarKind::Value);
    }

    #[test]
    fn instantiates_quantified_effect_vars_to_effect_mono_vars() {
        let int = Type::Named {
            path: path("int"),
            args: Vec::new(),
        };
        let mut scheme = scheme(Type::Fun {
            param: Box::new(int.clone()),
            param_effect: Box::new(Type::Var(var("e"))),
            ret_effect: Box::new(Type::Var(var("e"))),
            ret: Box::new(int),
        });
        scheme.quantified_effects.push(effect_var("e"));
        let mut arena = TypeArena::new();

        let instance =
            PrincipalTypeInstantiator::instantiate_scheme_body(&mut arena, &scheme).unwrap();

        let TypeKind::Fun {
            param_effect,
            ret_effect,
            ..
        } = arena.kind(instance.body)
        else {
            panic!("scheme body should import as a function");
        };
        assert_eq!(param_effect, ret_effect);
        let mono = instance.effect_vars[&effect_var("e")];
        assert_eq!(arena.kind(*param_effect), &TypeKind::Var(mono));
        assert_eq!(arena.var_kind(mono), TypeVarKind::Effect);
    }

    #[test]
    fn rejects_bounds_type_args_inside_nominal_type() {
        let int = Type::Named {
            path: path("int"),
            args: Vec::new(),
        };
        let scheme = scheme(Type::Named {
            path: path("list"),
            args: vec![TypeArg::Bounds(TypeBounds::exact(int))],
        });
        let mut arena = TypeArena::new();

        let error = PrincipalTypeInstantiator::instantiate_scheme_body(&mut arena, &scheme)
            .expect_err("bounds in nominal type args should be rejected");

        assert_eq!(error, PrincipalImportError::BoundsTypeArgInType);
    }

    #[test]
    fn rejects_union_inside_principal_type_tree() {
        let scheme = scheme(Type::Union(vec![Type::Never, Type::Any]));
        let mut arena = TypeArena::new();

        let error = PrincipalTypeInstantiator::instantiate_scheme_body(&mut arena, &scheme)
            .expect_err("union should not be imported as a plain type tree");

        assert_eq!(
            error,
            PrincipalImportError::UnsupportedTypeForm(PrincipalTypeForm::Union)
        );
    }

    #[test]
    fn imports_records_with_plain_field_types() {
        let int = Type::Named {
            path: path("int"),
            args: Vec::new(),
        };
        let scheme = scheme(Type::Record(RecordType {
            fields: vec![yulang_erased_ir::RecordField {
                name: Name("value".to_string()),
                value: int,
                optional: false,
            }],
            spread: None,
        }));
        let mut arena = TypeArena::new();

        let instance =
            PrincipalTypeInstantiator::instantiate_scheme_body(&mut arena, &scheme).unwrap();
        let int = arena.named(path("int"), Vec::new());

        assert!(instance.body_matches_kind(
            &arena,
            &TypeKind::Record(RecordShape {
                fields: vec![RecordField {
                    name: Name("value".to_string()),
                    value: int,
                    optional: false,
                }],
                spread: None,
            })
        ));
        let TypeKind::Record(shape) = instance.body_kind(&arena) else {
            panic!("scheme body should import as a record");
        };
        assert_eq!(shape.fields.len(), 1);
        assert_eq!(shape.fields[0].name, Name("value".to_string()));
    }
}
