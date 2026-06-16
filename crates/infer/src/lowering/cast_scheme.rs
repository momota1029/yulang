//! Cast declaration signature lowering.
//!
//! Cast declarations need a standalone poly scheme because they are registered
//! in the cast table before ordinary expression bodies are solved.

use super::*;

pub(super) struct CastScheme {
    pub(super) source: Vec<String>,
    pub(super) target: Vec<String>,
    pub(super) scheme: Scheme,
}

struct CastSchemeBuilder<'a> {
    arena: &'a mut poly::expr::Arena,
    modules: &'a ModuleTable,
    vars: FxHashMap<AnnTypeVarId, TypeVar>,
    quantifiers: Vec<TypeVar>,
}

impl<'a> CastSchemeBuilder<'a> {
    fn new(arena: &'a mut poly::expr::Arena, modules: &'a ModuleTable) -> Self {
        Self {
            arena,
            modules,
            vars: FxHashMap::default(),
            quantifiers: Vec::new(),
        }
    }

    fn build(mut self, source: &AnnType, target: &AnnType) -> Result<CastScheme, LoweringError> {
        let source_path = self.constructor_path(source)?;
        let target_path = self.constructor_path(target)?;
        let arg = self.lower_neg(source)?;
        let arg_eff = self.arena.typ.alloc_neg(Neg::Bot);
        let ret_eff = self.arena.typ.alloc_pos(Pos::Bot);
        let ret = self.lower_pos(target)?;
        let predicate = self.arena.typ.alloc_pos(Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        });
        Ok(CastScheme {
            source: source_path,
            target: target_path,
            scheme: Scheme {
                quantifiers: self.quantifiers,
                role_predicates: Vec::new(),
                recursive_bounds: Vec::new(),
                stack_quantifiers: Vec::new(),
                predicate,
            },
        })
    }

    fn constructor_path(&self, ann: &AnnType) -> Result<Vec<String>, LoweringError> {
        match ann {
            AnnType::Builtin(builtin) => Ok(vec![builtin.surface_name().to_string()]),
            AnnType::Named(id) => self.type_decl_path(*id),
            AnnType::Apply { callee, .. } => self.constructor_path(callee),
            ty => Err(LoweringError::AnnotationConstraint {
                error: AnnConstraintError::InvalidConstructorCallee { ty: ty.clone() },
            }),
        }
    }

    fn lower_pos(&mut self, ann: &AnnType) -> Result<PosId, LoweringError> {
        match ann {
            AnnType::Builtin(BuiltinType::Never) => Ok(self.arena.typ.alloc_pos(Pos::Bot)),
            AnnType::Builtin(builtin) => Ok(self.arena.typ.alloc_pos(Pos::Con(
                vec![builtin.surface_name().to_string()],
                Vec::new(),
            ))),
            AnnType::Named(id) => {
                let path = self.type_decl_path(*id)?;
                Ok(self.arena.typ.alloc_pos(Pos::Con(path, Vec::new())))
            }
            AnnType::Apply { callee, args } => {
                let path = self.constructor_path(callee)?;
                let args = args
                    .iter()
                    .map(|arg| self.lower_neu(arg))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.arena.typ.alloc_pos(Pos::Con(path, args)))
            }
            AnnType::Var(var) | AnnType::Wildcard(var) => {
                let var = self.type_var(var.id);
                Ok(self.arena.typ.alloc_pos(Pos::Var(var)))
            }
            AnnType::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|item| self.lower_pos(item))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.arena.typ.alloc_pos(Pos::Tuple(items)))
            }
            ty => Err(LoweringError::AnnotationConstraint {
                error: AnnConstraintError::InvalidConstructorCallee { ty: ty.clone() },
            }),
        }
    }

    fn lower_neg(&mut self, ann: &AnnType) -> Result<NegId, LoweringError> {
        match ann {
            AnnType::Builtin(BuiltinType::Never) => Ok(self.arena.typ.alloc_neg(Neg::Bot)),
            AnnType::Builtin(builtin) => Ok(self.arena.typ.alloc_neg(Neg::Con(
                vec![builtin.surface_name().to_string()],
                Vec::new(),
            ))),
            AnnType::Named(id) => {
                let path = self.type_decl_path(*id)?;
                Ok(self.arena.typ.alloc_neg(Neg::Con(path, Vec::new())))
            }
            AnnType::Apply { callee, args } => {
                let path = self.constructor_path(callee)?;
                let args = args
                    .iter()
                    .map(|arg| self.lower_neu(arg))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.arena.typ.alloc_neg(Neg::Con(path, args)))
            }
            AnnType::Var(var) | AnnType::Wildcard(var) => {
                let var = self.type_var(var.id);
                Ok(self.arena.typ.alloc_neg(Neg::Var(var)))
            }
            AnnType::Tuple(items) => {
                let items = items
                    .iter()
                    .map(|item| self.lower_neg(item))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.arena.typ.alloc_neg(Neg::Tuple(items)))
            }
            ty => Err(LoweringError::AnnotationConstraint {
                error: AnnConstraintError::InvalidConstructorCallee { ty: ty.clone() },
            }),
        }
    }

    fn lower_neu(&mut self, ann: &AnnType) -> Result<NeuId, LoweringError> {
        let lower = self.lower_pos(ann)?;
        let upper = self.lower_neg(ann)?;
        Ok(self.arena.typ.alloc_neu(Neu::Bounds(lower, upper)))
    }

    fn type_var(&mut self, id: AnnTypeVarId) -> TypeVar {
        if let Some(var) = self.vars.get(&id) {
            return *var;
        }
        let var = self.arena.fresh_type_var();
        self.vars.insert(id, var);
        self.quantifiers.push(var);
        var
    }

    fn type_decl_path(&self, id: TypeDeclId) -> Result<Vec<String>, LoweringError> {
        let decl = self
            .modules
            .type_decl_by_id(id)
            .ok_or(LoweringError::AnnotationConstraint {
                error: AnnConstraintError::MissingTypeDecl { id },
            })?;
        Ok(self
            .modules
            .type_decl_path(&decl)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect())
    }
}

pub(super) fn build_cast_scheme_from_ann(
    arena: &mut poly::expr::Arena,
    modules: &ModuleTable,
    source: &AnnType,
    target: &AnnType,
) -> Result<CastScheme, LoweringError> {
    CastSchemeBuilder::new(arena, modules).build(source, target)
}
