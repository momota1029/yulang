//! Builtin operator lowering and signature constraints.
//!
//! Builtin operators are resolved by symbol metadata before this module runs.
//! This file only turns the structured builtin signature into the same subtype
//! constraints used by ordinary values.

use super::*;

enum BuiltinOpTypePath {
    Builtin(BuiltinType),
    Named(Vec<String>),
}

impl<'a> ExprLowerer<'a> {
    /// Lower a resolved builtin operator reference into a primitive expression.
    pub(super) fn lower_builtin_op(
        &mut self,
        builtin: BuiltinOp,
    ) -> Result<Computation, LoweringError> {
        let value = self.fresh_type_var();
        let effect = self.fresh_exact_pure_effect();
        self.constrain_builtin_op_sig(value, builtin.sig)?;
        let expr = self.session.poly.add_expr(Expr::PrimitiveOp(builtin.op));
        Ok(Computation::value(expr, value, effect))
    }

    fn constrain_builtin_op_sig(
        &mut self,
        value: TypeVar,
        sig: BuiltinOpSig,
    ) -> Result<(), LoweringError> {
        if let BuiltinOpSig::Poly { params, ret } = sig {
            return self.constrain_poly_op_sig(value, params, ret);
        }
        let lower = self.builtin_op_pos_sig(sig)?;
        let upper = self.builtin_op_neg_sig(sig)?;
        self.constrain_lower(value, lower);
        self.constrain_upper(value, upper);
        Ok(())
    }

    fn constrain_poly_op_sig(
        &mut self,
        value: TypeVar,
        params: &[SigTy],
        ret: SigTy,
    ) -> Result<(), LoweringError> {
        let mut vars = FxHashMap::default();
        let lower = self.curried_poly_pos(&mut vars, params, ret)?;
        let upper = self.curried_poly_neg(&mut vars, params, ret)?;
        self.constrain_lower(value, lower);
        self.constrain_upper(value, upper);
        Ok(())
    }

    fn poly_sig_var(&mut self, vars: &mut FxHashMap<u8, TypeVar>, index: u8) -> TypeVar {
        if let Some(var) = vars.get(&index) {
            return *var;
        }
        let var = self.fresh_type_var();
        vars.insert(index, var);
        var
    }

    fn curried_poly_pos(
        &mut self,
        vars: &mut FxHashMap<u8, TypeVar>,
        params: &[SigTy],
        ret: SigTy,
    ) -> Result<Pos, LoweringError> {
        let Some((param, rest)) = params.split_first() else {
            return self.poly_sig_pos(ret, vars);
        };
        let arg = self.poly_sig_neg(*param, vars)?;
        let arg = self.alloc_neg(arg);
        let arg_eff = self.never_neg();
        let ret_eff = self.alloc_pos(Pos::Bot);
        let ret = self.curried_poly_pos(vars, rest, ret)?;
        let ret = self.alloc_pos(ret);
        Ok(Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        })
    }

    fn curried_poly_neg(
        &mut self,
        vars: &mut FxHashMap<u8, TypeVar>,
        params: &[SigTy],
        ret: SigTy,
    ) -> Result<Neg, LoweringError> {
        let Some((param, rest)) = params.split_first() else {
            return self.poly_sig_neg(ret, vars);
        };
        let arg = self.poly_sig_pos(*param, vars)?;
        let arg = self.alloc_pos(arg);
        let arg_eff = self.alloc_pos(Pos::Bot);
        let ret_eff = self.never_neg();
        let ret = self.curried_poly_neg(vars, rest, ret)?;
        let ret = self.alloc_neg(ret);
        Ok(Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        })
    }

    fn poly_sig_pos(
        &mut self,
        ty: SigTy,
        vars: &mut FxHashMap<u8, TypeVar>,
    ) -> Result<Pos, LoweringError> {
        match ty {
            SigTy::Var(index) => Ok(Pos::Var(self.poly_sig_var(vars, index))),
            SigTy::Con(name, []) => self.builtin_op_pos_type(name),
            SigTy::Con(name, args) => {
                let path = self.builtin_op_con_path(name)?;
                let args = args
                    .iter()
                    .map(|arg| self.poly_sig_neu(*arg, vars))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Pos::Con(path, args))
            }
        }
    }

    fn poly_sig_neg(
        &mut self,
        ty: SigTy,
        vars: &mut FxHashMap<u8, TypeVar>,
    ) -> Result<Neg, LoweringError> {
        match ty {
            SigTy::Var(index) => Ok(Neg::Var(self.poly_sig_var(vars, index))),
            SigTy::Con(name, []) => self.builtin_op_neg_type(name),
            SigTy::Con(name, args) => {
                let path = self.builtin_op_con_path(name)?;
                let args = args
                    .iter()
                    .map(|arg| self.poly_sig_neu(*arg, vars))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Neg::Con(path, args))
            }
        }
    }

    fn poly_sig_neu(
        &mut self,
        ty: SigTy,
        vars: &mut FxHashMap<u8, TypeVar>,
    ) -> Result<poly::types::NeuId, LoweringError> {
        match ty {
            SigTy::Var(index) => {
                let var = self.poly_sig_var(vars, index);
                Ok(self.invariant_var_arg(var))
            }
            SigTy::Con(name, args) => {
                let path = self.builtin_op_con_path(name)?;
                let args = args
                    .iter()
                    .map(|arg| self.poly_sig_neu(*arg, vars))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(self.session.infer.alloc_neu(Neu::Con(path, args)))
            }
        }
    }

    fn builtin_op_pos_sig(&mut self, sig: BuiltinOpSig) -> Result<Pos, LoweringError> {
        match sig {
            BuiltinOpSig::Nullary { ret } => self.builtin_op_pos_type(ret),
            BuiltinOpSig::Unary { param, ret } => self.curried_pos_fun(&[param], ret),
            BuiltinOpSig::Binary { param, ret } => self.curried_pos_fun(&[param, param], ret),
            BuiltinOpSig::BinaryPredicate { param } => {
                self.curried_pos_fun(&[param, param], "bool")
            }
            BuiltinOpSig::Mixed { params, ret } => self.curried_pos_fun(params, ret),
            BuiltinOpSig::BytesToUtf8Raw => {
                let ret = Pos::Tuple(vec![
                    self.alloc_pos(self.builtin_op_pos_type("str")?),
                    self.alloc_pos(self.builtin_op_pos_type("int")?),
                ]);
                self.curried_pos_fun_with_ret(&["bytes"], ret)
            }
            BuiltinOpSig::Poly { .. } => unreachable!("poly sigs are constrained directly"),
        }
    }

    fn builtin_op_neg_sig(&mut self, sig: BuiltinOpSig) -> Result<Neg, LoweringError> {
        match sig {
            BuiltinOpSig::Nullary { ret } => self.builtin_op_neg_type(ret),
            BuiltinOpSig::Unary { param, ret } => self.curried_neg_fun(&[param], ret),
            BuiltinOpSig::Binary { param, ret } => self.curried_neg_fun(&[param, param], ret),
            BuiltinOpSig::BinaryPredicate { param } => {
                self.curried_neg_fun(&[param, param], "bool")
            }
            BuiltinOpSig::Mixed { params, ret } => self.curried_neg_fun(params, ret),
            BuiltinOpSig::BytesToUtf8Raw => {
                let ret = Neg::Tuple(vec![
                    self.alloc_neg(self.builtin_op_neg_type("str")?),
                    self.alloc_neg(self.builtin_op_neg_type("int")?),
                ]);
                self.curried_neg_fun_with_ret(&["bytes"], ret)
            }
            BuiltinOpSig::Poly { .. } => unreachable!("poly sigs are constrained directly"),
        }
    }

    fn curried_pos_fun(
        &mut self,
        params: &[&'static str],
        ret: &'static str,
    ) -> Result<Pos, LoweringError> {
        let ret = self.builtin_op_pos_type(ret)?;
        self.curried_pos_fun_with_ret(params, ret)
    }

    fn curried_pos_fun_with_ret(
        &mut self,
        params: &[&'static str],
        ret: Pos,
    ) -> Result<Pos, LoweringError> {
        let Some((param, rest)) = params.split_first() else {
            return Ok(ret);
        };
        let arg = self.builtin_op_neg_type(param)?;
        let arg = self.alloc_neg(arg);
        let arg_eff = self.never_neg();
        let ret_eff = self.alloc_pos(Pos::Bot);
        let ret = self.curried_pos_fun_with_ret(rest, ret)?;
        let ret = self.alloc_pos(ret);
        Ok(Pos::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        })
    }

    fn curried_neg_fun(
        &mut self,
        params: &[&'static str],
        ret: &'static str,
    ) -> Result<Neg, LoweringError> {
        let ret = self.builtin_op_neg_type(ret)?;
        self.curried_neg_fun_with_ret(params, ret)
    }

    fn curried_neg_fun_with_ret(
        &mut self,
        params: &[&'static str],
        ret: Neg,
    ) -> Result<Neg, LoweringError> {
        let Some((param, rest)) = params.split_first() else {
            return Ok(ret);
        };
        let arg = self.builtin_op_pos_type(param)?;
        let arg = self.alloc_pos(arg);
        let arg_eff = self.alloc_pos(Pos::Bot);
        let ret_eff = self.never_neg();
        let ret = self.curried_neg_fun_with_ret(rest, ret)?;
        let ret = self.alloc_neg(ret);
        Ok(Neg::Fun {
            arg,
            arg_eff,
            ret_eff,
            ret,
        })
    }

    fn builtin_op_pos_type(&self, name: &'static str) -> Result<Pos, LoweringError> {
        let path = self.builtin_op_type_path(name)?;
        Ok(match path {
            BuiltinOpTypePath::Builtin(BuiltinType::Never) => Pos::Bot,
            BuiltinOpTypePath::Builtin(builtin) => {
                Pos::Con(vec![builtin.surface_name().to_string()], Vec::new())
            }
            BuiltinOpTypePath::Named(path) => Pos::Con(path, Vec::new()),
        })
    }

    fn builtin_op_neg_type(&self, name: &'static str) -> Result<Neg, LoweringError> {
        let path = self.builtin_op_type_path(name)?;
        Ok(match path {
            BuiltinOpTypePath::Builtin(BuiltinType::Never) => Neg::Bot,
            BuiltinOpTypePath::Builtin(builtin) => {
                Neg::Con(vec![builtin.surface_name().to_string()], Vec::new())
            }
            BuiltinOpTypePath::Named(path) => Neg::Con(path, Vec::new()),
        })
    }

    /// Resolve a surface type name into the constructor path used by type constraints.
    pub(super) fn builtin_op_con_path(
        &self,
        name: &'static str,
    ) -> Result<Vec<String>, LoweringError> {
        Ok(match self.builtin_op_type_path(name)? {
            BuiltinOpTypePath::Builtin(builtin) => vec![builtin.surface_name().to_string()],
            BuiltinOpTypePath::Named(path) => path,
        })
    }

    fn builtin_op_type_path(&self, name: &'static str) -> Result<BuiltinOpTypePath, LoweringError> {
        if let Some(builtin) = BuiltinType::from_surface_name(name) {
            return Ok(BuiltinOpTypePath::Builtin(builtin));
        }
        let name = Name(name.to_string());
        let Some(decl) = self.modules.lexical_type_at(self.module, &name, self.site) else {
            return Err(LoweringError::AnnotationBuild {
                error: AnnBuildError::UnresolvedTypeName { path: vec![name] },
            });
        };
        Ok(BuiltinOpTypePath::Named(
            self.modules
                .type_decl_path(&decl)
                .segments
                .into_iter()
                .map(|name| name.0)
                .collect(),
        ))
    }
}
