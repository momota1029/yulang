//! VM-ready validation for lowered control IR.

use std::fmt;

use mono::Type;

use crate::boundary::{function_boundary_supported, value_boundary_supported};
use crate::ir::{
    Block, DefId, Expr, ExprId, InstanceId, Pat, Program, RecordSpread, Root, SelectResolution,
    Stmt,
};

pub fn validate(program: &Program) -> Result<(), ValidateError> {
    Validator { program }.validate_program()
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValidateError {
    MissingExpr {
        expr: ExprId,
    },
    MissingInstance {
        instance: InstanceId,
    },
    MismatchedInstanceSlot {
        expected: InstanceId,
        actual: InstanceId,
    },
    UnsupportedExpr {
        expr: ExprId,
        feature: String,
    },
    UnsupportedPattern {
        feature: String,
    },
    UnsupportedBoundary {
        feature: String,
    },
    NonVmReadyType {
        feature: String,
        ty: Type,
    },
    UnresolvedSelect {
        expr: ExprId,
        name: String,
    },
    UnresolvedTypeclassMethod {
        expr: ExprId,
        member: DefId,
    },
}

impl fmt::Display for ValidateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingExpr { expr } => write!(f, "missing control expression e{}", expr.0),
            Self::MissingInstance { instance } => write!(f, "missing instance m{}", instance.0),
            Self::MismatchedInstanceSlot { expected, actual } => write!(
                f,
                "mismatched instance slot while validating: expected m{}, found m{}",
                expected.0, actual.0
            ),
            Self::UnsupportedExpr { expr, feature } => {
                write!(f, "unsupported VM expression at e{}: {feature}", expr.0)
            }
            Self::UnsupportedPattern { feature } => {
                write!(f, "unsupported VM pattern: {feature}")
            }
            Self::UnsupportedBoundary { feature } => {
                write!(f, "unsupported VM boundary: {feature}")
            }
            Self::NonVmReadyType { feature, ty } => write!(
                f,
                "non VM-ready type {}: {}",
                mono::dump::dump_type(ty),
                feature
            ),
            Self::UnresolvedSelect { expr, name } => {
                write!(f, "unresolved select at e{}: .{name}", expr.0)
            }
            Self::UnresolvedTypeclassMethod { expr, member } => write!(
                f,
                "unresolved typeclass method at e{}: d{}",
                expr.0, member.0
            ),
        }
    }
}

impl std::error::Error for ValidateError {}

struct Validator<'a> {
    program: &'a Program,
}

impl Validator<'_> {
    fn validate_program(&self) -> Result<(), ValidateError> {
        for root in &self.program.roots {
            match root {
                Root::Instance(instance) => self.validate_instance_ref(*instance)?,
                Root::Expr(expr) => self.validate_expr_ref(*expr)?,
            }
        }
        for (index, instance) in self.program.instances.iter().enumerate() {
            let expected = InstanceId(index as u32);
            if instance.id != expected {
                return Err(ValidateError::MismatchedInstanceSlot {
                    expected,
                    actual: instance.id,
                });
            }
            validate_type(&instance.signature.ty)?;
            self.validate_expr_ref(instance.entry)?;
        }
        for (index, expr) in self.program.exprs.iter().enumerate() {
            self.validate_expr(ExprId(index as u32), expr)?;
        }
        Ok(())
    }

    fn validate_expr_ref(&self, expr: ExprId) -> Result<(), ValidateError> {
        self.program
            .exprs
            .get(expr.0 as usize)
            .map(|_| ())
            .ok_or(ValidateError::MissingExpr { expr })
    }

    fn validate_instance_ref(&self, instance: InstanceId) -> Result<(), ValidateError> {
        let actual = self
            .program
            .instances
            .get(instance.0 as usize)
            .map(|instance| instance.id)
            .ok_or(ValidateError::MissingInstance { instance })?;
        if actual != instance {
            return Err(ValidateError::MismatchedInstanceSlot {
                expected: instance,
                actual,
            });
        }
        Ok(())
    }

    fn validate_expr(&self, id: ExprId, expr: &Expr) -> Result<(), ValidateError> {
        match expr {
            Expr::Lit(_)
            | Expr::PrimitiveOp { .. }
            | Expr::Constructor { .. }
            | Expr::EffectOp { .. }
            | Expr::Local(_) => Ok(()),
            Expr::InstanceRef(instance) => self.validate_instance_ref(*instance),
            Expr::Coerce {
                source,
                target,
                expr,
            } => {
                self.validate_expr_ref(*expr)?;
                validate_type(source)?;
                validate_type(target)?;
                if !value_boundary_supported(source, target) {
                    return Err(ValidateError::UnsupportedBoundary {
                        feature: format!(
                            "coerce {} => {}",
                            mono::dump::dump_type(source),
                            mono::dump::dump_type(target)
                        ),
                    });
                }
                Ok(())
            }
            Expr::MakeThunk {
                source,
                target,
                body,
            } => {
                validate_type(&source.effect)?;
                validate_type(&source.value)?;
                validate_type(&target.effect)?;
                validate_type(&target.value)?;
                self.validate_expr_ref(*body)
            }
            Expr::ForceThunk {
                source,
                target,
                thunk,
            } => {
                validate_type(&source.effect)?;
                validate_type(&source.value)?;
                validate_type(&target.effect)?;
                validate_type(&target.value)?;
                self.validate_expr_ref(*thunk)
            }
            Expr::FunctionAdapter {
                source,
                target,
                function,
                ..
            } => {
                self.validate_expr_ref(*function)?;
                validate_type(source)?;
                validate_type(target)?;
                if !function_boundary_supported(source, target) {
                    return Err(ValidateError::UnsupportedBoundary {
                        feature: format!(
                            "function adapter {} => {}",
                            mono::dump::dump_type(source),
                            mono::dump::dump_type(target)
                        ),
                    });
                }
                Ok(())
            }
            Expr::MarkerFrame { body, .. } => self.validate_expr_ref(*body),
            Expr::Apply { callee, arg } => {
                self.validate_expr_ref(*callee)?;
                self.validate_expr_ref(*arg)
            }
            Expr::RefSet { .. } => Err(ValidateError::UnsupportedExpr {
                expr: id,
                feature: "ref set".to_string(),
            }),
            Expr::Lambda { param, body } => {
                self.validate_pat(param)?;
                self.validate_expr_ref(*body)
            }
            Expr::Tuple(items) => self.validate_expr_refs(items),
            Expr::Record { fields, spread } => {
                for field in fields {
                    self.validate_expr_ref(field.value)?;
                }
                self.validate_expr_spread(spread)
            }
            Expr::PolyVariant { payloads, .. } => self.validate_expr_refs(payloads),
            Expr::Select {
                base,
                name,
                resolution,
            } => {
                self.validate_expr_ref(*base)?;
                match resolution {
                    Some(SelectResolution::RecordField) => Ok(()),
                    Some(SelectResolution::Method { instance }) => {
                        self.validate_instance_ref(*instance)
                    }
                    Some(SelectResolution::TypeclassMethod { member }) => {
                        Err(ValidateError::UnresolvedTypeclassMethod {
                            expr: id,
                            member: *member,
                        })
                    }
                    None => Err(ValidateError::UnresolvedSelect {
                        expr: id,
                        name: name.clone(),
                    }),
                }
            }
            Expr::Case { scrutinee, arms } => {
                self.validate_expr_ref(*scrutinee)?;
                for arm in arms {
                    self.validate_pat(&arm.pat)?;
                    if let Some(guard) = arm.guard {
                        self.validate_expr_ref(guard)?;
                    }
                    self.validate_expr_ref(arm.body)?;
                }
                Ok(())
            }
            Expr::Catch { body, arms } => {
                self.validate_expr_ref(*body)?;
                for arm in arms {
                    self.validate_pat(&arm.pat)?;
                    if let Some(continuation) = &arm.continuation {
                        self.validate_pat(continuation)?;
                    }
                    if let Some(guard) = arm.guard {
                        self.validate_expr_ref(guard)?;
                    }
                    self.validate_expr_ref(arm.body)?;
                }
                Ok(())
            }
            Expr::Block(block) => self.validate_block(block),
        }
    }

    fn validate_expr_refs(&self, exprs: &[ExprId]) -> Result<(), ValidateError> {
        for expr in exprs {
            self.validate_expr_ref(*expr)?;
        }
        Ok(())
    }

    fn validate_expr_spread(&self, spread: &RecordSpread<ExprId>) -> Result<(), ValidateError> {
        match spread {
            RecordSpread::None => Ok(()),
            RecordSpread::Head(expr) | RecordSpread::Tail(expr) => self.validate_expr_ref(*expr),
        }
    }

    fn validate_block(&self, block: &Block) -> Result<(), ValidateError> {
        for stmt in &block.stmts {
            match stmt {
                Stmt::Let(_, pat, expr) => {
                    self.validate_pat(pat)?;
                    self.validate_expr_ref(*expr)?;
                }
                Stmt::Expr(expr) => self.validate_expr_ref(*expr)?,
                Stmt::Module(_, stmts) => self.validate_stmts(stmts)?,
            }
        }
        if let Some(tail) = block.tail {
            self.validate_expr_ref(tail)?;
        }
        Ok(())
    }

    fn validate_stmts(&self, stmts: &[Stmt]) -> Result<(), ValidateError> {
        for stmt in stmts {
            match stmt {
                Stmt::Let(_, pat, expr) => {
                    self.validate_pat(pat)?;
                    self.validate_expr_ref(*expr)?;
                }
                Stmt::Expr(expr) => self.validate_expr_ref(*expr)?,
                Stmt::Module(_, stmts) => self.validate_stmts(stmts)?,
            }
        }
        Ok(())
    }

    fn validate_pat(&self, pat: &Pat) -> Result<(), ValidateError> {
        match pat {
            Pat::Wild | Pat::Lit(_) | Pat::Var(_) => Ok(()),
            Pat::Tuple(items) => self.validate_pats(items),
            Pat::List { .. } => Err(ValidateError::UnsupportedPattern {
                feature: "list pattern".to_string(),
            }),
            Pat::Record { fields, spread } => {
                for (_, pat) in fields {
                    self.validate_pat(pat)?;
                }
                if let RecordSpread::Head(_) | RecordSpread::Tail(_) = spread {
                    return Ok(());
                }
                Ok(())
            }
            Pat::PolyVariant(_, payloads) => self.validate_pats(payloads),
            Pat::Con(_, _) => Err(ValidateError::UnsupportedPattern {
                feature: "constructor pattern".to_string(),
            }),
            Pat::Ref(instance) => self.validate_instance_ref(*instance),
            Pat::Or(left, right) => {
                self.validate_pat(left)?;
                self.validate_pat(right)
            }
            Pat::As(pat, _) => self.validate_pat(pat),
        }
    }

    fn validate_pats(&self, pats: &[Pat]) -> Result<(), ValidateError> {
        for pat in pats {
            self.validate_pat(pat)?;
        }
        Ok(())
    }
}

fn validate_type(ty: &Type) -> Result<(), ValidateError> {
    if let Some((feature, ty)) = first_non_vm_ready_type(ty) {
        return Err(ValidateError::NonVmReadyType { feature, ty });
    }
    Ok(())
}

fn first_non_vm_ready_type(ty: &Type) -> Option<(String, Type)> {
    match ty {
        Type::Any | Type::Never => None,
        Type::OpenVar(_) => Some(("unresolved type variable".to_string(), ty.clone())),
        Type::Con { args, .. } => first_non_vm_ready_types(args),
        Type::Fun {
            arg,
            arg_effect,
            ret_effect,
            ret,
        } => {
            if !arg_effect.is_pure_effect() {
                return Some((
                    "function argument effect is not pure".to_string(),
                    ty.clone(),
                ));
            }
            if !ret_effect.is_pure_effect() {
                return Some(("function return effect is not pure".to_string(), ty.clone()));
            }
            first_non_vm_ready_type(arg)
                .or_else(|| first_non_vm_ready_type(arg_effect))
                .or_else(|| first_non_vm_ready_type(ret_effect))
                .or_else(|| first_non_vm_ready_type(ret))
        }
        Type::Thunk { effect, value } => {
            first_non_vm_ready_type(effect).or_else(|| first_non_vm_ready_type(value))
        }
        Type::Record(fields) => fields
            .iter()
            .find_map(|field| first_non_vm_ready_type(&field.value)),
        Type::PolyVariant(variants) => variants
            .iter()
            .find_map(|variant| first_non_vm_ready_types(&variant.payloads)),
        Type::Tuple(items) | Type::EffectRow(items) => first_non_vm_ready_types(items),
        Type::Stack { .. } => Some((
            "stack type remains after specialization".to_string(),
            ty.clone(),
        )),
        Type::Union(_, _) => Some((
            "union type remains after specialization".to_string(),
            ty.clone(),
        )),
        Type::Intersection(_, _) => Some((
            "intersection type remains after specialization".to_string(),
            ty.clone(),
        )),
    }
}

fn first_non_vm_ready_types(types: &[Type]) -> Option<(String, Type)> {
    types.iter().find_map(first_non_vm_ready_type)
}
