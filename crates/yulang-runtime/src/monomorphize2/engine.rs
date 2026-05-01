use super::*;
use crate::ir::{Binding, Module};

pub fn demand_monomorphize_module(
    module: Module,
) -> Result<DemandMonomorphizeOutput, DemandMonomorphizeError> {
    let engine_output = DemandEngine::from_module(&module).run()?;
    if engine_output.specializations.is_empty() {
        return Ok(DemandMonomorphizeOutput {
            module,
            profile: DemandMonomorphizeProfile::default(),
        });
    }
    let specializations = engine_output
        .specializations
        .iter()
        .filter(|specialization| specialization.solved.is_closed())
        .cloned()
        .collect::<Vec<_>>();
    if specializations.is_empty() {
        return Ok(DemandMonomorphizeOutput {
            module,
            profile: DemandMonomorphizeProfile::default(),
        });
    }
    if std::env::var_os("YULANG_DEBUG_MONO_PIPELINE").is_some() {
        for specialization in &engine_output.specializations {
            let status = if specialization.solved.is_closed() {
                "closed"
            } else {
                "open"
            };
            eprintln!(
                "demand specialization {status} {:?} -> {:?}: {:?}",
                specialization.target, specialization.path, specialization.solved
            );
        }
    }
    let emitted = DemandEngineOutput {
        checked: engine_output.checked,
        specializations: specializations.clone(),
    }
    .emit_bindings(&module)?;
    let rewrite =
        DemandEmitter::rewrite_module_uses_with_specializations_report(module, &specializations)?;
    if rewrite.changed_roots == 0 && rewrite.changed_bindings == 0 {
        return Ok(DemandMonomorphizeOutput {
            module: rewrite.module,
            profile: DemandMonomorphizeProfile::default(),
        });
    }
    let mut module = rewrite.module;
    let emitted_count = emitted.len();
    module.bindings.extend(emitted);
    Ok(DemandMonomorphizeOutput {
        module,
        profile: DemandMonomorphizeProfile {
            specializations: emitted_count,
        },
    })
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DemandMonomorphizeOutput {
    pub module: Module,
    pub profile: DemandMonomorphizeProfile,
}

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct DemandMonomorphizeProfile {
    pub specializations: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DemandMonomorphizeError {
    Check(DemandCheckError),
    Emit(DemandEmitError),
}

impl From<DemandCheckError> for DemandMonomorphizeError {
    fn from(error: DemandCheckError) -> Self {
        Self::Check(error)
    }
}

impl From<DemandEmitError> for DemandMonomorphizeError {
    fn from(error: DemandEmitError) -> Self {
        Self::Emit(error)
    }
}

pub struct DemandEngine<'a> {
    checker: DemandChecker<'a>,
    queue: DemandQueue,
    specializations: SpecializationTable,
    checked: Vec<CheckedDemand>,
}

impl<'a> DemandEngine<'a> {
    pub fn from_module(module: &'a Module) -> Self {
        let mut collector = DemandCollector::from_module(module);
        collector.collect_module(module);
        Self {
            checker: DemandChecker::from_module(module),
            queue: collector.into_queue(),
            specializations: SpecializationTable::default(),
            checked: Vec::new(),
        }
    }

    pub fn run(mut self) -> Result<DemandEngineOutput, DemandCheckError> {
        while let Some(demand) = self.queue.pop_front() {
            let checked = match self.checker.check_demand(&demand) {
                Ok(checked) => checked,
                Err(error) => {
                    if std::env::var_os("YULANG_DEBUG_MONO_PIPELINE").is_some() {
                        eprintln!(
                            "demand rejected for {:?}: {:?}: {:?}",
                            demand.target, demand.key.signature, error
                        );
                    }
                    continue;
                }
            };
            self.specializations.intern(&checked);
            let mut child_demands = checked.child_demands.clone();
            while let Some(child) = child_demands.pop_front() {
                self.queue
                    .push_signature(child.target, child.expected, child.key.signature);
            }
            self.checked.push(checked);
        }
        Ok(DemandEngineOutput {
            checked: self.checked,
            specializations: self.specializations.into_specializations(),
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DemandEngineOutput {
    pub checked: Vec<CheckedDemand>,
    pub specializations: Vec<DemandSpecialization>,
}

impl DemandEngineOutput {
    pub fn emit_bindings(&self, module: &Module) -> Result<Vec<Binding>, DemandEmitError> {
        DemandEmitter::from_module(module, &self.specializations).emit_all()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Binding, Expr, ExprKind, Root, Type as RuntimeType};

    #[test]
    fn engine_processes_root_and_child_demands_in_order() {
        let id = path("id");
        let use_id = path("use_id");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![
                binding(
                    id.clone(),
                    vec![core_ir::TypeVar("a".to_string())],
                    RuntimeType::fun(
                        RuntimeType::core(core_ir::Type::Any),
                        RuntimeType::core(core_ir::Type::Any),
                    ),
                    ExprKind::Lambda {
                        param: core_ir::Name("x".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(Expr::typed(
                            ExprKind::Var(path("x")),
                            RuntimeType::core(core_ir::Type::Any),
                        )),
                    },
                ),
                binding(
                    use_id.clone(),
                    Vec::new(),
                    RuntimeType::fun(
                        RuntimeType::core(named("int")),
                        RuntimeType::core(named("int")),
                    ),
                    ExprKind::Lambda {
                        param: core_ir::Name("x".to_string()),
                        param_effect_annotation: None,
                        param_function_allowed_effects: None,
                        body: Box::new(Expr::typed(
                            ExprKind::Apply {
                                callee: Box::new(Expr::typed(
                                    ExprKind::Var(id.clone()),
                                    RuntimeType::fun(
                                        RuntimeType::core(core_ir::Type::Any),
                                        RuntimeType::core(core_ir::Type::Any),
                                    ),
                                )),
                                arg: Box::new(Expr::typed(
                                    ExprKind::Var(path("x")),
                                    RuntimeType::core(named("int")),
                                )),
                                evidence: None,
                                instantiation: None,
                            },
                            RuntimeType::core(named("int")),
                        )),
                    },
                ),
            ],
            root_exprs: vec![Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(
                        ExprKind::Var(use_id.clone()),
                        RuntimeType::fun(
                            RuntimeType::core(named("int")),
                            RuntimeType::core(named("int")),
                        ),
                    )),
                    arg: Box::new(Expr::typed(
                        ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                        RuntimeType::core(named("int")),
                    )),
                    evidence: None,
                    instantiation: None,
                },
                RuntimeType::core(named("int")),
            )],
            roots: vec![Root::Expr(0)],
        };

        let output = DemandEngine::from_module(&module)
            .run()
            .expect("ran engine");
        let checked_targets = output
            .checked
            .iter()
            .map(|checked| checked.target.clone())
            .collect::<Vec<_>>();

        assert_eq!(checked_targets, vec![id]);
        assert_eq!(output.specializations.len(), 1);
        assert_eq!(
            output.specializations[0].path,
            core_ir::Path::from_name(core_ir::Name("id__ddmono0".to_string()))
        );
        let emitted = output.emit_bindings(&module).expect("emitted bindings");
        assert_eq!(emitted.len(), 1);
        assert_eq!(emitted[0].name, path("id__ddmono0"));
        assert!(emitted[0].type_params.is_empty());
    }

    #[test]
    fn demand_monomorphize_rewrites_root_call_to_specialization() {
        let id = path("id");
        let module = Module {
            path: core_ir::Path::default(),
            bindings: vec![binding(
                id.clone(),
                vec![core_ir::TypeVar("a".to_string())],
                RuntimeType::fun(
                    RuntimeType::core(core_ir::Type::Any),
                    RuntimeType::core(core_ir::Type::Any),
                ),
                ExprKind::Lambda {
                    param: core_ir::Name("x".to_string()),
                    param_effect_annotation: None,
                    param_function_allowed_effects: None,
                    body: Box::new(Expr::typed(
                        ExprKind::Var(path("x")),
                        RuntimeType::core(core_ir::Type::Any),
                    )),
                },
            )],
            root_exprs: vec![Expr::typed(
                ExprKind::Apply {
                    callee: Box::new(Expr::typed(
                        ExprKind::Var(id),
                        RuntimeType::fun(
                            RuntimeType::core(core_ir::Type::Any),
                            RuntimeType::core(core_ir::Type::Any),
                        ),
                    )),
                    arg: Box::new(Expr::typed(
                        ExprKind::Lit(core_ir::Lit::Int("1".to_string())),
                        RuntimeType::core(named("int")),
                    )),
                    evidence: None,
                    instantiation: None,
                },
                RuntimeType::core(named("int")),
            )],
            roots: vec![Root::Expr(0)],
        };

        let output = demand_monomorphize_module(module).expect("demand monomorphized");

        assert_eq!(output.profile.specializations, 1);
        assert_eq!(output.module.bindings.len(), 2);
        let ExprKind::Apply { callee, .. } = &output.module.root_exprs[0].kind else {
            panic!("expected rewritten root call");
        };
        let ExprKind::Var(path) = &callee.kind else {
            panic!("expected specialized callee");
        };
        assert_eq!(
            path,
            &core_ir::Path::from_name(core_ir::Name("id__ddmono0".to_string()))
        );
    }

    fn binding(
        name: core_ir::Path,
        type_params: Vec<core_ir::TypeVar>,
        ty: RuntimeType,
        kind: ExprKind,
    ) -> Binding {
        Binding {
            name,
            type_params,
            scheme: core_ir::Scheme {
                requirements: Vec::new(),
                body: core_ir::Type::Any,
            },
            body: Expr::typed(kind, ty),
        }
    }

    fn named(name: &str) -> core_ir::Type {
        core_ir::Type::Named {
            path: path(name),
            args: Vec::new(),
        }
    }

    fn path(name: &str) -> core_ir::Path {
        core_ir::Path::from_name(core_ir::Name(name.to_string()))
    }
}
