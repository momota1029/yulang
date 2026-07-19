//! Lowering from the tree-shaped `mono` program into the control IR arena.

use std::fmt;

use crate::ir::{
    Block, CaseArm, CatchArm, DefId, Expr, ExprId, Instance, InstanceId, Pat, Program, RecordField,
    RecordPatField, RecordSpread, Root, SelectResolution, Stmt,
};
use crate::{ApplicationProvenanceTable, SelectionProvenanceTable};

pub fn lower(program: &mono::Program) -> Result<Program, LowerError> {
    Ok(lower_with_application_provenance(program)?.program)
}

pub fn lower_with_application_provenance(
    program: &mono::Program,
) -> Result<LowerOutput, LowerError> {
    Lowerer::default().lower_program(program)
}

#[derive(Debug, Clone, PartialEq)]
pub struct LowerOutput {
    pub program: Program,
    pub application_provenance: ApplicationProvenanceTable,
    pub selection_provenance: SelectionProvenanceTable,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LowerError {
    MismatchedInstanceSlot {
        expected: InstanceId,
        actual: InstanceId,
    },
}

impl fmt::Display for LowerError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MismatchedInstanceSlot { expected, actual } => write!(
                f,
                "mismatched instance slot while lowering: expected m{}, found m{}",
                expected.0, actual.0
            ),
        }
    }
}

impl std::error::Error for LowerError {}

#[derive(Debug, Default)]
struct Lowerer {
    exprs: Vec<Expr>,
    application_provenance: ApplicationProvenanceTable,
    selection_provenance: SelectionProvenanceTable,
}

impl Lowerer {
    fn lower_program(mut self, program: &mono::Program) -> Result<LowerOutput, LowerError> {
        let roots = program
            .roots
            .iter()
            .map(|root| self.lower_root(root))
            .collect::<Result<Vec<_>, _>>()?;
        let instances = program
            .instances
            .iter()
            .enumerate()
            .map(|(index, instance)| self.lower_instance(index, instance))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(LowerOutput {
            program: Program {
                roots,
                instances,
                exprs: self.exprs,
            },
            application_provenance: self.application_provenance,
            selection_provenance: self.selection_provenance,
        })
    }

    fn lower_root(&mut self, root: &mono::Root) -> Result<Root, LowerError> {
        match root {
            mono::Root::Instance(instance) => Ok(Root::Instance(convert_instance(*instance))),
            mono::Root::EvalInstance(instance) => {
                Ok(Root::EvalInstance(convert_instance(*instance)))
            }
            mono::Root::Expr(expr) => Ok(Root::Expr(self.lower_expr(expr)?)),
        }
    }

    fn lower_instance(
        &mut self,
        index: usize,
        instance: &mono::Instance,
    ) -> Result<Instance, LowerError> {
        let expected = InstanceId(index as u32);
        let actual = convert_instance(instance.id);
        if expected != actual {
            return Err(LowerError::MismatchedInstanceSlot { expected, actual });
        }
        Ok(Instance {
            id: actual,
            source: instance.source.clone(),
            signature: instance.signature.clone(),
            entry: self.lower_expr(&instance.body)?,
        })
    }

    fn lower_expr(&mut self, expr: &mono::Expr) -> Result<ExprId, LowerError> {
        use mono::ExprKind as MonoExpr;
        let lowered = match &expr.kind {
            MonoExpr::Lit(lit) => Expr::Lit(lit.clone()),
            MonoExpr::PrimitiveOp { op, context } => Expr::PrimitiveOp {
                op: *op,
                context: context.clone(),
            },
            MonoExpr::Constructor { def, arity } => Expr::Constructor {
                def: convert_def(*def),
                arity: *arity,
            },
            MonoExpr::EffectOp { def, path } => Expr::EffectOp {
                def: def.map(convert_def),
                path: path.clone(),
            },
            MonoExpr::Local(def) => Expr::Local(convert_def(*def)),
            MonoExpr::InstanceRef(instance) => Expr::InstanceRef(convert_instance(*instance)),
            MonoExpr::Coerce {
                source,
                target,
                expr,
            } => Expr::Coerce {
                source: source.clone(),
                target: target.clone(),
                expr: self.lower_expr(expr)?,
            },
            MonoExpr::MakeThunk {
                source,
                target,
                body,
            } => Expr::MakeThunk {
                source: source.clone(),
                target: target.clone(),
                body: self.lower_expr(body)?,
            },
            MonoExpr::ForceThunk {
                source,
                target,
                thunk,
            } => Expr::ForceThunk {
                source: source.clone(),
                target: target.clone(),
                thunk: self.lower_expr(thunk)?,
            },
            MonoExpr::FunctionAdapter {
                source,
                target,
                function,
                hygiene,
            } => Expr::FunctionAdapter {
                source: source.clone(),
                target: target.clone(),
                function: self.lower_expr(function)?,
                hygiene: hygiene.clone(),
            },
            MonoExpr::MarkerFrame { path, body } => Expr::MarkerFrame {
                path: path.clone(),
                body: self.lower_expr(body)?,
            },
            MonoExpr::Apply(callee, arg) => Expr::Apply {
                callee: self.lower_expr(callee)?,
                arg: self.lower_expr(arg)?,
            },
            MonoExpr::RefSet(reference, value) => Expr::RefSet {
                reference: self.lower_expr(reference)?,
                value: self.lower_expr(value)?,
            },
            MonoExpr::Lambda(param, body) => Expr::Lambda {
                param: self.lower_pat(param)?,
                body: self.lower_expr(body)?,
            },
            MonoExpr::Tuple(items) => Expr::Tuple(self.lower_exprs(items)?),
            MonoExpr::Record { fields, spread } => Expr::Record {
                fields: fields
                    .iter()
                    .map(|field| {
                        Ok(RecordField {
                            name: field.name.clone(),
                            value: self.lower_expr(&field.value)?,
                        })
                    })
                    .collect::<Result<Vec<_>, LowerError>>()?,
                spread: self.lower_spread(spread)?,
            },
            MonoExpr::PolyVariant { tag, payloads } => Expr::PolyVariant {
                tag: tag.clone(),
                payloads: self.lower_exprs(payloads)?,
            },
            MonoExpr::Select {
                base,
                name,
                resolution,
            } => Expr::Select {
                base: self.lower_expr(base)?,
                name: name.clone(),
                resolution: resolution.as_ref().map(lower_select_resolution),
            },
            MonoExpr::Case { scrutinee, arms } => Expr::Case {
                scrutinee: self.lower_expr(scrutinee)?,
                arms: arms
                    .iter()
                    .map(|arm| {
                        Ok(CaseArm {
                            pat: self.lower_pat(&arm.pat)?,
                            guard: self.lower_optional_expr(arm.guard.as_ref())?,
                            body: self.lower_expr(&arm.body)?,
                        })
                    })
                    .collect::<Result<Vec<_>, LowerError>>()?,
            },
            MonoExpr::Catch { body, arms } => Expr::Catch {
                body: self.lower_expr(body)?,
                arms: arms
                    .iter()
                    .map(|arm| {
                        Ok(CatchArm {
                            operation_path: arm.operation_path.clone(),
                            pat: self.lower_pat(&arm.pat)?,
                            continuation: self.lower_optional_pat(arm.continuation.as_ref())?,
                            guard: self.lower_optional_expr(arm.guard.as_ref())?,
                            body: self.lower_expr(&arm.body)?,
                        })
                    })
                    .collect::<Result<Vec<_>, LowerError>>()?,
            },
            MonoExpr::Block(block) => Expr::Block(self.lower_block(block)?),
        };
        let id = ExprId(self.exprs.len() as u32);
        if let Some(tag) = expr.application_provenance() {
            debug_assert!(
                matches!(lowered, Expr::Apply { .. }),
                "application provenance must only be attached to mono Apply nodes"
            );
            let previous = self.application_provenance.insert(id, tag);
            debug_assert!(
                previous.is_none(),
                "fresh control site cannot be tagged twice"
            );
        }
        if let Some(tag) = expr.selection_provenance() {
            debug_assert!(
                matches!(lowered, Expr::Select { .. }),
                "selection provenance must only be attached to mono Select nodes"
            );
            let previous = self.selection_provenance.insert(id, tag);
            debug_assert!(
                previous.is_none(),
                "fresh control site cannot be tagged twice"
            );
        }
        self.exprs.push(lowered);
        Ok(id)
    }

    fn lower_exprs(&mut self, exprs: &[mono::Expr]) -> Result<Vec<ExprId>, LowerError> {
        exprs.iter().map(|expr| self.lower_expr(expr)).collect()
    }

    fn lower_optional_expr(
        &mut self,
        expr: Option<&mono::Expr>,
    ) -> Result<Option<ExprId>, LowerError> {
        expr.map(|expr| self.lower_expr(expr)).transpose()
    }

    fn lower_optional_pat(&mut self, pat: Option<&mono::Pat>) -> Result<Option<Pat>, LowerError> {
        pat.map(|pat| self.lower_pat(pat)).transpose()
    }

    fn lower_block(&mut self, block: &mono::Block) -> Result<Block, LowerError> {
        Ok(Block {
            stmts: block
                .stmts
                .iter()
                .map(|stmt| self.lower_stmt(stmt))
                .collect::<Result<Vec<_>, _>>()?,
            tail: self.lower_optional_expr(block.tail.as_deref())?,
        })
    }

    fn lower_stmt(&mut self, stmt: &mono::Stmt) -> Result<Stmt, LowerError> {
        match stmt {
            mono::Stmt::Let(vis, pat, value) => Ok(Stmt::Let(
                *vis,
                self.lower_pat(pat)?,
                self.lower_expr(value)?,
            )),
            mono::Stmt::Expr(expr) => Ok(Stmt::Expr(self.lower_expr(expr)?)),
            mono::Stmt::Module(def, stmts) => Ok(Stmt::Module(
                convert_def(*def),
                stmts
                    .iter()
                    .map(|stmt| self.lower_stmt(stmt))
                    .collect::<Result<Vec<_>, _>>()?,
            )),
        }
    }

    fn lower_spread(
        &mut self,
        spread: &mono::RecordSpread<Box<mono::Expr>>,
    ) -> Result<RecordSpread<ExprId>, LowerError> {
        match spread {
            mono::RecordSpread::None => Ok(RecordSpread::None),
            mono::RecordSpread::Head(expr) => Ok(RecordSpread::Head(self.lower_expr(expr)?)),
            mono::RecordSpread::Tail(expr) => Ok(RecordSpread::Tail(self.lower_expr(expr)?)),
        }
    }

    fn lower_pat(&mut self, pat: &mono::Pat) -> Result<Pat, LowerError> {
        Ok(match pat {
            mono::Pat::Wild => Pat::Wild,
            mono::Pat::Lit(lit) => Pat::Lit(lit.clone()),
            mono::Pat::Tuple(items) => Pat::Tuple(self.lower_pats(items)?),
            mono::Pat::List {
                prefix,
                spread,
                suffix,
            } => Pat::List {
                prefix: self.lower_pats(prefix)?,
                spread: self.lower_optional_pat(spread.as_deref())?.map(Box::new),
                suffix: self.lower_pats(suffix)?,
            },
            mono::Pat::Record { fields, spread } => Pat::Record {
                fields: fields
                    .iter()
                    .map(|field| {
                        Ok(RecordPatField {
                            name: field.name.clone(),
                            pat: self.lower_pat(&field.pat)?,
                            default: self.lower_optional_expr(field.default.as_ref())?,
                        })
                    })
                    .collect::<Result<Vec<_>, LowerError>>()?,
                spread: lower_def_spread(spread),
            },
            mono::Pat::PolyVariant(tag, payloads) => {
                Pat::PolyVariant(tag.clone(), self.lower_pats(payloads)?)
            }
            mono::Pat::Con(def, payloads) => {
                Pat::Con(convert_def(*def), self.lower_pats(payloads)?)
            }
            mono::Pat::Ref(instance) => Pat::Ref(convert_instance(*instance)),
            mono::Pat::Var(def) => Pat::Var(convert_def(*def)),
            mono::Pat::Or(left, right) => Pat::Or(
                Box::new(self.lower_pat(left)?),
                Box::new(self.lower_pat(right)?),
            ),
            mono::Pat::As(pat, def) => Pat::As(Box::new(self.lower_pat(pat)?), convert_def(*def)),
        })
    }

    fn lower_pats(&mut self, pats: &[mono::Pat]) -> Result<Vec<Pat>, LowerError> {
        pats.iter().map(|pat| self.lower_pat(pat)).collect()
    }
}

fn lower_def_spread(spread: &mono::RecordSpread<mono::DefId>) -> RecordSpread<DefId> {
    match spread {
        mono::RecordSpread::None => RecordSpread::None,
        mono::RecordSpread::Head(def) => RecordSpread::Head(convert_def(*def)),
        mono::RecordSpread::Tail(def) => RecordSpread::Tail(convert_def(*def)),
    }
}

fn lower_select_resolution(resolution: &mono::SelectResolution) -> SelectResolution {
    match resolution {
        mono::SelectResolution::RecordField => SelectResolution::RecordField,
        mono::SelectResolution::Method { instance } => SelectResolution::Method {
            instance: convert_instance(*instance),
        },
        mono::SelectResolution::TypeclassMethod { member } => SelectResolution::TypeclassMethod {
            member: convert_def(*member),
        },
    }
}

fn convert_def(def: mono::DefId) -> DefId {
    DefId(def.0)
}

fn convert_instance(instance: mono::InstanceId) -> InstanceId {
    InstanceId(instance.0)
}

#[cfg(test)]
mod tests {
    use mono::{ApplicationSpecializationTask, ExprKind};

    use super::*;

    #[test]
    fn source_not_callable_application_reaches_its_final_control_site() {
        let source = "my a = 1 2\na\n";
        let lowering = lower_source(source);
        let source_provenance = lowering.application_provenance();
        let mut captured_entries = source_provenance.iter();
        let (poly_expr, captured) = captured_entries
            .next()
            .expect("not-callable canary should have one source application");
        assert!(captured_entries.next().is_none());

        let specialized = specialize::specialize_with_runtime_evidence_and_application_provenance(
            &lowering.session.poly,
            source_provenance.expr_ids(),
        )
        .expect("not-callable canary should specialize");
        let mono_apply = specialized
            .program
            .instances
            .iter()
            .map(|instance| &instance.body)
            .find(|expr| expr.application_provenance().is_some())
            .expect("source application should tag its mono Apply");
        assert!(matches!(mono_apply.kind, ExprKind::Apply(_, _)));
        let mono_tag = mono_apply
            .application_provenance()
            .expect("tagged mono Apply");
        assert_eq!(mono_tag.poly_expr, poly_expr.0);
        assert!(matches!(
            mono_tag.task,
            ApplicationSpecializationTask::Instance { .. }
        ));

        let control = lower_with_application_provenance(&specialized.program)
            .expect("tagged mono program should lower");
        assert_eq!(
            lower(&specialized.program).expect("legacy lowering should still succeed"),
            control.program,
            "capturing the side table must not change the control program"
        );
        let mut control_entries = control.application_provenance.iter();
        let (site, control_tag) = control_entries
            .next()
            .expect("not-callable canary should have one tagged control Apply");
        assert!(control_entries.next().is_none());
        assert!(matches!(
            control.program.exprs[site.0 as usize],
            Expr::Apply { .. }
        ));
        assert_eq!(control_tag, mono_tag);

        let resolved = source_provenance
            .iter()
            .find_map(|(expr, provenance)| (expr.0 == control_tag.poly_expr).then_some(provenance))
            .expect("control tag should resolve in infer's source table");
        assert_eq!(resolved, captured);
        assert_eq!(
            source_text(source, resolved.application_span.range),
            "1 2\n"
        );
        assert_eq!(source_text(source, resolved.callee_span.range), "1");
    }

    #[test]
    fn source_not_record_selection_reaches_its_final_control_site() {
        let source = "my a = 1.a\na\n";
        let lowering = lower_source(source);
        let mut source_selections = lowering.session.selections.source_spans();
        let (select, captured) = source_selections
            .next()
            .expect("not-record canary should have one source selection");
        assert!(source_selections.next().is_none());
        assert_eq!(source_text(source, captured.range), "a");

        let specialized = specialize::specialize_with_runtime_evidence_and_source_provenance(
            &lowering.session.poly,
            lowering.application_provenance().expr_ids(),
            [select],
        )
        .expect("not-record canary should specialize");
        let mono_select = specialized
            .program
            .instances
            .iter()
            .map(|instance| &instance.body)
            .find(|expr| expr.selection_provenance().is_some())
            .expect("source selection should tag its mono Select");
        assert!(matches!(mono_select.kind, ExprKind::Select { .. }));
        let mono_tag = mono_select
            .selection_provenance()
            .expect("tagged mono Select");
        assert_eq!(mono_tag.select, select.0);
        assert!(matches!(
            mono_tag.task,
            ApplicationSpecializationTask::Instance { .. }
        ));

        let control = lower_with_application_provenance(&specialized.program)
            .expect("tagged mono program should lower");
        assert_eq!(
            lower(&specialized.program).expect("legacy lowering should still succeed"),
            control.program,
            "capturing the side table must not change the control program"
        );
        let mut control_entries = control.selection_provenance.iter();
        let (site, control_tag) = control_entries
            .next()
            .expect("not-record canary should have one tagged control Select");
        assert!(control_entries.next().is_none());
        assert!(matches!(
            control.program.exprs[site.0 as usize],
            Expr::Select { .. }
        ));
        assert_eq!(control_tag, mono_tag);

        let resolved = lowering
            .session
            .selections
            .source_spans()
            .find_map(|(select, span)| (select.0 == control_tag.select).then_some(span))
            .expect("control tag should resolve in infer's source table");
        assert_eq!(resolved, captured);
    }

    #[test]
    fn one_generic_body_application_has_distinct_tags_in_two_instance_tasks() {
        let source = concat!(
            "my call f x = f x\n",
            "my id x = x\n",
            "(call(id)(1), call(id)(true))\n",
        );
        let lowering = lower_source(source);
        let source_provenance = lowering.application_provenance();
        let (body_application, _) = source_provenance
            .iter()
            .find(|(_, provenance)| {
                source_text(source, provenance.application_span.range).trim_end() == "f x"
            })
            .expect("generic body source application");

        let specialized = specialize::specialize_with_runtime_evidence_and_application_provenance(
            &lowering.session.poly,
            source_provenance.expr_ids(),
        )
        .expect("two generic call instances should specialize");
        let control = lower_with_application_provenance(&specialized.program)
            .expect("tagged generic instances should lower");
        let tags = control
            .application_provenance
            .iter()
            .filter_map(|(site, tag)| (tag.poly_expr == body_application.0).then_some((site, tag)))
            .collect::<Vec<_>>();

        assert_eq!(tags.len(), 2, "the generic body should be emitted twice");
        assert_ne!(tags[0].0, tags[1].0, "control Apply sites are fresh");
        assert_ne!(tags[0].1.task, tags[1].1.task, "tasks must not conflate");
        assert!(tags.iter().all(|(site, tag)| {
            matches!(control.program.exprs[site.0 as usize], Expr::Apply { .. })
                && matches!(tag.task, ApplicationSpecializationTask::Instance { .. })
                && source_provenance
                    .iter()
                    .any(|(expr, _)| expr.0 == tag.poly_expr)
        }));
    }

    fn lower_source(source: &str) -> infer::lowering::BodyLowering {
        let files = sources::load(vec![sources::SourceFile {
            module_path: sources::Path::default(),
            source: source.to_string(),
        }]);
        let output = infer::dump::dump_loaded_files(&files).expect("source should lower");
        assert!(
            output.lowering.errors.is_empty(),
            "body lowering errors: {:?}",
            output.lowering.errors
        );
        output.lowering
    }

    fn source_text(source: &str, range: sources::SourceRange) -> &str {
        &source[range.start..range.end]
    }
}
