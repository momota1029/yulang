//! Whole-program certificate for the closed primitive ModuleRun universe.
//! This is unavailable for imported execution contexts or raw Resume entry.
use std::collections::{HashMap, HashSet};

use yu_hir::HirLocalId;
use yu_hir::shadow::{
    LocalSourceCatchBinderId, LocalSourceCatchPattern, LocalSourceCatchPayloadPattern,
    LocalSourceCatchValuePattern, LocalSourceResolution, SourceAnnotationType,
    SourceAnnotationValue, SourceOperationDeclaration, SourceOperationId,
    SourceOperationResolution,
};

use super::program::{Instruction, Label, NameConsumption, RuntimeProgram};

#[derive(Clone, Copy)]
enum Role {
    Ground = 0,
    DirectCallee = 1,
}
enum Visit {
    Enter(Label, Role),
    Leave(Label, Role),
}

/// Checks every constructed definition, arm and dependency, including unused
/// code. Failure withholds only this negative-visibility certificate.
///
/// Work and storage are linear in code, ownership/dependency edges and distinct
/// declaration operands, including the hash/equality cost of authentic IDs.
/// No runtime receipt, view or continuation is rewritten by this classifier.
pub(super) fn closed_primitive(program: &RuntimeProgram) -> bool {
    let mut locals: HashMap<&HirLocalId, Label> = HashMap::new();
    let mut catches: HashSet<&LocalSourceCatchBinderId> = HashSet::new();
    let mut operations = HashMap::new();
    for code in &program.code {
        match &code.instruction {
            Instruction::Lambda { .. } => return false,
            Instruction::Block { bindings, .. } => {
                for binding in bindings {
                    if binding.recursive
                        || binding.id.source_root() != &code.site.source_root
                        || locals.insert(&binding.id, binding.initializer).is_some()
                    {
                        return false;
                    }
                }
            }
            Instruction::Catch { arms, .. } => {
                for arm in arms {
                    match &arm.pattern {
                        LocalSourceCatchPattern::Value(pattern) => {
                            if !ground_pattern(pattern, &code.site.source_root, &mut catches) {
                                return false;
                            }
                        }
                        LocalSourceCatchPattern::Operation {
                            resolution,
                            payloads,
                            continuation,
                            ..
                        } => {
                            let SourceOperationResolution::Resolved(declaration) = resolution
                            else {
                                return false;
                            };
                            if !primitive_operation(declaration, &mut operations)
                                || !matches!(continuation, LocalSourceCatchValuePattern::Wildcard)
                            {
                                return false;
                            }
                            let [payload] = payloads.as_slice() else {
                                return false;
                            };
                            if let LocalSourceCatchPayloadPattern::Value(pattern) = payload {
                                if !ground_pattern(pattern, &code.site.source_root, &mut catches) {
                                    return false;
                                }
                            }
                        }
                    }
                }
            }
            Instruction::Case { arms, .. } => {
                if arms.iter().any(|arm| matches!(arm.pattern, super::program::CasePattern::Wildcard | super::program::CasePattern::Binder(_))) {
                    // Integer tests and total binders are closed local primitive patterns.
                } else {
                    return false;
                }
                for arm in arms {
                    if let super::program::CasePattern::Binder(id) = &arm.pattern {
                        if id.source_root() != &code.site.source_root {
                            return false;
                        }
                        catches.insert(id);
                    }
                }
            }
            _ => {}
        }
    }
    if program.definition_indices.len() != program.definitions.len() {
        return false;
    }
    let mut work = Vec::new();
    for (index, definition) in program.definitions.iter().enumerate() {
        if program.definition_indices.get(&definition.id) != Some(&index) {
            return false;
        }
        work.push(Visit::Enter(definition.body, Role::Ground));
    }
    for body in program.expression_roots.values() {
        work.push(Visit::Enter(*body, Role::Ground));
    }
    let mut states = vec![[0u8; 2]; program.code.len()];
    while let Some(visit) = work.pop() {
        let (label, role) = match visit {
            Visit::Enter(label, role) => (label, role),
            Visit::Leave(label, role) => {
                states[label.0][role as usize] = 2;
                continue;
            }
        };
        let Some(code) = program.code.get(label.0) else {
            return false;
        };
        match states[label.0][role as usize] {
            1 => return false, // No ungrounded definition/local dependency cycle.
            2 => continue,
            _ => {}
        }
        states[label.0][role as usize] = 1;
        work.push(Visit::Leave(label, role));
        if matches!(role, Role::DirectCallee) {
            match &code.instruction {
                Instruction::Forward(inner) => work.push(Visit::Enter(*inner, role)),
                Instruction::Operation(SourceOperationResolution::Resolved(declaration))
                    if primitive_operation(declaration, &mut operations) => {}
                _ => return false,
            }
            continue;
        }
        match &code.instruction {
            Instruction::Unit
            | Instruction::Integer(_)
            | Instruction::Boolean(_)
            | Instruction::String(_) => {}
            Instruction::Forward(inner) => work.push(Visit::Enter(*inner, Role::Ground)),
            Instruction::Name {
                resolution,
                consumption,
            } => {
                if *consumption != NameConsumption::Observe {
                    return false;
                }
                match resolution {
                    LocalSourceResolution::ModuleDef(id) => {
                        let Some(index) = program.definition_indices.get(id) else {
                            return false;
                        };
                        work.push(Visit::Enter(program.definitions[*index].body, Role::Ground));
                    }
                    LocalSourceResolution::Local(id) => {
                        let Some(initializer) = locals.get(id) else {
                            return false;
                        };
                        work.push(Visit::Enter(*initializer, Role::Ground));
                    }
                    LocalSourceResolution::CatchBinder(id) if catches.contains(id) => {}
                    LocalSourceResolution::CaseBinder(id) if catches.contains(id) => {}
                    _ => return false,
                }
            }
            Instruction::Apply { callee, argument } => {
                work.push(Visit::Enter(*callee, Role::DirectCallee));
                work.push(Visit::Enter(*argument, Role::Ground));
            }
            Instruction::Block {
                bindings,
                final_expression,
            } => {
                work.push(Visit::Enter(*final_expression, Role::Ground));
                for binding in bindings {
                    work.push(Visit::Enter(binding.initializer, Role::Ground));
                }
            }
            Instruction::If { arms, else_branch } => {
                if let Some(branch) = else_branch {
                    work.push(Visit::Enter(*branch, Role::Ground));
                }
                for (condition, body) in arms {
                    work.push(Visit::Enter(*condition, Role::Ground));
                    work.push(Visit::Enter(*body, Role::Ground));
                }
            }
            Instruction::Sequence { items } => {
                for item in items { work.push(Visit::Enter(*item, Role::Ground)); }
            }
            Instruction::Catch { scrutinee, arms } => {
                work.push(Visit::Enter(*scrutinee, Role::Ground));
                for arm in arms {
                    work.push(Visit::Enter(arm.body, Role::Ground));
                }
            }
            Instruction::Case { scrutinee, arms } => {
                work.push(Visit::Enter(*scrutinee, Role::Ground));
                for arm in arms {
                    work.push(Visit::Enter(arm.body, Role::Ground));
                }
            }
            Instruction::Lambda { .. } | Instruction::Operation(_) => return false,
        }
    }
    // Orphaned retained code cannot escape the whole-universe check.
    states.iter().all(|state| state.contains(&2))
}

fn ground_pattern<'a>(
    pattern: &'a LocalSourceCatchValuePattern,
    owner: &yu_hir::SourceRootId,
    binders: &mut HashSet<&'a LocalSourceCatchBinderId>,
) -> bool {
    match pattern {
        LocalSourceCatchValuePattern::Wildcard => true,
        LocalSourceCatchValuePattern::Binder(binder) => {
            binder.id.source_root() == owner && binders.insert(&binder.id)
        }
    }
}
fn primitive_value(ty: &SourceAnnotationType) -> bool {
    ty.effects.is_none()
        && matches!(
            ty.value,
            SourceAnnotationValue::Unit
                | SourceAnnotationValue::Int
                | SourceAnnotationValue::Bool
                | SourceAnnotationValue::Str
        )
}
fn primitive_operation<'a>(
    declaration: &'a SourceOperationDeclaration,
    cache: &mut HashMap<&'a SourceOperationId, bool>,
) -> bool {
    *cache.entry(&declaration.id).or_insert_with(|| {
        let SourceAnnotationValue::Function { argument, result } = &declaration.signature.value
        else {
            return false;
        };
        declaration.signature.effects.is_none()
            && primitive_value(argument)
            && primitive_value(result)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::runtime::RuntimeEvidence;
    use std::sync::Arc;
    use yu_hir::shadow::lower_module_with_local_source;
    use yu_hir::{FileId, FileKey, ModuleIdentity, SemanticImports};
    use yu_syntax::{SourceText, SyntaxEnvironment, parse_file, scan_header};

    fn classify(source: &str) -> bool {
        let source: Arc<SourceText> = Arc::from(source);
        let parsed = parse_file(
            source.clone(),
            Arc::new(scan_header(source)),
            Arc::new(SyntaxEnvironment::empty()),
        );
        assert!(parsed.syntax_diagnostics().unwrap().is_empty());
        let hir = Arc::new(
            lower_module_with_local_source(
                ModuleIdentity::source_root(FileId::new(FileKey::new(
                    "primitive-classifier",
                    "test.yu",
                ))),
                &parsed,
                SemanticImports::empty(),
            )
            .unwrap(),
        );
        let program = RuntimeProgram::from_hir(hir, RuntimeEvidence::default()).unwrap();
        closed_primitive(&program)
    }
    const IO: &str = "act io:\n    our tick: int -> int\n";

    #[test]
    fn certificate_covers_closed_roots_ground_dependencies_and_discarding_arms() {
        for body in [
            "my main = catch io::tick 7 { io::tick(p), _ -> p }",
            "my value = 7; my main = catch io::tick value { io::tick(p), _ -> p }",
            "my main = { my value = 7; catch io::tick value { io::tick(p), _ -> p } }",
            "my main = catch (if true: io::tick 7 else: 9) { io::tick(p), _ -> p, x -> x }",
        ] {
            assert!(classify(&format!("{IO}{body}")), "{body}");
        }
    }
    #[test]
    fn certificate_rejects_unused_callable_values_aliases_raw_binders_and_comp_ports() {
        for body in [
            "my unused x = x; my main = catch io::tick 7 { io::tick(p), _ -> p }",
            "my alias = io::tick; my main = catch io::tick 7 { io::tick(p), _ -> p }",
            "my main = catch io::tick 7 { io::tick(p), k -> p }",
        ] {
            assert!(!classify(&format!("{IO}{body}")), "{body}");
        }
        assert!(!classify(
            "act io:\n    our tick: int -> [io] int\nmy main = catch io::tick 7 { io::tick(p), _ -> p }"
        ));
    }
}
