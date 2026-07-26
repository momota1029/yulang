//! Structural `Eq` derivation for nominal algebraic declarations.
//!
//! A derive request first resolves its role through the ordinary type namespace.
//! Only the canonical standard-library `Eq` identity selects this strategy; the
//! generated method then uses ordinary field method calls, so role prerequisites
//! are collected by the same path as a handwritten conditional implementation.

use super::super::*;
use super::synthetic_role_impl::{SyntheticRoleImpl, SyntheticRoleImplMethod};
use super::*;
use crate::{DeriveViaTarget, module_path_site};
use parser::sink::YulangLanguage;
use rowan::SyntaxNode;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum DeriveStrategy {
    Eq,
    Debug,
}

#[derive(Debug)]
struct EqDerivePlan {
    source: String,
}

impl BodyLowerer {
    pub(super) fn lower_derive_requests(&mut self, node: &Cst, decl: &ModuleTypeDecl) {
        let requests = self.modules.derive_requests(decl.id).to_vec();
        for request in requests {
            for role_ref in request.roles {
                let role_name = role_ref.node.text().to_string().trim().to_string();
                let strategy = match self.derive_strategy(&role_ref.node, decl) {
                    Ok(Some(strategy)) => strategy,
                    Ok(None) => {
                        self.errors.push(BodyLoweringError::Derive {
                            diagnostic: DeriveDiagnostic::UnsupportedRole { role: role_name },
                            source: role_ref.span,
                        });
                        continue;
                    }
                    Err(()) => {
                        self.errors.push(BodyLoweringError::Derive {
                            diagnostic: DeriveDiagnostic::UnresolvedRole { role: role_name },
                            source: role_ref.span,
                        });
                        continue;
                    }
                };
                let role = match strategy {
                    DeriveStrategy::Eq => self.canonical_eq_role(decl.module),
                    DeriveStrategy::Debug => self.canonical_debug_role(decl.module),
                };
                let Some(role) = role else {
                    continue;
                };
                let Some(requirements) = self.derive_field_requirements(
                    node,
                    decl,
                    role,
                    &role_name,
                    &role_ref.span,
                    request.via.as_ref(),
                ) else {
                    continue;
                };
                self.pending_derive_requirements.extend(requirements);
                match strategy {
                    DeriveStrategy::Eq => {
                        let Some(plan) = EqDerivePlan::build(node, decl, request.via.as_ref())
                        else {
                            continue;
                        };
                        self.lower_eq_derive_plan(node, decl, request.companion, plan);
                    }
                    DeriveStrategy::Debug => {
                        self.lower_debug_derive_request(
                            node,
                            decl,
                            request.companion,
                            request.via.as_ref(),
                        );
                    }
                }
            }
        }
    }

    fn derive_strategy(
        &self,
        role_ref: &Cst,
        decl: &ModuleTypeDecl,
    ) -> Result<Option<DeriveStrategy>, ()> {
        let mut builder = ann_type_builder(&self.modules, decl.module, decl.order, None);
        let role = builder.build_type_expr(role_ref).map_err(|_| ())?;
        let Some(role) = ann_type_named_head(&role) else {
            return Ok(None);
        };
        if self
            .canonical_eq_role(decl.module)
            .is_some_and(|eq_role| role == eq_role)
        {
            Ok(Some(DeriveStrategy::Eq))
        } else if self
            .canonical_debug_role(decl.module)
            .is_some_and(|debug_role| role == debug_role)
        {
            Ok(Some(DeriveStrategy::Debug))
        } else {
            Ok(None)
        }
    }

    fn derive_field_requirements(
        &mut self,
        node: &Cst,
        decl: &ModuleTypeDecl,
        role: TypeDeclId,
        role_name: &str,
        role_source: &SourceSpan,
        via: Option<&DeriveViaTarget>,
    ) -> Option<Vec<PendingDeriveRequirement>> {
        if !matches!(
            decl.kind,
            ModuleTypeKind::Struct | ModuleTypeKind::Enum | ModuleTypeKind::Error
        ) {
            self.errors.push(BodyLoweringError::Derive {
                diagnostic: DeriveDiagnostic::InvalidTarget {
                    role: role_name.to_string(),
                    target: decl.name.0.clone(),
                },
                source: role_source.clone(),
            });
            return None;
        }
        if let Some(via) = via
            && decl.kind != ModuleTypeKind::Struct
        {
            self.errors.push(BodyLoweringError::Derive {
                diagnostic: DeriveDiagnostic::InvalidViaTarget {
                    target: decl.name.0.clone(),
                },
                source: via.span.clone(),
            });
            return None;
        }

        let role_path = self.modules.type_decl_by_id(role).map(|decl| {
            self.modules
                .type_decl_path(&decl)
                .segments
                .into_iter()
                .map(|name| name.0)
                .collect::<Vec<_>>()
        })?;
        let mut fields = Vec::new();
        match decl.kind {
            ModuleTypeKind::Struct => {
                let struct_fields = crate::struct_field_nodes(node);
                let named = struct_fields
                    .iter()
                    .all(|field| crate::struct_field_name(field).is_some());
                if let Some(via) = via
                    && !named
                {
                    self.errors.push(BodyLoweringError::Derive {
                        diagnostic: DeriveDiagnostic::InvalidViaTarget {
                            target: decl.name.0.clone(),
                        },
                        source: via.span.clone(),
                    });
                    return None;
                }
                for (index, field) in struct_fields.into_iter().enumerate() {
                    let name = crate::struct_field_name(&field)
                        .map(|name| name.0)
                        .unwrap_or_else(|| format!("#{index}"));
                    if let Some(via) = via
                        && name != via.name.0
                    {
                        continue;
                    }
                    let Some(field_type) = crate::field_type_expr(&field) else {
                        continue;
                    };
                    fields.push((name, field, field_type));
                }
                if let Some(via) = via
                    && fields.is_empty()
                {
                    self.errors.push(BodyLoweringError::Derive {
                        diagnostic: DeriveDiagnostic::UnknownField {
                            target: decl.name.0.clone(),
                            field: via.name.0.clone(),
                        },
                        source: via.span.clone(),
                    });
                    return None;
                }
            }
            ModuleTypeKind::Enum | ModuleTypeKind::Error => {
                for variant in crate::enum_variant_nodes(node) {
                    let variant_name = crate::enum_variant_name(&variant)
                        .map(|name| name.0)
                        .unwrap_or_else(|| "<variant>".to_string());
                    let variant_fields = crate::enum_variant_field_nodes(&variant);
                    if variant_fields.is_empty() {
                        fields.extend(
                            crate::enum_variant_direct_type_exprs(&variant)
                                .into_iter()
                                .enumerate()
                                .map(|(index, field_type)| {
                                    (
                                        format!("{variant_name}#{index}"),
                                        field_type.clone(),
                                        field_type,
                                    )
                                }),
                        );
                    } else {
                        for (index, field) in variant_fields.into_iter().enumerate() {
                            let name = crate::struct_field_name(&field)
                                .map(|name| name.0)
                                .unwrap_or_else(|| format!("{variant_name}#{index}"));
                            if let Some(field_type) = crate::field_type_expr(&field) {
                                fields.push((name, field, field_type));
                            }
                        }
                    }
                }
            }
            ModuleTypeKind::TypeAlias | ModuleTypeKind::Role | ModuleTypeKind::Act => {
                unreachable!()
            }
        }

        Some(
            fields
                .into_iter()
                .map(|(field, field_node, field_type)| PendingDeriveRequirement {
                    role: role_path.clone(),
                    role_name: role_name.to_string(),
                    target: decl.name.0.clone(),
                    field,
                    primary_source: via.map_or_else(|| role_source.clone(), |via| via.span.clone()),
                    field_source: SourceSpan {
                        file: role_source.file.clone(),
                        range: crate::node_trimmed_source_range(&field_node),
                    },
                    field_type,
                    module: decl.module,
                    site: decl.order,
                })
                .collect(),
        )
    }

    pub(super) fn validate_pending_derive_requirements(&mut self) {
        let requirements = std::mem::take(&mut self.pending_derive_requirements);
        for requirement in requirements {
            let mut builder =
                ann_type_builder(&self.modules, requirement.module, requirement.site, None);
            let Ok(field_type) = builder.build_type_expr(&requirement.field_type) else {
                continue;
            };
            if ann_type_is_open(&field_type) {
                continue;
            }
            let mut lowerer = AnnConstraintLowerer::new(&mut self.session.infer, &self.modules);
            let Ok(input) = lowerer.lower_role_arg(&field_type) else {
                continue;
            };
            let demand = RoleConstraint {
                role: requirement.role.clone(),
                inputs: vec![input],
                associated: Vec::new(),
            };
            let demand =
                crate::compact::compact_role_constraint(self.session.infer.constraints(), &demand);
            let resolved = crate::role_solve::resolve_role_constraints_with_stats(
                self.session.infer.constraints(),
                &crate::compact::CompactRoot::default(),
                &[demand],
                &self.session.role_impls,
                &FxHashSet::default(),
            );
            let satisfied = match resolved.resolutions.as_slice() {
                [resolution] => resolution.residual_prerequisites.is_empty(),
                [] => resolved.stats.candidate_matches > 0,
                _ => true,
            };
            if !satisfied {
                self.errors.push(BodyLoweringError::Derive {
                    diagnostic: DeriveDiagnostic::UnsatisfiedField {
                        role: requirement.role_name,
                        target: requirement.target,
                        field: requirement.field,
                        field_source: requirement.field_source,
                    },
                    source: requirement.primary_source,
                });
            }
        }
    }

    fn canonical_eq_role(&self, module: ModuleId) -> Option<TypeDeclId> {
        self.modules
            .type_path_at(
                module,
                &names(&["std", "core", "cmp", "Eq"]),
                module_path_site(),
            )
            .filter(|decl| decl.kind == ModuleTypeKind::Role)
            .map(|decl| decl.id)
    }

    pub(super) fn canonical_debug_role(&self, module: ModuleId) -> Option<TypeDeclId> {
        self.modules
            .type_path_at(
                module,
                &names(&["std", "core", "fmt", "Debug"]),
                module_path_site(),
            )
            .filter(|decl| decl.kind == ModuleTypeKind::Role)
            .map(|decl| decl.id)
    }

    fn lower_eq_derive_plan(
        &mut self,
        node: &Cst,
        decl: &ModuleTypeDecl,
        module: ModuleId,
        plan: EqDerivePlan,
    ) {
        let Some(eq_role) = self.canonical_eq_role(decl.module) else {
            return;
        };
        let Some(eq_method) = self
            .modules
            .role_methods(eq_role)
            .iter()
            .find(|method| method.name.0 == "eq")
            .cloned()
        else {
            return;
        };
        if self.modules.role_inputs(eq_role).len() != 1 {
            return;
        }

        let binding = synthetic_binding(&plan.source).ok_or(LoweringError::UnsupportedSyntax {
            kind: SyntaxKind::Binding,
        });
        let role_associated = self.modules.role_associated(eq_role).to_vec();
        let type_vars = crate::type_var_names(node);
        let mut builder = ann_type_builder(&self.modules, module, module_path_site(), None);
        let target_ann = builder.type_decl_application(decl.id, &type_vars);
        let input_anns = vec![target_ann.clone()];
        let associated_anns = role_associated
            .iter()
            .map(|name| {
                (
                    name.clone(),
                    AnnType::Var(builder.ann_type_var_for_role(name)),
                )
            })
            .collect::<Vec<_>>();
        let type_var_bindings = builder.type_var_bindings();
        let _ = self.lower_synthetic_role_impl(SyntheticRoleImpl {
            role: eq_role,
            module,
            site: module_path_site(),
            target_ann,
            input_anns,
            associated_anns,
            type_var_bindings,
            prerequisites: Vec::new(),
            methods: vec![SyntheticRoleImplMethod {
                name: eq_method.name,
                receiver: Some(Name("__derive_left".into())),
                vis: Vis::Our,
                label: format!("{}::eq#derive", decl.name.0),
                binding: binding.as_ref().map_err(Clone::clone),
            }],
        });
    }
}

impl EqDerivePlan {
    fn build(node: &Cst, decl: &ModuleTypeDecl, via: Option<&DeriveViaTarget>) -> Option<Self> {
        let source = match decl.kind {
            ModuleTypeKind::Struct => eq_struct_source(node, via)?,
            ModuleTypeKind::Enum | ModuleTypeKind::Error => {
                via.is_none().then(|| eq_sum_source(node))?
            }
            ModuleTypeKind::TypeAlias | ModuleTypeKind::Role | ModuleTypeKind::Act => return None,
        };
        Some(Self { source })
    }
}

fn eq_struct_source(node: &Cst, via: Option<&DeriveViaTarget>) -> Option<String> {
    let fields = crate::struct_field_nodes(node);
    let named_fields = fields
        .iter()
        .map(crate::struct_field_name)
        .collect::<Option<Vec<_>>>();

    if let Some(fields) = named_fields {
        let compared = match via {
            Some(via) => vec![fields.iter().find(|field| **field == via.name)?.clone()],
            None => fields,
        };
        let comparisons = compared
            .iter()
            .map(|field| format!("__derive_left.{}.eq __derive_right.{}", field.0, field.0))
            .collect::<Vec<_>>();
        return Some(format!(
            "our __derive_left.eq __derive_right = {}\n",
            short_circuit_eq(&comparisons)
        ));
    }

    // `via` has no positional form, so tuple structs are left for DERIVE-F to diagnose.
    if via.is_some() {
        return None;
    }
    let constructor = crate::type_decl_name(node)?;
    let arity = fields.len();
    if arity == 0 {
        return Some("our __derive_left.eq __derive_right = true\n".into());
    }
    let left = derive_payload_names("left", arity);
    let right = derive_payload_names("right", arity);
    let comparisons = left
        .iter()
        .zip(&right)
        .map(|(left, right)| format!("{left}.eq {right}"))
        .collect::<Vec<_>>();
    Some(format!(
        "our __derive_left.eq __derive_right = case (__derive_left, __derive_right):\n    ({} ({}), {} ({})) -> {}\n    _ -> false\n",
        constructor.0,
        left.join(", "),
        constructor.0,
        right.join(", "),
        short_circuit_eq(&comparisons),
    ))
}

fn eq_sum_source(node: &Cst) -> String {
    let mut source =
        "our __derive_left.eq __derive_right = case (__derive_left, __derive_right):\n".to_string();
    for (variant_index, variant) in crate::enum_variant_nodes(node).iter().enumerate() {
        let Some(name) = crate::enum_variant_name(variant) else {
            continue;
        };
        let fields = crate::enum_variant_field_nodes(variant);
        let direct = crate::enum_variant_direct_type_exprs(variant);
        let arity = fields.len().max(direct.len());
        let left = derive_payload_names(&format!("{variant_index}_left"), arity);
        let right = derive_payload_names(&format!("{variant_index}_right"), arity);
        let comparisons = left
            .iter()
            .zip(&right)
            .map(|(left, right)| format!("{left}.eq {right}"))
            .collect::<Vec<_>>();
        let (left_pattern, right_pattern) = if fields.is_empty() {
            (
                constructor_pattern(&name.0, &left),
                constructor_pattern(&name.0, &right),
            )
        } else {
            (
                record_constructor_pattern(&name.0, &fields, &left),
                record_constructor_pattern(&name.0, &fields, &right),
            )
        };
        source.push_str(&format!(
            "    ({left_pattern}, {right_pattern}) -> {}\n",
            short_circuit_eq(&comparisons)
        ));
    }
    source.push_str("    _ -> false\n");
    source
}

fn short_circuit_eq(comparisons: &[String]) -> String {
    match comparisons {
        [] => "true".into(),
        [comparison] => comparison.clone(),
        [comparison, rest @ ..] => {
            format!("if {comparison}: {} else: false", short_circuit_eq(rest))
        }
    }
}

fn constructor_pattern(name: &str, payloads: &[String]) -> String {
    match payloads {
        [] => name.into(),
        [payload] => format!("{name} {payload}"),
        _ => format!("{name} ({})", payloads.join(", ")),
    }
}

fn record_constructor_pattern(name: &str, fields: &[Cst], payloads: &[String]) -> String {
    let bindings = fields
        .iter()
        .zip(payloads)
        .filter_map(|(field, payload)| {
            crate::struct_field_name(field).map(|name| format!("{}: {payload}", name.0))
        })
        .collect::<Vec<_>>();
    format!("{name} {{ {} }}", bindings.join(", "))
}

fn derive_payload_names(prefix: &str, arity: usize) -> Vec<String> {
    (0..arity)
        .map(|index| format!("__derive_{prefix}_{index}"))
        .collect()
}

fn ann_type_named_head(ann: &AnnType) -> Option<TypeDeclId> {
    match ann {
        AnnType::Named(id) => Some(*id),
        AnnType::Apply { callee, .. } => ann_type_named_head(callee),
        _ => None,
    }
}

fn ann_type_is_open(ann: &AnnType) -> bool {
    match ann {
        AnnType::Builtin(_) | AnnType::Named(_) => false,
        AnnType::Var(_) | AnnType::Wildcard(_) => true,
        AnnType::EffectRow(row) => {
            row.tail.is_some()
                || row.items.iter().any(|atom| match atom {
                    AnnEffectAtom::Type(ann) => ann_type_is_open(ann),
                    AnnEffectAtom::Wildcard => true,
                })
        }
        AnnType::Effectful { eff, ret } => {
            ann_type_is_open(&AnnType::EffectRow(eff.clone())) || ann_type_is_open(ret)
        }
        AnnType::Tuple(items) => items.iter().any(ann_type_is_open),
        AnnType::Apply { callee, args } => {
            ann_type_is_open(callee) || args.iter().any(ann_type_is_open)
        }
        AnnType::Function {
            param,
            arg_eff,
            ret_eff,
            ret,
        } => {
            ann_type_is_open(param)
                || arg_eff
                    .as_ref()
                    .is_some_and(|row| ann_type_is_open(&AnnType::EffectRow(row.clone())))
                || ret_eff
                    .as_ref()
                    .is_some_and(|row| ann_type_is_open(&AnnType::EffectRow(row.clone())))
                || ann_type_is_open(ret)
        }
    }
}

pub(super) fn names(segments: &[&str]) -> Vec<Name> {
    segments
        .iter()
        .map(|segment| Name((*segment).to_string()))
        .collect()
}

pub(super) fn synthetic_binding(source: &str) -> Option<Cst> {
    let root = SyntaxNode::<YulangLanguage>::new_root(parser::parse_module_to_green(source));
    root.children()
        .find(|node| node.kind() == SyntaxKind::Binding)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pair_derive_registers_one_exact_eq_prerequisite() {
        let source = concat!(
            "mod std:\n",
            "  pub mod core:\n",
            "    pub mod cmp:\n",
            "      pub role Eq 'a:\n",
            "        pub a.eq: 'a -> bool\n",
            "  pub mod control:\n",
            "    pub mod junction:\n",
            "      pub mod junction:\n",
            "        pub junction x = x\n",
            "struct pair 'a { l: 'a, r: 'a } derives std::core::cmp::Eq\n",
        );
        let root = SyntaxNode::new_root(parser::parse_module_to_green(source));
        let lower = crate::lower_module_map(&root);
        let output = crate::lowering::lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let candidates = output.session.poly.role_impls.candidates(&[
            "std".into(),
            "core".into(),
            "cmp".into(),
            "Eq".into(),
        ]);
        assert_eq!(candidates.len(), 1);
        let candidate = &candidates[0];
        assert_eq!(candidate.prerequisites.len(), 1);
        let prerequisite = &candidate.prerequisites[0];
        assert_eq!(prerequisite.role, vec!["std", "core", "cmp", "Eq"]);
        assert_eq!(prerequisite.inputs.len(), 1);
        assert_eq!(
            poly::dump::format_pos(&output.session.poly.typ, prerequisite.inputs[0].lower),
            "'a"
        );
    }
}
