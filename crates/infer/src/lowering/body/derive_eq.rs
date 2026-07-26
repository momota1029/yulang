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
enum DeriveStrategy {
    Eq,
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
                if self.derive_strategy(&role_ref.node, decl) != Some(DeriveStrategy::Eq) {
                    // DERIVE-F owns diagnostics for unresolved and unsupported roles.
                    continue;
                }
                let Some(plan) = EqDerivePlan::build(node, decl, request.via.as_ref()) else {
                    // DERIVE-F owns diagnostics for invalid derive targets and `via` targets.
                    continue;
                };
                self.lower_eq_derive_plan(node, decl, request.companion, plan);
            }
        }
    }

    fn derive_strategy(&self, role_ref: &Cst, decl: &ModuleTypeDecl) -> Option<DeriveStrategy> {
        let mut builder = ann_type_builder(&self.modules, decl.module, decl.order, None);
        let role = builder.build_type_expr(role_ref).ok()?;
        let role = ann_type_named_head(&role)?;
        (role == self.canonical_eq_role(decl.module)?).then_some(DeriveStrategy::Eq)
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

fn names(segments: &[&str]) -> Vec<Name> {
    segments
        .iter()
        .map(|segment| Name((*segment).to_string()))
        .collect()
}

fn synthetic_binding(source: &str) -> Option<Cst> {
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
