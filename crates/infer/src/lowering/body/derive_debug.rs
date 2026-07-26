//! Structural `Debug` derivation for nominal algebraic declarations.
//!
//! The generated implementation calls each rendered value's ordinary `debug`
//! method. That keeps field prerequisites on the same lowering path as a
//! handwritten conditional implementation and never asks the VM to format a
//! structural value.

use super::super::*;
use super::derive_eq::synthetic_binding;
use super::synthetic_role_impl::{SyntheticRoleImpl, SyntheticRoleImplMethod};
use super::*;
use crate::{DeriveViaTarget, module_path_site};

#[derive(Debug)]
struct DebugDerivePlan {
    source: String,
}

impl BodyLowerer {
    pub(super) fn lower_debug_derive_request(
        &mut self,
        node: &Cst,
        decl: &ModuleTypeDecl,
        module: ModuleId,
        via: Option<&DeriveViaTarget>,
    ) {
        let Some(plan) = DebugDerivePlan::build(node, decl, via) else {
            // DERIVE-F owns diagnostics for invalid derive targets and `via` targets.
            return;
        };
        self.lower_debug_derive_plan(node, decl, module, plan);
    }

    fn lower_debug_derive_plan(
        &mut self,
        node: &Cst,
        decl: &ModuleTypeDecl,
        module: ModuleId,
        plan: DebugDerivePlan,
    ) {
        let Some(debug_role) = self.canonical_debug_role(decl.module) else {
            return;
        };
        let Some(debug_method) = self
            .modules
            .role_methods(debug_role)
            .iter()
            .find(|method| method.name.0 == "debug")
            .cloned()
        else {
            return;
        };
        if self.modules.role_inputs(debug_role).len() != 1 {
            return;
        }

        let binding = synthetic_binding(&plan.source).ok_or(LoweringError::UnsupportedSyntax {
            kind: SyntaxKind::Binding,
        });
        let role_associated = self.modules.role_associated(debug_role).to_vec();
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
            role: debug_role,
            module,
            site: module_path_site(),
            target_ann,
            input_anns,
            associated_anns,
            type_var_bindings,
            prerequisites: Vec::new(),
            methods: vec![SyntheticRoleImplMethod {
                name: debug_method.name,
                receiver: Some(Name("__derive_debug".into())),
                vis: Vis::Our,
                label: format!("{}::debug#derive", decl.name.0),
                binding: binding.as_ref().map_err(Clone::clone),
            }],
        });
    }
}

impl DebugDerivePlan {
    fn build(node: &Cst, decl: &ModuleTypeDecl, via: Option<&DeriveViaTarget>) -> Option<Self> {
        let source = match decl.kind {
            ModuleTypeKind::Struct => debug_struct_source(node, via)?,
            ModuleTypeKind::Enum | ModuleTypeKind::Error => {
                via.is_none().then(|| debug_sum_source(node, decl))?
            }
            ModuleTypeKind::TypeAlias | ModuleTypeKind::Role | ModuleTypeKind::Act => return None,
        };
        Some(Self { source })
    }
}

fn debug_struct_source(node: &Cst, via: Option<&DeriveViaTarget>) -> Option<String> {
    let type_name = crate::type_decl_name(node)?;
    let fields = crate::struct_field_nodes(node);
    let named_fields = fields
        .iter()
        .map(crate::struct_field_name)
        .collect::<Option<Vec<_>>>();

    if let Some(fields) = named_fields {
        if let Some(via) = via {
            let field = fields.iter().find(|field| **field == via.name)?;
            return Some(format!(
                "our __derive_debug.debug = __derive_debug.{}.debug\n",
                field.0
            ));
        }
        if fields.is_empty() {
            return Some(format!(
                "our __derive_debug.debug = \"{} {{ }}\"\n",
                type_name.0
            ));
        }
        let rendered = fields
            .iter()
            .map(|field| (field.0.clone(), format!("__derive_debug.{}.debug", field.0)))
            .collect::<Vec<_>>();
        return Some(format!(
            "our __derive_debug.debug = {}\n",
            debug_record_text(&type_name.0, &rendered),
        ));
    }

    // `via` has no positional form, so tuple structs are left for DERIVE-F to diagnose.
    if via.is_some() {
        return None;
    }
    let payloads = derive_payload_names("tuple", fields.len());
    let pattern = constructor_pattern(&type_name.0, &payloads);
    let rendered = debug_text_join(
        &payloads
            .iter()
            .map(|name| format!("{name}.debug"))
            .collect::<Vec<_>>(),
        ", ",
    );
    Some(format!(
        "our __derive_debug.debug = case __derive_debug:\n    {pattern} -> \"{}(\" + {rendered} + \")\"\n",
        type_name.0,
    ))
}

fn debug_sum_source(node: &Cst, decl: &ModuleTypeDecl) -> String {
    let mut source = "our __derive_debug.debug = case __derive_debug:\n".to_string();
    for (variant_index, variant) in crate::enum_variant_nodes(node).iter().enumerate() {
        let Some(name) = crate::enum_variant_name(variant) else {
            continue;
        };
        let fields = crate::enum_variant_field_nodes(variant);
        let direct = crate::enum_variant_direct_type_exprs(variant);
        let arity = fields.len().max(direct.len());
        let payloads = derive_payload_names(&format!("{variant_index}_payload"), arity);
        let type_and_variant = format!("{}::{}", decl.name.0, name.0);
        if fields.is_empty() {
            let pattern = constructor_pattern(&name.0, &payloads);
            let rendered = debug_text_join(
                &payloads
                    .iter()
                    .map(|payload| format!("{payload}.debug"))
                    .collect::<Vec<_>>(),
                ", ",
            );
            let text = if payloads.is_empty() {
                format!("\"{type_and_variant}\"")
            } else {
                format!("\"{type_and_variant}(\" + {rendered} + \")\"")
            };
            source.push_str(&format!("    {pattern} -> {text}\n"));
        } else {
            let pattern = record_constructor_pattern(&name.0, &fields, &payloads);
            let rendered = fields
                .iter()
                .zip(&payloads)
                .filter_map(|(field, payload)| {
                    crate::struct_field_name(field)
                        .map(|field| (field.0, format!("{payload}.debug")))
                })
                .collect::<Vec<_>>();
            source.push_str(&format!(
                "    {pattern} -> {}\n",
                debug_record_text(&type_and_variant, &rendered),
            ));
        }
    }
    source
}

fn debug_text_join(parts: &[String], separator: &str) -> String {
    match parts {
        [] => "\"\"".into(),
        [part] => part.clone(),
        [part, rest @ ..] => format!(
            "{part} + \"{separator}\" + {}",
            debug_text_join(rest, separator)
        ),
    }
}

fn debug_record_text(head: &str, fields: &[(String, String)]) -> String {
    let Some((first_name, first_value)) = fields.first() else {
        return format!("\"{head} {{ }}\"");
    };
    let mut text = format!("\"{head} {{ {first_name}: \" + {first_value}");
    for (name, value) in &fields[1..] {
        text.push_str(&format!(" + \", {name}: \" + {value}"));
    }
    text.push_str(" + \" }\"");
    text
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

#[cfg(test)]
mod tests {
    use rowan::SyntaxNode;

    #[test]
    fn pair_derive_registers_one_exact_debug_prerequisite_and_only_debug_method() {
        let source = concat!(
            "mod std:\n",
            "  pub mod text:\n",
            "    pub mod str:\n",
            "      pub type str\n",
            "  pub mod core:\n",
            "    pub mod fmt:\n",
            "      use std::text::str::str\n",
            "      pub role Debug 'a:\n",
            "        pub a.debug: str\n",
            "        pub a.dd = a.debug\n",
            "  pub mod control:\n",
            "    pub mod junction:\n",
            "      pub mod junction:\n",
            "        pub junction x = x\n",
            "pub infix (+) 5.0.0 5.0.1 = \\x -> \\y -> x\n",
            "use std::core::fmt::*\n",
            "struct pair 'a { l: 'a, r: 'a } derives std::core::fmt::Debug\n",
        );
        let root = SyntaxNode::new_root(parser::parse_module_to_green(source));
        let lower = crate::lower_module_map(&root);
        let output = crate::lowering::lower_binding_bodies(&root, lower);

        assert!(output.errors.is_empty(), "{:?}", output.errors);
        let candidates = output.session.poly.role_impls.candidates(&[
            "std".into(),
            "core".into(),
            "fmt".into(),
            "Debug".into(),
        ]);
        assert_eq!(candidates.len(), 1);
        let candidate = &candidates[0];
        assert_eq!(candidate.methods.len(), 1);
        assert_eq!(candidate.prerequisites.len(), 1, "{candidate:#?}");
        let prerequisite = &candidate.prerequisites[0];
        assert_eq!(prerequisite.role, vec!["std", "core", "fmt", "Debug"]);
        assert_eq!(prerequisite.inputs.len(), 1);
        assert_eq!(
            poly::dump::format_pos(&output.session.poly.typ, prerequisite.inputs[0].lower),
            "'a"
        );
    }
}
