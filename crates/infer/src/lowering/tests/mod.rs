//! Regression tests for body lowering.

use super::*;
use crate::lower_module_map;
use crate::scc::SccEvent;
use poly::expr::{
    DefId, ExprId, Pat, PrimitiveOp, RecordSpread, RefId, SelectId, SelectResolution, Vis,
};

fn parse(src: &str) -> Cst {
    SyntaxNode::new_root(parser::parse_module_to_green(src))
}

fn parse_with_junction_std(src: &str) -> Cst {
    parse(&format!(
        "mod std:\n  pub mod control:\n    pub mod junction:\n      pub mod junction:\n        pub junction x = x\n{src}"
    ))
}

fn parse_with_text_parse_std(src: &str) -> Cst {
    parse(&format!(
        "mod std:\n  pub mod text:\n    pub mod parse:\n      pub token expected = expected\n      pub word() = 0\n      pub choice p q = p\n      pub many p = p\n      pub some p = p\n      pub optional p = p\n{src}"
    ))
}

fn lower_with_text_yumark_std(src: &str) -> (Cst, Lower) {
    let source = text_yumark_std_source(src);
    let root = parse(&source);
    let lower = crate::module_map::lower_module_map_with_source(&root, &source);
    (root, lower)
}

fn text_yumark_std_source(src: &str) -> String {
    format!(
        concat!(
            "mod std:\n",
            "  pub mod text:\n",
            "    pub mod str:\n",
            "      pub type str\n",
            "    pub mod yumark:\n",
            "      pub nil format algebra = algebra\n",
            "      pub cons head tail format algebra = algebra\n",
            "      pub text value format algebra = algebra\n",
            "      pub paragraph children format algebra = algebra\n",
            "      pub heading marker level children format algebra = algebra\n",
            "      pub blank_line marker format algebra = algebra\n",
            "      pub section_close marker children format algebra = algebra\n",
            "      pub list_block ordered items format algebra = algebra\n",
            "      pub list_item marker children format algebra = algebra\n",
            "      pub list_item_body children format algebra = algebra\n",
            "      pub code_fence info body format algebra = algebra\n",
            "      pub quote_block children format algebra = algebra\n",
            "      pub emphasis children format algebra = algebra\n",
            "      pub strong children format algebra = algebra\n",
            "{}",
        ),
        src
    )
}

fn parse_with_flow_loop_std(src: &str) -> Cst {
    parse(&format!(
        "mod std:\n  pub mod control:\n    pub mod flow:\n      pub act loop:\n        pub for_in xs f = f xs\n{src}"
    ))
}

fn parse_with_flow_loop_and_label_std(src: &str) -> Cst {
    parse(&format!(
        concat!(
            "mod std:\n",
            "  pub mod control:\n",
            "    pub mod flow:\n",
            "      pub act loop:\n",
            "        pub for_in xs f = f xs\n",
            "      pub act label_loop:\n",
            "        pub label = 0\n",
            "        pub for_in xs f = f label xs\n",
            "{}"
        ),
        src
    ))
}

fn parse_with_text_str_std(src: &str) -> Cst {
    parse(&format!(
        "mod std:\n  pub mod text:\n    pub mod str:\n      pub concat a b = a\n{src}"
    ))
}

fn parse_with_text_str_and_format_std(src: &str) -> Cst {
    let mut full = concat!(
        "mod std:\n",
        "  pub mod data:\n",
        "    pub mod opt:\n",
        "      pub enum opt 'a = nil | just 'a\n",
        "  pub mod core:\n",
        "    pub mod fmt:\n",
        "      use std::data::opt::*\n",
        "      pub enum format_kind = display | debug | lower_hex | upper_hex\n",
        "      pub enum format_align = left | right | center\n",
        "      pub enum format_sign = plus | minus\n",
        "      pub struct format_spec {\n",
        "        kind: format_kind,\n",
        "        align: opt format_align,\n",
        "        sign: opt format_sign,\n",
        "        fill: opt str,\n",
        "        width: opt int,\n",
        "        precision: opt int,\n",
        "        alternate: bool,\n",
        "        zero_pad: bool,\n",
        "      }\n",
        "      pub format_display spec value = value\n",
        "      pub format_debug spec value = value\n",
        "      pub format_lower_hex spec value = value\n",
        "      pub format_upper_hex spec value = value\n",
        "  pub mod text:\n",
        "    pub mod str:\n",
        "      pub concat a b = a\n",
    )
    .to_string();
    full.push_str(src);
    parse(&full)
}

fn binding_expr(root: &Cst, name: &str) -> Cst {
    binding_node(root, name)
        .and_then(|binding| binding_body_expr(&binding))
        .expect("binding body expr")
}

fn binding_node(root: &Cst, name: &str) -> Option<Cst> {
    root.children().find(|child| {
        child.kind() == SyntaxKind::Binding && binding_name(child).as_deref() == Some(name)
    })
}

fn binding_name(binding: &Cst) -> Option<String> {
    binding
        .children()
        .find(|child| child.kind() == SyntaxKind::BindingHeader)?
        .children()
        .find(|child| child.kind() == SyntaxKind::Pattern)?
        .children_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.kind() == SyntaxKind::Ident)
        .map(|token| token.text().to_string())
}

fn binding_def_and_order(
    modules: &ModuleTable,
    module: ModuleId,
    name: &str,
) -> (DefId, ModuleOrder) {
    let decl = modules.value_decls(module, &Name(name.into()))[0].clone();
    (decl.def, decl.order)
}

fn std_junction_def(modules: &ModuleTable) -> DefId {
    let path = crate::std_paths::control_junction_value()
        .into_iter()
        .map(Name)
        .collect::<Vec<_>>();
    modules
        .value_path_at(modules.root_id(), &path, ModuleOrder::from_index(u32::MAX))
        .expect("std junction value")
}

fn text_parse_def(modules: &ModuleTable, name: &str) -> DefId {
    let path = crate::std_paths::text_parse_value(name)
        .into_iter()
        .map(Name)
        .collect::<Vec<_>>();
    modules
        .value_path_at(modules.root_id(), &path, ModuleOrder::from_index(u32::MAX))
        .unwrap_or_else(|| panic!("std text parse value {name}"))
}

fn text_yumark_def(modules: &ModuleTable, name: &str) -> DefId {
    let path = crate::std_paths::text_yumark_value(name)
        .into_iter()
        .map(Name)
        .collect::<Vec<_>>();
    modules
        .value_path_at(modules.root_id(), &path, ModuleOrder::from_index(u32::MAX))
        .unwrap_or_else(|| panic!("std text yumark value {name}"))
}

fn control_flow_loop_for_in_def(modules: &ModuleTable) -> DefId {
    let path = crate::std_paths::control_flow_loop_for_in_value()
        .into_iter()
        .map(Name)
        .collect::<Vec<_>>();
    modules
        .value_path_at(modules.root_id(), &path, ModuleOrder::from_index(u32::MAX))
        .expect("std control flow loop for_in")
}

fn control_flow_label_loop_for_in_def(modules: &ModuleTable) -> DefId {
    let path = crate::std_paths::control_flow_label_loop_for_in_value()
        .into_iter()
        .map(Name)
        .collect::<Vec<_>>();
    modules
        .value_path_at(modules.root_id(), &path, ModuleOrder::from_index(u32::MAX))
        .expect("std control flow label_loop for_in")
}

fn text_str_concat_def(modules: &ModuleTable) -> DefId {
    let path = crate::std_paths::text_str_concat_value()
        .into_iter()
        .map(Name)
        .collect::<Vec<_>>();
    modules
        .value_path_at(modules.root_id(), &path, ModuleOrder::from_index(u32::MAX))
        .expect("std text str concat")
}

fn core_fmt_def(modules: &ModuleTable, name: &str) -> DefId {
    let path = crate::std_paths::core_fmt_value(name)
        .into_iter()
        .map(Name)
        .collect::<Vec<_>>();
    modules
        .value_path_at(modules.root_id(), &path, ModuleOrder::from_index(u32::MAX))
        .unwrap_or_else(|| panic!("std core fmt value {name}"))
}

fn core_fmt_format_sign_def(modules: &ModuleTable, name: &str) -> DefId {
    let path = crate::std_paths::core_fmt_format_sign_value(name)
        .into_iter()
        .map(Name)
        .collect::<Vec<_>>();
    modules
        .value_path_at(modules.root_id(), &path, ModuleOrder::from_index(u32::MAX))
        .unwrap_or_else(|| panic!("std core fmt format_sign value {name}"))
}

fn assert_junction_app(session: &AnalysisSession, expr: ExprId, junction: DefId) -> ExprId {
    match session.poly.expr(expr) {
        Expr::App(callee, arg) => {
            let reference = expr_ref(session, *callee);
            assert_eq!(session.poly.ref_target(reference), Some(junction));
            *arg
        }
        _ => panic!("expected junction application"),
    }
}

fn binding_body_id(output: &BodyLowering, def: DefId) -> ExprId {
    match output.session.poly.defs.get(def) {
        Some(Def::Let {
            body: Some(body), ..
        }) => *body,
        _ => panic!("expected lowered let body"),
    }
}

fn def_scheme(output: &BodyLowering, def: DefId) -> &poly::types::Scheme {
    match output.session.poly.defs.get(def) {
        Some(Def::Let {
            scheme: Some(scheme),
            ..
        }) => scheme,
        _ => panic!("expected def scheme"),
    }
}

fn local_effect_item_fragment<'a>(rendered: &'a str, family_prefix: &str) -> Option<&'a str> {
    let start = rendered.find(family_prefix)?;
    let rest = &rendered[start..];
    let end = rest.find([';', ']']).unwrap_or(rest.len());
    Some(&rest[..end])
}

fn build_neg_signature_field_type(src: &str, type_name: &str, field_name: &str) -> SignatureType {
    let root = parse(src);
    let lower = lower_module_map(&root);
    let module = lower.modules.root_id();
    let expected_type_name = Name(type_name.into());
    let expected_field_name = Name(field_name.into());
    let owner_decl = lower.modules.type_decls(module, &expected_type_name)[0].clone();
    let struct_decl = root
        .children()
        .find(|child| {
            child.kind() == SyntaxKind::StructDecl
                && crate::type_decl_name(child).as_ref() == Some(&expected_type_name)
        })
        .expect("struct declaration should exist");
    let type_vars = crate::type_var_names(&struct_decl);
    let type_expr = crate::struct_field_nodes(&struct_decl)
        .into_iter()
        .find(|field| crate::struct_field_name(field).as_ref() == Some(&expected_field_name))
        .and_then(|field| crate::field_type_expr(&field))
        .expect("field should contain a type expression");
    let builder = NegSignatureBuilder::with_self_alias(
        &lower.modules,
        module,
        owner_decl.order,
        SignatureSelfAlias {
            owner: owner_decl.id,
            type_vars,
        },
    );
    builder
        .build_type_expr(&type_expr)
        .expect("negative signature should build")
        .signature
}

mod application_provenance;
mod case_01;
mod case_02;
mod case_03;
mod case_04;
mod case_05;
mod case_06;
mod case_07;
mod ordinary_cast_characterization;

use case_01::{
    assert_act_method_receiver_has_self_subtract, assert_method_body_is_receiver_identity,
    assert_pos_stack_pop_var, find_pos_or_var_lower_stack_pop_var, function_lower_bound,
    role_arg_vars, type_field_method, weight_has_empty_stack,
};
use case_06::{
    assert_neg_bottom, assert_role_arg_is_exact_con, assert_var_has_exact_con_bound,
    assert_var_has_lower_con_bound, assert_var_has_lower_con_path, expr_ref, find_select_by_name,
    function_result_effect, lambda_body, lambda_output, recursive_self_block_parts,
};
