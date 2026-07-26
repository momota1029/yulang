use super::synthetic_role_impl::{SyntheticRoleImpl, SyntheticRoleImplMethod};
use super::*;
use crate::module_path_site;

#[test]
fn synthetic_role_impl_reaches_final_poly_with_method_and_residual_prerequisite() {
    let root = SyntaxNode::new_root(parser::parse_module_to_green(
        "role Eq 'a:\n  our x.eq: unit\nrole Box 'a:\n  our x.get: unit\n",
    ));
    let lower = crate::lower_module_map(&root);
    let module = lower.modules.root_id();
    let binding_root = SyntaxNode::new_root(parser::parse_module_to_green("our x.get = x.eq\n"));
    let binding = binding_root
        .children()
        .find(|child| child.kind() == SyntaxKind::Binding)
        .expect("test source has one synthetic method binding");
    let box_role = lower
        .modules
        .lexical_type_at(module, &Name("Box".into()), module_path_site())
        .expect("Box role resolves");
    let requirement = lower.modules.role_methods(box_role.id)[0].def;

    let mut lowerer = BodyLowerer::new(lower);
    lowerer.lower_block(&root, module);
    let mut builder = ann_type_builder(&lowerer.modules, module, module_path_site(), None);
    let target_ann = AnnType::Var(builder.ann_type_var_for_role("synthetic_item"));
    let result = lowerer
        .lower_synthetic_role_impl(SyntheticRoleImpl {
            role: box_role.id,
            module,
            site: module_path_site(),
            target_ann: target_ann.clone(),
            input_anns: vec![target_ann],
            associated_anns: Vec::new(),
            type_var_bindings: builder.type_var_bindings(),
            methods: vec![SyntheticRoleImplMethod {
                name: Name("get".into()),
                receiver: Some(Name("x".into())),
                vis: Vis::Our,
                label: "synthetic::get#test".into(),
                binding: Ok(&binding),
            }],
        })
        .expect("synthetic role impl lowers");
    lowerer.drain_analysis_with_conformance();
    lowerer
        .session
        .resolve_unresolved_selections_as_record_fields();
    let output = lowerer.finish();

    assert!(output.errors.is_empty(), "{:?}", output.errors);
    let candidates = output
        .session
        .poly
        .role_impls
        .candidates(&["Box".to_string()]);
    assert_eq!(candidates.len(), 1);
    let candidate = &candidates[0];
    assert_eq!(candidate.impl_def, Some(result.impl_def));
    assert_eq!(candidate.methods.len(), 1);
    assert_eq!(candidate.methods[0].requirement, requirement);
    assert_eq!(candidate.methods[0].implementation, result.method_defs[0]);
    assert_eq!(candidate.prerequisites.len(), 1);
    assert_eq!(candidate.prerequisites[0].role, vec!["Eq".to_string()]);
}
