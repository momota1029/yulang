use std::collections::HashSet;

use super::*;

#[test]
fn source_application_provenance_uses_cst_ranges_across_binding_renames() {
    let mut observed_application_ranges = Vec::new();

    for binding in ["a", "some_longer_name"] {
        let source = format!("my {binding} = 1 2\n");
        let (root, output, module, source_file) = lower_application_canary(&source);
        let source_expr = binding_expr(&root, binding);
        let (def, _) = binding_def_and_order(&output.modules, module, binding);
        let body = binding_body_id(&output, def);
        let provenance = output
            .application_provenance()
            .get(body)
            .expect("surface application should own provenance");

        assert_eq!(provenance.origin, ApplicationOrigin::Source);
        assert_eq!(provenance.module, module);
        assert_eq!(provenance.application_span.file, source_file);
        assert_eq!(provenance.callee_span.file, source_file);
        assert_eq!(
            provenance.application_span.range,
            crate::node_source_range(&source_expr)
        );
        assert_eq!(
            provenance.callee_span.range,
            expression_head_source_range(&source_expr)
        );

        observed_application_ranges.push(provenance.application_span.range);
    }

    assert_ne!(
        observed_application_ranges[0], observed_application_ranges[1],
        "renaming moves the CST-derived range instead of retaining a copied offset"
    );
}

#[test]
fn multi_argument_call_records_each_cumulative_source_application() {
    let source = "type list 'a\nmy f x y z = x\nmy generated = [1, 2]\nmy result = f 1 2 3\n";
    let (root, output, module, source_file) = lower_application_canary(source);
    let source_expr = binding_expr(&root, "result");
    let (def, _) = binding_def_and_order(&output.modules, module, "result");
    let body = binding_body_id(&output, def);

    let mut applications = Vec::new();
    let mut current = body;
    while let poly::expr::Expr::App(callee, _) = output.session.poly.expr(current) {
        applications.push(current);
        current = *callee;
    }
    applications.reverse();
    assert_eq!(applications.len(), 3);

    let table = output.application_provenance();
    assert_eq!(table.iter().count(), 3);
    let (generated_def, _) = binding_def_and_order(&output.modules, module, "generated");
    let generated_body = binding_body_id(&output, generated_def);
    assert!(matches!(
        output.session.poly.expr(generated_body),
        poly::expr::Expr::App(_, _)
    ));
    assert_eq!(
        table.get(generated_body),
        None,
        "desugared applications are explicitly unowned"
    );
    let provenance = applications
        .iter()
        .map(|expr| {
            table
                .get(*expr)
                .expect("each source application in the chain should own provenance")
        })
        .collect::<Vec<_>>();

    let distinct_ranges = provenance
        .iter()
        .map(|provenance| provenance.application_span.range)
        .collect::<HashSet<_>>();
    assert_eq!(distinct_ranges.len(), 3);
    assert_eq!(
        provenance[0].callee_span.range,
        expression_head_source_range(&source_expr)
    );
    for pair in provenance.windows(2) {
        assert_eq!(pair[1].callee_span, pair[0].application_span);
    }
    assert_eq!(
        provenance.last().unwrap().application_span.range,
        crate::node_source_range(&source_expr)
    );
    assert!(provenance.iter().all(|provenance| {
        provenance.origin == ApplicationOrigin::Source
            && provenance.module == module
            && provenance.application_span.file == source_file
            && provenance.callee_span.file == source_file
    }));
}

fn lower_application_canary(source: &str) -> (Cst, BodyLowering, ModuleId, sources::Path) {
    let source_file = sources::Path {
        segments: vec![sources::Name("canary".to_string())],
    };
    let loaded = sources::load(vec![
        sources::SourceFile {
            module_path: sources::Path::default(),
            source: "mod canary;\n".to_string(),
        },
        sources::SourceFile {
            module_path: source_file.clone(),
            source: source.to_string(),
        },
    ]);
    let root = loaded
        .iter()
        .find(|file| file.module_path == source_file)
        .map(|file| SyntaxNode::new_root(file.cst.clone()))
        .expect("canary source CST");
    assert_eq!(root.text().to_string(), source);

    let output = lower_loaded_files(&loaded).expect("lower application canary");
    let module = output
        .modules
        .module_by_path(&source_file)
        .expect("canary module");
    (root, output, module, source_file)
}

fn expression_head_source_range(expr: &Cst) -> SourceRange {
    let head = expr
        .children_with_tokens()
        .find(|item| !item_is_trivia(item))
        .expect("application source expression head");
    item_source_range(&head)
}
