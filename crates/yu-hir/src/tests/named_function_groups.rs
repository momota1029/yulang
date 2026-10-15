use super::*;
use crate::shadow::{
    LocalSource, LocalSourceForm, LocalSourceNamedGroupOwner, LocalSourceResolution,
    lower_module_with_local_source,
};

fn lower(text: &str) -> HirModule {
    let parsed = parsed(text);
    assert!(parsed.structural_recoveries().is_empty(), "{text}");
    lower_module_with_local_source(
        ModuleIdentity::source_root(FileId::new(FileKey::new("named-groups", "source.yu"))),
        &parsed,
        SemanticImports::empty(),
    )
    .unwrap()
}

fn source<'a>(hir: &'a HirModule, name: &str) -> &'a LocalSource {
    let root = hir
        .items()
        .iter()
        .find_map(|item| match item {
            HirItem::Binding(binding) if binding.name().spelling() == name => {
                Some(binding.definition_root())
            }
            _ => None,
        })
        .unwrap();
    hir.local_source(root).unwrap().unwrap()
}

fn check_groups(hir: &HirModule, source: &LocalSource) {
    let mut occurrences = std::collections::HashSet::new();
    for expression in source.expressions() {
        assert!(hir.owns_occurrence(&expression.occurrence));
        assert!(occurrences.insert(expression.occurrence.clone()));
        if let Some(id) = &expression.named_group {
            assert_eq!(&source.named_group(id).unwrap().id, id);
        }
    }
    for group in source.named_groups() {
        assert!(!group.formals.is_empty());
        for (index, formal) in group.formals.iter().enumerate() {
            let expression = source.expression(&formal.lambda).unwrap();
            assert_eq!(expression.named_group.as_ref(), Some(&group.id));
            assert_eq!(expression.source, group.source);
            let LocalSourceForm::Lambda { parameter, body } = &expression.form else {
                panic!("generated header Lambda");
            };
            assert_eq!(parameter.id, formal.parameter);
            let expected = group
                .formals
                .get(index + 1)
                .map_or(&group.terminal_body, |next| &next.lambda);
            assert_eq!(body, expected);
        }
        assert_eq!(
            &group.formals.last().unwrap().lambda,
            &group.terminal_lambda
        );
        assert_eq!(
            source
                .expression(&group.terminal_body)
                .unwrap()
                .named_group
                .as_ref(),
            Some(&group.id)
        );
    }
    let metadata_floor = source.expressions().len()
        * std::mem::size_of::<crate::shadow::LocalSourceExpr>()
        + source.named_groups().len() * std::mem::size_of::<crate::shadow::LocalSourceNamedGroup>()
        + source
            .named_groups()
            .iter()
            .map(|group| {
                group.formals.capacity()
                    * std::mem::size_of::<crate::shadow::LocalSourceNamedFormal>()
            })
            .sum::<usize>();
    assert!(source.retained_arena_bytes() >= metadata_floor);
}

#[test]
fn top_named_header_retains_ordered_formals_and_actual_terminal_body() {
    let hir = lower("my compose f g x = f (g x)");
    let source = source(&hir, "compose");
    assert_eq!(source.named_groups().len(), 1);
    let group = &source.named_groups()[0];
    assert_eq!(
        group.owner,
        LocalSourceNamedGroupOwner::Definition(source.definition_root().clone())
    );
    assert!(group.enclosing.is_none());
    assert_eq!(&group.formals[0].lambda, source.body());
    let names: Vec<_> = group
        .formals
        .iter()
        .map(|formal| {
            let LocalSourceForm::Lambda { parameter, .. } =
                &source.expression(&formal.lambda).unwrap().form
            else {
                panic!("Lambda");
            };
            parameter.spelling.as_ref()
        })
        .collect();
    assert_eq!(names, ["f", "g", "x"]);
    assert!(matches!(
        source.expression(&group.terminal_body).unwrap().form,
        LocalSourceForm::Apply { .. }
    ));
    check_groups(&hir, source);
}

#[test]
fn local_header_capture_retains_distinct_group_and_outer_formal_identity() {
    let hir = lower("my outer h x = { my step i = h i; step x }");
    let source = source(&hir, "outer");
    assert_eq!(source.named_groups().len(), 2);
    let outer = &source.named_groups()[0];
    let binding = source
        .bindings()
        .iter()
        .find(|binding| binding.spelling.as_ref() == "step")
        .unwrap();
    let step = source
        .named_groups()
        .iter()
        .find(|group| group.owner == LocalSourceNamedGroupOwner::Local(binding.id.clone()))
        .unwrap();
    assert_eq!(step.enclosing.as_ref(), Some(&outer.id));
    assert_eq!(&step.formals[0].lambda, &binding.initializer);
    assert_eq!(outer.formals.len(), 2);
    assert_eq!(step.formals.len(), 1);
    let captured = source
        .expressions()
        .iter()
        .find(|expression| {
            matches!(&expression.form,
        LocalSourceForm::Name { spelling, resolution: LocalSourceResolution::Parameter(id) }
            if spelling.as_ref() == "h" && id == &outer.formals[0].parameter)
        })
        .unwrap();
    assert_eq!(captured.named_group.as_ref(), Some(&step.id));
    check_groups(&hir, source);
}

#[test]
fn same_spelling_and_zero_parameter_initializers_do_not_define_group_identity() {
    let hir =
        lower("my outer h x = { my step h = h; my holder = { my step x = x; step }; step h }");
    let source = source(&hir, "outer");
    let outer = &source.named_groups()[0];
    let steps: Vec<_> = source
        .bindings()
        .iter()
        .filter(|binding| binding.spelling.as_ref() == "step")
        .collect();
    assert_eq!(steps.len(), 2);
    assert_ne!(steps[0].id, steps[1].id);
    let groups: Vec<_> = steps
        .iter()
        .map(|binding| {
            source
                .named_groups()
                .iter()
                .find(|group| group.owner == LocalSourceNamedGroupOwner::Local(binding.id.clone()))
                .unwrap()
        })
        .collect();
    assert_ne!(groups[0].id, groups[1].id);
    assert!(
        groups
            .iter()
            .all(|group| group.enclosing.as_ref() == Some(&outer.id))
    );
    assert_ne!(groups[0].formals[0].parameter, outer.formals[0].parameter);
    let holder = source
        .bindings()
        .iter()
        .find(|binding| binding.spelling.as_ref() == "holder")
        .unwrap();
    assert!(holder.parameters.is_empty());
    assert_eq!(
        source
            .expression(&holder.initializer)
            .unwrap()
            .named_group
            .as_ref(),
        Some(&outer.id)
    );
    assert_eq!(source.named_groups().len(), 3);
    check_groups(&hir, source);
}

#[test]
fn value_group_and_ascription_wrappers_keep_the_enclosing_group() {
    let hir = lower("my outer h x = { my alias = ((h as int)); alias }");
    let source = source(&hir, "outer");
    assert_eq!(source.named_groups().len(), 1);
    let group = &source.named_groups()[0];
    assert!(
        source
            .expressions()
            .iter()
            .all(|expression| expression.named_group.as_ref() == Some(&group.id))
    );
    assert!(
        source
            .expressions()
            .iter()
            .any(|expression| matches!(expression.form, LocalSourceForm::Group { .. }))
    );
    assert!(
        source
            .expressions()
            .iter()
            .any(|expression| matches!(expression.form, LocalSourceForm::Ascription { .. }))
    );
    check_groups(&hir, source);
}

#[test]
fn zero_parameter_root_and_nested_conditional_keep_explicit_surrounding_context() {
    let hir = lower(
        "my value = { my local x = x; local }\nmy outer h x = if true: ({ my step i = h i; step }) else: x",
    );
    let value = source(&hir, "value");
    assert_eq!(value.named_groups().len(), 1);
    assert!(
        value
            .expression(value.body())
            .unwrap()
            .named_group
            .is_none()
    );
    assert!(value.named_groups()[0].enclosing.is_none());
    let outer = source(&hir, "outer");
    let group = &outer.named_groups()[0];
    assert!(matches!(
        outer.expression(&group.terminal_body).unwrap().form,
        LocalSourceForm::If { .. }
    ));
    assert_eq!(outer.named_groups()[1].enclosing.as_ref(), Some(&group.id));
    check_groups(&hir, value);
    check_groups(&hir, outer);
}
