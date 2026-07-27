use super::*;

fn parse(src: &str) -> Cst {
    SyntaxNode::new_root(parser::parse_module_to_green(src))
}

fn lower_source(src: &str) -> Lower {
    let cst = parse(src);
    crate::module_map::lower_module_map_with_source(&cst, src)
}

fn value_def(lower: &Lower, name: &str) -> DefId {
    let root = lower.modules.root_id();
    lower.modules.value_decls(root, &Name(name.into()))[0].def
}

fn doc_unit_texts(doc: &DocComment) -> Vec<String> {
    doc.units()
        .iter()
        .map(|unit| unit.node().text().to_string())
        .collect()
}

fn doc_unit_kinds(doc: &DocComment) -> Vec<DocCommentKind> {
    doc.units().iter().map(|unit| unit.kind()).collect()
}

fn doc_unit_scopes(doc: &DocComment) -> Vec<(ModuleId, ModuleOrder)> {
    doc.units()
        .iter()
        .map(|unit| (unit.module(), unit.order()))
        .collect()
}

#[test]
fn registers_top_level_bindings() {
    let cst = parse("my f = 1\npub g = 2\n");
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let f = lower.modules.value_decls(root, &Name("f".into()));
    let g = lower.modules.value_decls(root, &Name("g".into()));
    assert_eq!(f.len(), 1);
    assert_eq!(g.len(), 1);
    assert_eq!(lower.arena.roots.len(), 2);
}

#[test]
fn doc_comment_line_attaches_to_following_binding() {
    let lower = lower_source("-- hello\nmy x = 1\n");
    let x = value_def(&lower, "x");
    let doc = lower
        .modules
        .def_doc_comment(x)
        .expect("line doc comment should attach to x");

    assert_eq!(doc_unit_kinds(doc), vec![DocCommentKind::Line]);
    assert_eq!(doc_unit_texts(doc), vec!["-- hello".to_string()]);
}

#[test]
fn contiguous_line_doc_comments_attach_as_one_logical_unit() {
    let lower = lower_source("-- first\n-- second\nmy x = 1\n");
    let x = value_def(&lower, "x");
    let doc = lower
        .modules
        .def_doc_comment(x)
        .expect("contiguous line doc comment should attach to x");

    assert_eq!(doc_unit_kinds(doc), vec![DocCommentKind::Line]);
    assert_eq!(doc_unit_texts(doc), vec!["-- first\n-- second".to_string()]);
}

#[test]
fn block_doc_comment_attaches_to_following_binding() {
    let lower = lower_source("---\n# Title\n---\nmy x = 1\n");
    let x = value_def(&lower, "x");
    let doc = lower
        .modules
        .def_doc_comment(x)
        .expect("block doc comment should attach to x");

    assert_eq!(doc_unit_kinds(doc), vec![DocCommentKind::Block]);
    assert_eq!(doc_unit_texts(doc), vec!["---\n# Title\n---".to_string()]);
}

#[test]
fn blank_line_between_doc_comment_and_binding_breaks_association() {
    let lower = lower_source("-- orphan\n\nmy x = 1\n");
    let x = value_def(&lower, "x");

    assert!(lower.modules.def_doc_comment(x).is_none());
}

#[test]
fn trailing_doc_comment_without_declaration_is_unassociated() {
    let lower = lower_source("-- orphan\n");

    assert_eq!(lower.modules.def_doc_comments().count(), 0);
    assert_eq!(lower.modules.type_doc_comments().count(), 0);
}

#[test]
fn doc_comment_attaches_to_type_declaration_metadata() {
    let lower = lower_source("-- boxed value\nstruct Box { value: int }\n");
    let root = lower.modules.root_id();
    let ty = lower.modules.type_decls(root, &Name("Box".into()))[0].id;
    let doc = lower
        .modules
        .type_doc_comment(ty)
        .expect("line doc comment should attach to Box type metadata");

    assert_eq!(doc_unit_kinds(doc), vec![DocCommentKind::Line]);
    assert_eq!(doc_unit_texts(doc), vec!["-- boxed value".to_string()]);
}

#[test]
fn doc_comments_retain_the_documented_declaration_lexical_scope() {
    // Written as separate literals rather than backslash continuations: `\` before a newline
    // also eats the following line's leading whitespace, which would flatten the nested module
    // body and leave `nested` empty.
    let lower = lower_source(concat!(
        "my before_top = 0\n",
        "-- top\n",
        "my top = 1\n",
        "mod nested:\n",
        "    my before_nested = 0\n",
        "    -- nested\n",
        "    my nested_value = 1\n",
        "    my after_nested = 2\n",
    ));
    let root = lower.modules.root_id();
    let top = value_def(&lower, "top");
    let nested = lower
        .modules
        .first_module_decl(root, &Name("nested".into()))
        .expect("nested module should be registered");
    let nested_value = lower
        .modules
        .value_decls(nested.module, &Name("nested_value".into()))[0]
        .def;

    let top_doc = lower
        .modules
        .def_doc_comment(top)
        .expect("top-level doc comment should attach to top");
    assert_eq!(
        doc_unit_scopes(top_doc),
        vec![(root, ModuleOrder::from_index(1))]
    );

    let nested_doc = lower
        .modules
        .def_doc_comment(nested_value)
        .expect("nested doc comment should attach to nested_value");
    assert_eq!(
        doc_unit_scopes(nested_doc),
        vec![(nested.module, ModuleOrder::from_index(1))]
    );
}

#[test]
fn doc_fence_token_ranges_are_absolute_in_the_original_multiline_source() {
    let source = concat!(
        "my padding_a = 0\n",
        "my padding_b = 1\n",
        "---\n",
        "prose one\n",
        "prose two\n",
        "```yulang\n",
        "my local = true\n",
        "assert false\n",
        "```\n",
        "---\n",
        "my documented = 0\n",
    );
    let lower = lower_source(source);
    let documented = value_def(&lower, "documented");
    let doc = lower
        .modules
        .def_doc_comment(documented)
        .expect("doc comment should attach");
    let assertion = doc.units()[0]
        .node()
        .descendants_with_tokens()
        .filter_map(|item| item.into_token())
        .find(|token| token.text() == "assert")
        .expect("parsed yulang fence should retain the assertion token");
    let fence = assertion
        .parent_ancestors()
        .find(|node| node.kind() == parser::lex::SyntaxKind::YmCodeFence)
        .expect("assertion should be inside a code fence");
    let comment = &doc.units()[0];
    let comment_start = comment.source_span().range.start;
    let raw_comment = &source[comment.source_span().range.start..comment.source_span().range.end];
    let raw_fence_start = raw_comment
        .find("```yulang")
        .expect("original comment contains the fence");
    let range_in_fence = usize::from(assertion.text_range().start() - fence.text_range().start());

    assert_eq!(
        comment.fence_source_start(0),
        Some(source.find("```yulang").expect("source contains the fence"))
    );
    assert_eq!(
        comment_start + raw_fence_start + range_in_fence,
        source
            .find("assert false")
            .expect("source contains assertion")
    );
}

#[test]
fn registers_cast_decl_as_hidden_cast_metadata() {
    let cst = parse("cast(x: int): int = x\nmy site = 1\n");
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();

    assert_eq!(lower.modules.cast_decls(root).len(), 1);
    assert!(
        lower
            .modules
            .value_decls(root, &Name("#cast".into()))
            .is_empty()
    );
    assert_eq!(lower.arena.roots.len(), 1);
}

#[test]
fn registers_parenthesized_keyword_call_binding() {
    let cst = parse("pub (mod)(x: int, y: int): int\nmy site = mod\n");
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();

    assert_eq!(
        lower.modules.value_decls(root, &Name("mod".into())).len(),
        1
    );
    assert_eq!(
        lower.modules.value_decls(root, &Name("site".into())).len(),
        1
    );
    assert_eq!(lower.arena.roots.len(), 2);
}

#[test]
fn registers_struct_and_enum_constructors_as_values() {
    let cst = parse("struct Box 'a { value: 'a }\nenum opt 'a = none | some 'a\n");
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();

    assert_eq!(
        lower.modules.value_decls(root, &Name("Box".into())).len(),
        1
    );
    // enum constructor は型 companion module に住む。
    let opt = lower.modules.type_decls(root, &Name("opt".into()))[0].id;
    let companion = lower.modules.type_companion(opt).expect("opt companion");
    assert_eq!(
        lower
            .modules
            .value_decls(companion, &Name("none".into()))
            .len(),
        1
    );
    assert_eq!(
        lower
            .modules
            .value_decls(companion, &Name("some".into()))
            .len(),
        1
    );
    assert!(
        lower
            .modules
            .value_decls(root, &Name("none".into()))
            .is_empty()
    );
}

#[test]
fn derives_requests_normalize_all_attachment_positions_for_nominal_declarations() {
    for fixture in [
        DeriveRequestFixture {
            name: "Record",
            sources: [
                "struct Record { value: int } derives Eq, Debug via value",
                "struct Record { value: int } with:\n  derives Eq, Debug via value",
                "struct Record derives Eq, Debug via value:\n  value: int",
            ],
            via: Some("value"),
        },
        DeriveRequestFixture {
            name: "Tuple",
            sources: [
                "struct Tuple(int) derives Eq, Debug",
                "struct Tuple(int) with:\n  derives Eq, Debug",
                "struct Tuple derives Eq, Debug (int)",
            ],
            via: None,
        },
        DeriveRequestFixture {
            name: "Choice",
            sources: [
                "enum Choice { A } derives Eq, Debug",
                "enum Choice { A } with:\n  derives Eq, Debug",
                "enum Choice derives Eq, Debug:\n  A",
            ],
            via: None,
        },
        DeriveRequestFixture {
            name: "Failure",
            sources: [
                "error Failure { bad int } derives Eq, Debug",
                "error Failure { bad int } with:\n  derives Eq, Debug",
                "error Failure derives Eq, Debug:\n  bad int",
            ],
            via: None,
        },
    ] {
        let expected = vec![(0, vec!["Eq".to_string(), "Debug".to_string()], fixture.via)];
        for source in fixture.sources {
            let lower = lower_source(source);
            let root = lower.modules.root_id();
            let declaration = lower.modules.type_decls(root, &Name(fixture.name.into()))[0].clone();
            let companion = lower
                .modules
                .type_companion(declaration.id)
                .expect("derive request companion");
            let requests = lower.modules.derive_requests(declaration.id);

            assert_eq!(derive_request_summary(requests), expected, "{source}");
            for request in requests {
                assert_eq!(request.owner, declaration.id, "{source}");
                assert_eq!(request.companion, companion, "{source}");
                assert_eq!(
                    request
                        .roles
                        .iter()
                        .map(|role| role.span.range)
                        .collect::<Vec<_>>(),
                    vec![
                        source_range_of(source, "Eq"),
                        source_range_of(source, "Debug")
                    ],
                    "{source}"
                );
                if let Some(via) = &request.via {
                    assert_eq!(
                        via.span.range,
                        via_target_source_range(source, fixture.via.unwrap())
                    );
                }
            }
        }
    }
}

#[test]
fn derives_requests_preserve_source_order_and_duplicate_roles() {
    let source = concat!(
        "struct Record derives Eq { value: int } derives Debug with:\n",
        "  derives Eq via value\n",
    );
    let lower = lower_source(source);
    let root = lower.modules.root_id();
    let record = lower.modules.type_decls(root, &Name("Record".into()))[0].id;
    let requests = lower.modules.derive_requests(record);

    assert_eq!(
        derive_request_summary(requests),
        vec![
            (0, vec!["Eq".to_string()], None),
            (1, vec!["Debug".to_string()], None),
            (2, vec!["Eq".to_string()], Some("value")),
        ]
    );
}

#[test]
fn derives_requests_are_retained_for_parsed_out_of_scope_declarations() {
    for (name, source) in [
        ("Alias", "type Alias derives Eq"),
        ("Console", "act Console derives Eq;"),
    ] {
        let lower = lower_source(source);
        let root = lower.modules.root_id();
        let declaration = lower.modules.type_decls(root, &Name(name.into()))[0].clone();
        let requests = lower.modules.derive_requests(declaration.id);

        assert_eq!(
            derive_request_summary(requests),
            vec![(0, vec!["Eq".to_string()], None)],
            "{source}"
        );
        assert_eq!(requests[0].owner, declaration.id, "{source}");
        assert_eq!(
            requests[0].companion,
            lower
                .modules
                .type_companion(declaration.id)
                .expect("derive request companion"),
            "{source}"
        );
    }
}

struct DeriveRequestFixture {
    name: &'static str,
    sources: [&'static str; 3],
    via: Option<&'static str>,
}

fn derive_request_summary(requests: &[DeriveRequest]) -> Vec<(u32, Vec<String>, Option<&str>)> {
    requests
        .iter()
        .map(|request| {
            (
                request.order,
                request
                    .roles
                    .iter()
                    .map(|role| role.node.text().to_string().trim().to_string())
                    .collect(),
                request.via.as_ref().map(|via| via.name.0.as_str()),
            )
        })
        .collect()
}

fn source_range_of(source: &str, text: &str) -> SourceRange {
    let start = source.find(text).expect("source text");
    SourceRange {
        start,
        end: start + text.len(),
    }
}

fn via_target_source_range(source: &str, text: &str) -> SourceRange {
    let start = source.find(&format!("via {text}")).expect("via target") + "via ".len();
    SourceRange {
        start,
        end: start + text.len(),
    }
}

#[test]
fn role_impl_body_gets_poly_module_identity() {
    let cst = parse("role Eq 'a;\nimpl int: Eq {\n  our x.eq = x\n  my helper = x\n}\n");
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let [impl_decl] = lower.modules.role_impls(root) else {
        panic!("impl should be registered once");
    };
    let Some(Def::Mod { children, .. }) = lower.arena.defs.get(impl_decl.def) else {
        panic!("impl should have a poly module def");
    };

    assert!(lower.arena.roots.contains(&impl_decl.def));
    assert_eq!(children.len(), 2);
    assert_eq!(children[0], impl_decl.methods[0].def);
    assert_eq!(
        lower
            .modules
            .value_decls(impl_decl.body_module, &Name("helper".into()))
            .len(),
        1
    );
}

#[test]
fn collects_use_aliases() {
    let cst = parse("use a::b as c\nuse x::y::*\nmy f = 1\n");
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    // alias c と glob x::y の 2 本が溜まり、pass1 完了後に import view へ展開される。
    assert_eq!(lower.modules.aliases(root).len(), 2);
    assert_eq!(lower.modules.value_decls(root, &Name("f".into())).len(), 1);
}

#[test]
fn import_view_resolves_aliases_across_namespaces() {
    let cst = parse(
        "mod m:\n  type T\n  our value = 1\n  mod n:\n    type U\nuse m::T as AliasT\nuse m::value as imported_value\nuse m::n as imported_n\nmy site = imported_value\n",
    );
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let m = lower.modules.module_decls(root, &Name("m".into()))[0].module;
    let n = lower.modules.module_decls(m, &Name("n".into()))[0].module;
    let value = lower.modules.value_decls(m, &Name("value".into()))[0].def;
    let site_order = lower.modules.value_decls(root, &Name("site".into()))[0].order;
    let alias_t = lower
        .modules
        .lexical_type_at(root, &Name("AliasT".into()), site_order)
        .expect("type alias import should resolve");

    assert_eq!(
        lower.modules.type_decl_path(&alias_t).segments,
        vec![Name("m".into()), Name("T".into())]
    );
    assert_eq!(
        lower
            .modules
            .lexical_value_at(root, &Name("imported_value".into()), site_order),
        Some(value)
    );
    assert_eq!(
        lower
            .modules
            .lexical_module_at(root, &Name("imported_n".into()), site_order),
        Some(n)
    );
}

#[test]
fn import_view_resolves_alias_to_reexported_value() {
    let cst = parse(
        "mod inner:\n  pub value = 1\nmod facade:\n  pub use inner::*\nuse facade::value as imported_value\nmy site = imported_value\n",
    );
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let inner = lower.modules.module_decls(root, &Name("inner".into()))[0].module;
    let value = lower.modules.value_decls(inner, &Name("value".into()))[0].def;
    let site_order = lower.modules.value_decls(root, &Name("site".into()))[0].order;

    assert_eq!(
        lower
            .modules
            .lexical_value_at(root, &Name("imported_value".into()), site_order),
        Some(value)
    );
}

#[test]
fn same_band_import_does_not_resolve_private_value() {
    let cst = parse("mod m:\n  my value = 1\nuse m::value as imported_value\nmy site = 1\n");
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let site_order = lower.modules.value_decls(root, &Name("site".into()))[0].order;

    assert_eq!(
        lower
            .modules
            .lexical_value_at(root, &Name("imported_value".into()), site_order),
        None
    );
}

#[test]
fn import_view_resolves_globs_across_namespaces() {
    let cst = parse(
        "mod m:\n  type T\n  our value = 1\n  mod n:\n    type U\nuse m::*\nmy site = value\n",
    );
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let m = lower.modules.module_decls(root, &Name("m".into()))[0].module;
    let n = lower.modules.module_decls(m, &Name("n".into()))[0].module;
    let value = lower.modules.value_decls(m, &Name("value".into()))[0].def;
    let site_order = lower.modules.value_decls(root, &Name("site".into()))[0].order;
    let imported_t = lower
        .modules
        .lexical_type_at(root, &Name("T".into()), site_order)
        .expect("glob type import should resolve");

    assert_eq!(
        lower.modules.type_decl_path(&imported_t).segments,
        vec![Name("m".into()), Name("T".into())]
    );
    assert_eq!(
        lower
            .modules
            .lexical_value_at(root, &Name("value".into()), site_order),
        Some(value)
    );
    assert_eq!(
        lower
            .modules
            .lexical_module_at(root, &Name("n".into()), site_order),
        Some(n)
    );
}

#[test]
fn my_visibility_imports_keep_descendants_open_and_reexports_closed() {
    // `our use` may import an ancestor's `my` declaration from a descendant;
    // the carried origin remains the ancestor. `my use` makes the descendant
    // its new, narrower private boundary.
    let named = lower_source(
        "mod owner:\n  my value = 1\n  my act Thing:\n    pub ping: () -> int\n  my mod child:\n  pub mod descendant:\n    our use band::owner::value as our_value\n    our use band::owner::Thing as OurThing\n    our use band::owner::child as our_child\n    my use band::owner::value as my_value\n    my use band::owner::Thing as MyThing\n    my use band::owner::child as my_child\n",
    );
    let root = named.modules.root_id();
    let owner = named.modules.module_decls(root, &Name("owner".into()))[0].module;
    let descendant = named
        .modules
        .module_decls(owner, &Name("descendant".into()))[0]
        .module;
    let owner_origins = source_private_origins(&named.modules, owner);

    assert_private_origin(
        &named.modules,
        private_value_origin(&named.modules, descendant, "our_value"),
        owner_origins.0,
    );
    assert_private_origin(
        &named.modules,
        private_type_origin(&named.modules, descendant, "OurThing"),
        owner_origins.1,
    );
    assert_private_origin(
        &named.modules,
        private_module_origin(&named.modules, descendant, "our_child"),
        owner_origins.2,
    );
    for (name, actual) in [
        (
            "my_value",
            private_value_origin(&named.modules, descendant, "my_value"),
        ),
        (
            "MyThing",
            private_type_origin(&named.modules, descendant, "MyThing"),
        ),
        (
            "my_child",
            private_module_origin(&named.modules, descendant, "my_child"),
        ),
    ] {
        let expected = named
            .modules
            .aliases(descendant)
            .iter()
            .find(|alias| {
                matches!(&alias.import, UseImport::Alias { name: alias_name, .. } if alias_name.0 == name)
            })
            .and_then(|alias| alias.private_origin)
            .expect("my use should establish the descendant private boundary");
        assert_private_origin(&named.modules, actual, expected);
    }

    // A descendant glob can cross its ancestor's private module boundary and
    // receives every public namespace from that module.
    let descendant_glob = lower_source(
        "mod owner:\n  my mod source:\n    pub value = 1\n    pub act Thing:\n      pub ping: () -> int\n    pub mod child:\n  pub mod descendant:\n    use band::owner::source::*\n",
    );
    let root = descendant_glob.modules.root_id();
    let owner = descendant_glob
        .modules
        .module_decls(root, &Name("owner".into()))[0]
        .module;
    let descendant = descendant_glob
        .modules
        .module_decls(owner, &Name("descendant".into()))[0]
        .module;
    assert!(
        descendant_glob.modules.nodes[descendant.0]
            .import_values
            .contains_key(&Name("value".into()))
    );
    assert!(
        descendant_glob.modules.nodes[descendant.0]
            .import_types
            .contains_key(&Name("Thing".into()))
    );
    assert!(
        descendant_glob.modules.nodes[descendant.0]
            .import_modules
            .contains_key(&Name("child".into()))
    );

    // An external glob itself is legal, but private entries do not enter its
    // surface. That is deliberately not a private-access diagnostic.
    let external_glob = lower_source(
        "pub mod owner:\n  my value = 1\n  my act Thing:\n    pub ping: () -> int\n  my mod child:\nmod outsider:\n  use band::owner::*\n",
    );
    let root = external_glob.modules.root_id();
    let outsider = external_glob
        .modules
        .module_decls(root, &Name("outsider".into()))[0]
        .module;
    assert!(
        !external_glob.modules.nodes[outsider.0]
            .import_values
            .contains_key(&Name("value".into()))
    );
    assert!(
        !external_glob.modules.nodes[outsider.0]
            .import_types
            .contains_key(&Name("Thing".into()))
    );
    assert!(
        !external_glob.modules.nodes[outsider.0]
            .import_modules
            .contains_key(&Name("child".into()))
    );
    assert!(
        external_glob
            .modules
            .import_privacy_diagnostics()
            .is_empty()
    );

    // A descendant may publish its aliases, but an unrelated second step may
    // not turn the carried private origin into a public re-export.
    let two_step = lower_source(
        "pub mod owner:\n  my value = 1\n  my act Thing:\n    pub ping: () -> int\n  my mod child:\n  pub mod descendant:\n    pub use band::owner::value\n    pub use band::owner::Thing\n    pub use band::owner::child\n    our use band::owner::value as our_value\n    our use band::owner::Thing as OurThing\n    our use band::owner::child as our_child\n    my use band::owner::value as my_value\n    my use band::owner::Thing as MyThing\n    my use band::owner::child as my_child\npub mod relay:\n  pub use band::owner::descendant::value\n  pub use band::owner::descendant::Thing\n  pub use band::owner::descendant::child\n  pub use band::owner::descendant::our_value\n  pub use band::owner::descendant::OurThing\n  pub use band::owner::descendant::our_child\n  pub use band::owner::descendant::my_value\n  pub use band::owner::descendant::MyThing\n  pub use band::owner::descendant::my_child\n",
    );
    let root = two_step.modules.root_id();
    let relay = two_step.modules.module_decls(root, &Name("relay".into()))[0].module;
    for name in ["value", "our_value", "my_value"] {
        assert!(
            !two_step.modules.nodes[relay.0]
                .import_values
                .contains_key(&Name(name.into()))
        );
    }
    for name in ["Thing", "OurThing", "MyThing"] {
        assert!(
            !two_step.modules.nodes[relay.0]
                .import_types
                .contains_key(&Name(name.into()))
        );
    }
    for name in ["child", "our_child", "my_child"] {
        assert!(
            !two_step.modules.nodes[relay.0]
                .import_modules
                .contains_key(&Name(name.into()))
        );
    }
    assert_eq!(two_step.modules.import_privacy_diagnostics().len(), 9);
}

fn private_value_origin(modules: &ModuleTable, module: ModuleId, name: &str) -> PrivateOriginId {
    modules.nodes[module.0].import_values[&Name(name.into())]
        .iter()
        .find_map(|entry| entry.private_origin)
        .expect("imported value should retain private provenance")
}

fn private_type_origin(modules: &ModuleTable, module: ModuleId, name: &str) -> PrivateOriginId {
    modules.nodes[module.0].import_types[&Name(name.into())]
        .iter()
        .find_map(|entry| entry.private_origin)
        .expect("imported type should retain private provenance")
}

fn private_module_origin(modules: &ModuleTable, module: ModuleId, name: &str) -> PrivateOriginId {
    modules.nodes[module.0].import_modules[&Name(name.into())]
        .iter()
        .find_map(|entry| entry.private_origin)
        .expect("imported module should retain private provenance")
}

fn source_private_origins(
    modules: &ModuleTable,
    module: ModuleId,
) -> (PrivateOriginId, PrivateOriginId, PrivateOriginId) {
    let value = modules.value_decls(module, &Name("value".into()))[0]
        .private_origin
        .expect("private value declaration should have provenance");
    let ty = modules.type_decls(module, &Name("Thing".into()))[0]
        .private_origin
        .expect("private type declaration should have provenance");
    let child = modules.module_decls(module, &Name("child".into()))[0]
        .private_origin
        .expect("private module declaration should have provenance");
    (value, ty, child)
}

fn expose_private_source_for_import_copy_test(lower: &mut Lower, module: ModuleId) {
    for decl in &mut lower.modules.nodes[module.0].decls {
        if decl.private_origin.is_some() {
            decl.vis = Vis::Pub;
        }
    }
    lower.modules.build_import_views();
}

fn expose_private_imports_for_import_copy_test(lower: &mut Lower, module: ModuleId) {
    for entries in lower.modules.nodes[module.0].import_values.values_mut() {
        for entry in entries {
            entry.vis = Vis::Pub;
        }
    }
    for entries in lower.modules.nodes[module.0].import_types.values_mut() {
        for entry in entries {
            entry.vis = Vis::Pub;
        }
    }
    for entries in lower.modules.nodes[module.0].import_modules.values_mut() {
        for entry in entries {
            entry.vis = Vis::Pub;
        }
    }
    lower.modules.build_import_views();
}

fn assert_private_origin(
    modules: &ModuleTable,
    actual: PrivateOriginId,
    expected: PrivateOriginId,
) {
    assert_eq!(
        modules.private_origin(actual),
        modules.private_origin(expected)
    );
}

fn add_private_alias(
    modules: &mut ModuleTable,
    module: ModuleId,
    name: &str,
    path: &[&str],
    span_start: usize,
) {
    modules.add_alias(
        module,
        UseImport::Alias {
            name: Name(name.into()),
            path: ModulePath {
                segments: path.iter().map(|segment| Name((*segment).into())).collect(),
            },
            route: sources::UsePathRoute::Relative,
            version: None,
            anchor: None,
        },
        Vis::My,
        Some(SourceSpan {
            file: ModulePath::default(),
            range: SourceRange {
                start: span_start,
                end: span_start + name.len(),
            },
        }),
    );
}

#[test]
fn runtime_imports_retain_private_provenance_at_every_copy_site() {
    let mut named = lower_source(
        "mod source:\n  my value = 1\n  my act Thing:\n    pub ping: () -> int\n  my mod child:\nuse source::value as value_alias\nuse source::Thing as type_alias\nuse source::child as module_alias\n",
    );
    let root = named.modules.root_id();
    let source = named.modules.module_decls(root, &Name("source".into()))[0].module;
    let expected = source_private_origins(&named.modules, source);
    expose_private_source_for_import_copy_test(&mut named, source);
    assert_private_origin(
        &named.modules,
        private_value_origin(&named.modules, root, "value_alias"),
        expected.0,
    );
    assert_private_origin(
        &named.modules,
        private_type_origin(&named.modules, root, "type_alias"),
        expected.1,
    );
    assert_private_origin(
        &named.modules,
        private_module_origin(&named.modules, root, "module_alias"),
        expected.2,
    );

    let mut direct_glob = lower_source(
        "mod source:\n  my value = 1\n  my act Thing:\n    pub ping: () -> int\n  my mod child:\nuse source::*\n",
    );
    let root = direct_glob.modules.root_id();
    let source = direct_glob
        .modules
        .module_decls(root, &Name("source".into()))[0]
        .module;
    let expected = source_private_origins(&direct_glob.modules, source);
    expose_private_source_for_import_copy_test(&mut direct_glob, source);
    assert_private_origin(
        &direct_glob.modules,
        private_value_origin(&direct_glob.modules, root, "value"),
        expected.0,
    );
    assert_private_origin(
        &direct_glob.modules,
        private_type_origin(&direct_glob.modules, root, "Thing"),
        expected.1,
    );
    assert_private_origin(
        &direct_glob.modules,
        private_module_origin(&direct_glob.modules, root, "child"),
        expected.2,
    );

    let mut reexport = lower_source(
        "mod public:\n  pub value = 1\n  pub act Thing:\n    pub ping: () -> int\n  pub mod child:\nmod owner:\n  mod source:\n    pub use public::value\n    pub use public::Thing\n    pub use public::child\n  pub mod facade:\n    pub use band::owner::source::*\n",
    );
    let root = reexport.modules.root_id();
    let owner = reexport.modules.module_decls(root, &Name("owner".into()))[0].module;
    let source = reexport.modules.module_decls(owner, &Name("source".into()))[0].module;
    let expected = reexport
        .modules
        .private_origin_for(
            owner,
            Vis::My,
            Some(SourceSpan {
                file: ModulePath::default(),
                range: SourceRange { start: 0, end: 0 },
            }),
        )
        .expect("my visibility should create an origin");
    for entries in reexport.modules.nodes[source.0].import_values.values_mut() {
        for entry in entries {
            entry.private_origin = Some(expected);
        }
    }
    for entries in reexport.modules.nodes[source.0].import_types.values_mut() {
        for entry in entries {
            entry.private_origin = Some(expected);
        }
    }
    for entries in reexport.modules.nodes[source.0].import_modules.values_mut() {
        for entry in entries {
            entry.private_origin = Some(expected);
        }
    }
    expose_private_imports_for_import_copy_test(&mut reexport, source);
    let facade = reexport.modules.module_decls(owner, &Name("facade".into()))[0].module;
    assert_private_origin(
        &reexport.modules,
        private_value_origin(&reexport.modules, facade, "value"),
        expected,
    );
    assert_private_origin(
        &reexport.modules,
        private_type_origin(&reexport.modules, facade, "Thing"),
        expected,
    );
    assert_private_origin(
        &reexport.modules,
        private_module_origin(&reexport.modules, facade, "child"),
        expected,
    );

    let private_alias = lower_source(
        "mod public:\n  pub value = 1\n  pub act Thing:\n    pub ping: () -> int\n  pub mod child:\nmy use public::value as private_value\nmy use public::Thing as private_type\nmy use public::child as private_module\n",
    );
    let root = private_alias.modules.root_id();
    for name in ["private_value", "private_type", "private_module"] {
        let origin = match name {
            "private_value" => private_value_origin(&private_alias.modules, root, name),
            "private_type" => private_type_origin(&private_alias.modules, root, name),
            "private_module" => private_module_origin(&private_alias.modules, root, name),
            _ => unreachable!(),
        };
        let expected = private_alias.modules.aliases(root)
            .iter()
            .find(|alias| matches!(&alias.import, UseImport::Alias { name: alias_name, .. } if alias_name.0 == name))
            .and_then(|alias| alias.private_origin)
            .expect("my use should register its private origin");
        assert_private_origin(&private_alias.modules, origin, expected);
    }

    let mut operator_alias = lower_source("mod public:\n  pub infix (+) 50 50 = 1\n");
    let root = operator_alias.modules.root_id();
    add_private_alias(&mut operator_alias.modules, root, "+", &["public", "+"], 40);
    operator_alias.modules.build_import_views();
    let origin = private_value_origin(&operator_alias.modules, root, "#op:infix:+");
    let expected = operator_alias.modules.aliases(root)[0]
        .private_origin
        .expect("my operator use should register its private origin");
    assert_private_origin(&operator_alias.modules, origin, expected);
}

#[test]
fn compiled_namespace_round_trips_private_reexport_provenance() {
    // This is the MYVIS-B format-bump witness.  Materialize a private ancestor
    // origin on owner imports, then let its descendant facade re-export them.
    let mut lower = lower_source(
        "mod public:\n  pub value = 1\n  pub act Thing:\n    pub ping: () -> int\n  pub mod child:\nmod owner:\n  pub use public::value\n  pub use public::Thing\n  pub use public::child\n  pub mod facade:\n    pub use band::owner::*\n",
    );
    let root = lower.modules.root_id();
    let owner = lower.modules.module_decls(root, &Name("owner".into()))[0].module;
    let origin = lower
        .modules
        .private_origin_for(
            owner,
            Vis::My,
            Some(SourceSpan {
                file: ModulePath::default(),
                range: SourceRange { start: 17, end: 22 },
            }),
        )
        .unwrap();
    for entries in lower.modules.nodes[owner.0].import_values.values_mut() {
        for entry in entries {
            entry.private_origin = Some(origin);
        }
    }
    for entries in lower.modules.nodes[owner.0].import_types.values_mut() {
        for entry in entries {
            entry.private_origin = Some(origin);
        }
    }
    for entries in lower.modules.nodes[owner.0].import_modules.values_mut() {
        for entry in entries {
            entry.private_origin = Some(origin);
        }
    }
    expose_private_imports_for_import_copy_test(&mut lower, owner);

    let mut surface = CompiledNamespaceSurface::from_module_table(&lower.modules);
    // A prefix carries its exported materialized view.  Keep the owner module
    // solely as the origin scope and the facade's three re-exports as the
    // observable entries, avoiding unrelated duplicate exports in this unit.
    for module in &mut surface.modules {
        module.values.clear();
        module.types.clear();
        if module.path != vec!["owner".to_string(), "facade".to_string()] {
            module.imported_values.clear();
            module.imported_types.clear();
            module.imported_modules.clear();
        } else {
            module
                .imported_values
                .sort_by_key(|entry| entry.private_origin.is_none());
            module
                .imported_types
                .sort_by_key(|entry| entry.private_origin.is_none());
            module
                .imported_modules
                .sort_by_key(|entry| entry.private_origin.is_none());
            module
                .imported_values
                .dedup_by(|left, right| left.name == right.name);
            module
                .imported_types
                .dedup_by(|left, right| left.name == right.name);
            module
                .imported_modules
                .dedup_by(|left, right| left.name == right.name);
        }
    }
    let bytes = bincode::serialize(&surface).unwrap();
    let round_trip: CompiledNamespaceSurface = bincode::deserialize(&bytes).unwrap();
    let merged = CompiledNamespaceSurface::merge_prefixes_with_remap([&round_trip]).unwrap();
    let facade_path = vec!["owner".to_string(), "facade".to_string()];
    let facade = merged
        .surface
        .modules
        .iter()
        .find(|module| module.path == facade_path)
        .unwrap();
    for origin in [
        facade
            .imported_values
            .iter()
            .find(|entry| entry.name == "value")
            .unwrap()
            .private_origin
            .as_ref(),
        facade
            .imported_types
            .iter()
            .find(|entry| entry.name == "Thing")
            .unwrap()
            .private_origin
            .as_ref(),
        facade
            .imported_modules
            .iter()
            .find(|entry| entry.name == "child")
            .unwrap()
            .private_origin
            .as_ref(),
    ] {
        let origin = origin.expect("compiled materialized re-export must retain provenance");
        assert_eq!(
            origin.scope_module,
            merged
                .map_module(
                    0,
                    round_trip
                        .modules
                        .iter()
                        .find(|module| module.path == vec!["owner".to_string()])
                        .unwrap()
                        .id
                )
                .unwrap()
        );
        assert_eq!(
            origin.declaration_span.as_ref().unwrap().range,
            SourceRange { start: 17, end: 22 }
        );
    }
}

#[test]
fn direct_type_decl_shadows_glob_import() {
    let cst = parse("mod m:\n  type T\nuse m::*\ntype T\nmy site = 1\n");
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let site_order = lower.modules.value_decls(root, &Name("site".into()))[0].order;
    let found = lower
        .modules
        .lexical_type_at(root, &Name("T".into()), site_order)
        .expect("local type should resolve");

    assert_eq!(
        lower.modules.type_decl_path(&found).segments,
        vec![Name("T".into())]
    );
}

#[test]
fn registers_nested_module() {
    let cst = parse("mod m:\n  my x = 1\n");
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let module_decls = lower.modules.module_decls(root, &Name("m".into()));
    let [m_decl] = module_decls.as_slice() else {
        panic!("module m should be registered once");
    };
    assert_eq!(m_decl.order, ModuleOrder(0));
    let m = m_decl.module;
    assert_eq!(lower.modules.value_decls(m, &Name("x".into())).len(), 1);
}

#[test]
fn retains_named_and_unnamed_test_module_markers() {
    let lower =
        lower_source("mod test:\n  my unnamed = 1\nmy mod test internals:\n  my named = 2\n");
    let tests = lower.modules.test_module_decls();

    assert_eq!(tests.len(), 2);
    assert_eq!(tests[0].name, None);
    assert_eq!(tests[0].vis, Vis::Our);
    assert_eq!(tests[1].name, Some(Name("internals".into())));
    assert_eq!(tests[1].vis, Vis::My);
    assert!(tests.iter().all(|test| {
        lower.modules.is_test_module(test.module)
            && lower
                .arena
                .defs
                .get(test.def)
                .is_some_and(|def| matches!(def, Def::Mod { .. }))
    }));
    assert_eq!(
        lower
            .modules
            .value_decls(tests[0].module, &Name("unnamed".into()))
            .len(),
        1
    );
    assert_eq!(
        lower
            .modules
            .value_decls(tests[1].module, &Name("named".into()))
            .len(),
        1
    );
}

#[test]
fn registers_type_namespace_decls_and_constructor_roots() {
    let cst = parse(
        "type Alias\nstruct Record { x: int }\nenum Choice { A }\nerror Failure:\n  bad str\nrole Eq;\nact Console;\nmy value = 1\n",
    );
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();

    assert_eq!(lower.arena.roots.len(), 4);
    assert_eq!(
        lower
            .modules
            .value_decls(root, &Name("Record".into()))
            .len(),
        1
    );
    // enum / error の constructor は型 companion module に住む。
    let choice = lower.modules.type_decls(root, &Name("Choice".into()))[0].id;
    let choice_companion = lower
        .modules
        .type_companion(choice)
        .expect("Choice companion");
    assert_eq!(
        lower
            .modules
            .value_decls(choice_companion, &Name("A".into()))
            .len(),
        1
    );
    let failure = lower.modules.type_decls(root, &Name("Failure".into()))[0].id;
    let failure_companion = lower
        .modules
        .type_companion(failure)
        .expect("Failure companion");
    assert_eq!(
        lower
            .modules
            .value_decls(failure_companion, &Name("bad".into()))
            .len(),
        1
    );
    assert_eq!(
        lower.modules.type_decls(root, &Name("Alias".into()))[0].kind,
        ModuleTypeKind::TypeAlias
    );
    assert_eq!(
        lower.modules.type_decls(root, &Name("Record".into()))[0].kind,
        ModuleTypeKind::Struct
    );
    assert_eq!(
        lower.modules.type_decls(root, &Name("Choice".into()))[0].kind,
        ModuleTypeKind::Enum
    );
    assert_eq!(
        lower.modules.type_decls(root, &Name("Failure".into()))[0].kind,
        ModuleTypeKind::Error
    );
    assert_eq!(
        lower.modules.type_decls(root, &Name("Eq".into()))[0].kind,
        ModuleTypeKind::Role
    );
    assert_eq!(
        lower.modules.type_decls(root, &Name("Console".into()))[0].kind,
        ModuleTypeKind::Act
    );
}

#[test]
fn registers_type_with_body_as_companion_module_methods() {
    let cst = parse("type box 'a with:\n  our x.value = x\n  our &x.update = &x\nmy site = 1\n");
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let box_type = lower.modules.type_decls(root, &Name("box".into()))[0].clone();
    let companion = lower
        .modules
        .type_companion(box_type.id)
        .expect("type with should create a companion module");
    let methods = lower.modules.type_methods(box_type.id);

    assert_eq!(
        lower.modules.module_decls(root, &Name("box".into()))[0].module,
        companion
    );
    assert_eq!(
        lower
            .modules
            .value_decls(companion, &Name("value".into()))
            .len(),
        1
    );
    assert_eq!(
        lower
            .modules
            .value_decls(companion, &Name("update!".into()))
            .len(),
        1
    );
    assert_eq!(methods.len(), 2);
    assert_eq!(methods[0].name, Name("value".into()));
    assert_eq!(methods[0].receiver, Name("x".into()));
    assert_eq!(methods[0].receiver_kind, TypeMethodReceiver::Value);
    assert_eq!(methods[1].name, Name("update".into()));
    assert_eq!(methods[1].receiver, Name("&x".into()));
    assert_eq!(methods[1].receiver_kind, TypeMethodReceiver::Ref);
}

#[test]
fn registers_type_with_self_struct_as_outer_constructor() {
    let cst = parse("type t 'a with:\n  struct self:\n    field: 'a\n");
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let t_type = lower.modules.type_decls(root, &Name("t".into()))[0].clone();
    let companion = lower
        .modules
        .type_companion(t_type.id)
        .expect("type with should create companion module");

    assert_eq!(lower.modules.value_decls(root, &Name("t".into())).len(), 1);
    assert!(
        lower
            .modules
            .type_decls(companion, &Name("self".into()))
            .is_empty()
    );
}

#[test]
fn registers_act_operation_names_for_coverage() {
    let cst = parse(
        "act out:\n  our say: int -> unit\n  our write: int -> unit\n  our x.clear = x\nmy site = 1\n",
    );
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let site = lower.modules.value_decls(root, &Name("site".into()))[0].order;
    let ops = lower
        .modules
        .act_operation_decls_at(root, &[Name("out".into())], site)
        .found()
        .expect("local act operations should resolve")
        .into_iter()
        .map(|op| op.name)
        .collect::<Vec<_>>();

    assert_eq!(ops, vec![Name("say".into()), Name("write".into())]);
}

#[test]
fn myvis_e_private_act_is_rejected_outside_owner() {
    let cst = parse("mod owner:\n  my act hidden:\n    our ping: () -> unit\nmy site = 1\n");
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let site = lower.modules.value_decls(root, &Name("site".into()))[0].order;

    let lookup = lower.modules.act_operation_decls_at(
        root,
        &[Name("owner".into()), Name("hidden".into())],
        site,
    );

    assert!(matches!(lookup, Lookup::Private(_)));
}

#[test]
fn myvis_e_act_operation_visibility_follows_companion_ancestry() {
    let cst = parse(
        "pub mod owner:\n  pub act effect:\n    my ping: () -> unit\n    our pong: () -> unit\n    pub mod child:\n      pub mod grandchild:\n  pub mod sibling:\npub mod unrelated:\nmy site = 1\n",
    );
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let site = lower.modules.value_decls(root, &Name("site".into()))[0].order;
    let owner = lower
        .modules
        .module_at(root, root, &Name("owner".into()), site)
        .found()
        .expect("owner module should resolve");
    let effect = lower
        .modules
        .module_at(owner, owner, &Name("effect".into()), site)
        .found()
        .expect("act companion should resolve");
    let child = lower
        .modules
        .module_at(effect, effect, &Name("child".into()), site)
        .found()
        .expect("act companion child should resolve");
    let grandchild = lower
        .modules
        .module_at(child, child, &Name("grandchild".into()), site)
        .found()
        .expect("act companion grandchild should resolve");
    let sibling = lower
        .modules
        .module_at(owner, owner, &Name("sibling".into()), site)
        .found()
        .expect("act companion sibling should resolve");
    let unrelated = lower
        .modules
        .module_at(root, root, &Name("unrelated".into()), site)
        .found()
        .expect("unrelated module should resolve");
    let effect_path = &[Name("owner".into()), Name("effect".into())];
    let ping = Name("ping".into());

    for (relationship, requester) in [
        ("same module", effect),
        ("child", child),
        ("grandchild", grandchild),
    ] {
        let lookup = lower
            .modules
            .act_operation_decl_at(requester, effect_path, &ping, site);
        assert!(matches!(lookup, Lookup::Found(_)), "{relationship}");
    }

    for (relationship, requester) in [("sibling", sibling), ("unrelated", unrelated)] {
        let lookup = lower
            .modules
            .act_operation_decl_at(requester, effect_path, &ping, site);
        assert!(
            matches!(lookup, Lookup::Private(_)),
            "{relationship}: {lookup:?}"
        );
        let operations = lower
            .modules
            .act_operation_decls_at(requester, effect_path, site)
            .found()
            .expect("the public operation should keep the visible lookup result");
        assert_eq!(
            operations
                .into_iter()
                .map(|operation| operation.name)
                .collect::<Vec<_>>(),
            vec![Name("pong".into())],
            "{relationship}"
        );
    }
}

#[test]
fn registers_act_operation_value_defs_in_companion_scope() {
    let cst = parse("act out:\n  our say: int -> unit\nmy site = 1\n");
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let out = lower.modules.type_decls(root, &Name("out".into()))[0].clone();
    let companion = lower
        .modules
        .type_companion(out.id)
        .expect("act should create companion");
    let op_def = lower.modules.value_decls(companion, &Name("say".into()))[0].def;
    let op = lower
        .modules
        .act_operation_decl_by_def(op_def)
        .expect("operation value def should resolve to act operation");

    assert_eq!(op.effect.id, out.id);
    assert_eq!(op.name, Name("say".into()));
    assert_eq!(op.def, Some(op_def));
    assert_eq!(
        lower
            .modules
            .act_operation_decls_at(root, &[Name("out".into())], module_path_site())
            .found()
            .expect("local act operations should resolve")[0]
            .def,
        Some(op_def)
    );
}

#[test]
fn act_type_vars_include_bare_application_chain() {
    let cst = parse("act parse 'item 'err 'pos 'snap:\n  our item: () -> 'item\n");
    let root = cst
        .descendants()
        .find(|child| child.kind() == SyntaxKind::ActDecl)
        .expect("act declaration");

    assert_eq!(
        act_type_var_names(&root),
        vec![
            "item".to_string(),
            "err".to_string(),
            "pos".to_string(),
            "snap".to_string()
        ]
    );
}

#[test]
fn registers_act_copy_body_in_destination_companion() {
    let cst = parse(
        "act loop:\n  my act last:\n    our break: () -> never\n  my act next = last\nmy site = 1\n",
    );
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let loop_act = lower.modules.type_decls(root, &Name("loop".into()))[0].clone();
    let loop_companion = lower
        .modules
        .type_companion(loop_act.id)
        .expect("outer act should create companion");
    let next = lower
        .modules
        .type_decls(loop_companion, &Name("next".into()))[0]
        .clone();
    let next_companion = lower
        .modules
        .type_companion(next.id)
        .expect("copied act should create companion");
    let ops = lower
        .modules
        .act_operation_decls_at(loop_companion, &[Name("next".into())], module_path_site())
        .found()
        .expect("copied act operations should resolve")
        .into_iter()
        .map(|op| op.name)
        .collect::<Vec<_>>();

    assert_eq!(ops, vec![Name("break".into())]);
    assert!(lower.modules.module_path(next_companion).segments.len() >= 2);
}

#[test]
fn act_copy_does_not_register_source_private_members_in_destination_companion() {
    let cst = parse(
        "act source:\n  my hidden = 1\n  our visible = 2\nact copy = source with:\n  our leak = 3\nmy site = 1\n",
    );
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let copy = lower.modules.type_decls(root, &Name("copy".into()))[0].clone();
    let companion = lower
        .modules
        .type_companion(copy.id)
        .expect("copied act should create companion");

    assert!(
        lower
            .modules
            .value_decls(companion, &Name("hidden".into()))
            .is_empty()
    );
    assert_eq!(
        lower
            .modules
            .value_decls(companion, &Name("visible".into()))
            .len(),
        1
    );
    assert_eq!(
        lower
            .modules
            .value_decls(companion, &Name("leak".into()))
            .len(),
        1
    );
}

#[test]
fn act_copy_does_not_inherit_source_private_operations() {
    let cst = parse(
        "act source:\n  my hidden: () -> never\n  our visible: () -> never\nact copy = source\nmy site = 1\n",
    );
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let site = lower.modules.value_decls(root, &Name("site".into()))[0].order;
    let ops = lower
        .modules
        .act_operation_decls_at(root, &[Name("copy".into())], site)
        .found()
        .expect("copied act operations should resolve")
        .into_iter()
        .map(|op| op.name)
        .collect::<Vec<_>>();

    assert_eq!(ops, vec![Name("visible".into())]);
}

#[test]
fn registers_act_copy_from_qualified_source_path() {
    let cst = parse(
        "mod effects:\n  act base:\n    our tick: () -> never\nact local = effects::base\nmy site = 1\n",
    );
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let local = lower.modules.type_decls(root, &Name("local".into()))[0].clone();
    let site = lower.modules.value_decls(root, &Name("site".into()))[0].order;
    let ops = lower
        .modules
        .act_operation_decls_at(root, &[Name("local".into())], site)
        .found()
        .expect("qualified copied act operations should resolve")
        .into_iter()
        .map(|op| op.name)
        .collect::<Vec<_>>();

    assert_eq!(ops, vec![Name("tick".into())]);
    assert!(lower.modules.type_companion(local.id).is_some());
}

#[test]
fn registers_act_copy_from_import_alias_after_import_view() {
    let cst = parse(
        "mod effects:\n  act base:\n    our tick: () -> never\nuse effects::base as copied\nact local = copied\nmy site = 1\n",
    );
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let site = lower.modules.value_decls(root, &Name("site".into()))[0].order;
    let ops = lower
        .modules
        .act_operation_decls_at(root, &[Name("local".into())], site)
        .found()
        .expect("imported copied act operations should resolve")
        .into_iter()
        .map(|op| op.name)
        .collect::<Vec<_>>();

    assert_eq!(ops, vec![Name("tick".into())]);
}

#[test]
fn resolves_act_copy_type_arg_aliases() {
    let cst = parse("act source 'a:\n  our tick: 'a -> never\nact local 't = source 't\n");
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let local = lower.modules.type_decls(root, &Name("local".into()))[0].clone();
    let resolved = lower
        .modules
        .resolved_act_copy(local.id)
        .expect("act copy type should resolve");

    assert_eq!(
        resolved.type_var_aliases,
        vec![("a".to_string(), "t".to_string())]
    );
}

#[test]
fn records_act_type_vars_as_module_metadata() {
    let cst = parse("act source 'a 'b:\n  our tick: unit -> never\n");
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let source = lower.modules.type_decls(root, &Name("source".into()))[0].clone();

    assert_eq!(
        lower.modules.act_type_vars(source.id),
        Some(["a".to_string(), "b".to_string()].as_slice())
    );
}

#[test]
fn act_resolution_accepts_strict_function_type_args_without_aliasing() {
    let cst = parse(
        "type a\ntype b\ntype c\nact source 'f:\n  our tick: unit -> never\nact local = source (a -> b -> c)\n",
    );
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let local = lower.modules.type_decls(root, &Name("local".into()))[0].clone();
    let resolved = lower
        .modules
        .resolved_act_copy(local.id)
        .expect("strict act use should resolve");

    assert!(resolved.type_var_aliases.is_empty());
}

#[test]
fn act_resolution_rejects_non_act_head() {
    let cst = parse("type source\nact local = source\n");
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let local = lower.modules.type_decls(root, &Name("local".into()))[0].clone();

    assert!(lower.modules.resolved_act_copy(local.id).is_none());
}

#[test]
fn registers_act_body_as_companion_module_operations_and_methods() {
    let cst = parse("act out:\n  our say: int -> unit\n  our x.clear = x\nmy site = 1\n");
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let out = lower.modules.type_decls(root, &Name("out".into()))[0].clone();
    let companion = lower
        .modules
        .type_companion(out.id)
        .expect("act body should create a companion module");
    let methods = lower.modules.act_methods(out.id);

    assert_eq!(
        lower.modules.module_decls(root, &Name("out".into()))[0].module,
        companion
    );
    assert_eq!(methods.len(), 1);
    assert_eq!(methods[0].name, Name("clear".into()));
    assert_eq!(methods[0].receiver, Name("x".into()));
    let operation = lower.modules.value_decls(companion, &Name("say".into()));
    assert_eq!(operation.len(), 1);
    assert!(lower.modules.is_act_operation_def(operation[0].def));
}

#[test]
fn registers_role_body_as_companion_module_role_methods() {
    let cst = parse("role Display 'a:\n  type out\n  our x.display: out\nmy site = 1\n");
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let display = lower.modules.type_decls(root, &Name("Display".into()))[0].clone();
    let companion = lower
        .modules
        .type_companion(display.id)
        .expect("role body should create a companion module");
    let methods = lower.modules.role_methods(display.id);

    assert_eq!(lower.modules.role_inputs(display.id), &["a".to_string()]);
    assert_eq!(
        lower.modules.role_associated(display.id),
        &["out".to_string()]
    );
    assert_eq!(
        lower.modules.module_decls(root, &Name("Display".into()))[0].module,
        companion
    );
    assert_eq!(
        lower
            .modules
            .value_decls(companion, &Name("display".into()))
            .len(),
        1
    );
    assert_eq!(methods.len(), 1);
    assert_eq!(methods[0].name, Name("display".into()));
    assert_eq!(methods[0].receiver, Some(Name("x".into())));
    assert_eq!(methods[0].vis, Vis::Our);
}

#[test]
fn lexical_type_lookup_converts_child_site_to_parent_module_order() {
    let cst = parse("type User\nmod m:\n  my y = 1\n");
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let m = lower.modules.module_decls(root, &Name("m".into()))[0].module;
    let y_order = lower.modules.value_decls(m, &Name("y".into()))[0].order;

    assert_eq!(
        lower
            .modules
            .lexical_type_at(m, &Name("User".into()), y_order)
            .map(|decl| decl.kind),
        Some(ModuleTypeKind::TypeAlias)
    );
}

#[test]
fn ordered_lookup_prefers_last_previous_decl() {
    let cst = parse("my a = 1\nmy b = a\nmy a = 2\n");
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let a_decls = lower.modules.value_decls(root, &Name("a".into()));
    let b_order = lower.modules.value_decls(root, &Name("b".into()))[0].order;

    assert_eq!(a_decls.len(), 2);
    assert_eq!(
        lower
            .modules
            .value_at(root, root, &Name("a".into()), b_order),
        Some(a_decls[0].def)
    );
}

#[test]
fn ordered_lookup_uses_nearest_following_decl_when_no_previous_decl_exists() {
    let cst = parse("my b = a\nmy a = 1\nmy a = 2\n");
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let a_decls = lower.modules.value_decls(root, &Name("a".into()));
    let b_order = lower.modules.value_decls(root, &Name("b".into()))[0].order;

    assert_eq!(
        lower
            .modules
            .value_at(root, root, &Name("a".into()), b_order),
        Some(a_decls[0].def)
    );
}

#[test]
fn lexical_lookup_converts_child_site_to_parent_module_order() {
    let cst = parse("mod m:\n  my y = x\nmy x = 1\n");
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let m = lower.modules.module_decls(root, &Name("m".into()))[0].module;
    let y_order = lower.modules.value_decls(m, &Name("y".into()))[0].order;
    let x = lower.modules.value_decls(root, &Name("x".into()))[0].def;

    assert_eq!(
        lower
            .modules
            .lexical_value_at(m, &Name("x".into()), y_order),
        Some(x)
    );
}

#[test]
fn lexical_lookup_prefers_parent_decl_before_child_module_over_later_parent_decl() {
    let cst = parse("my x = 0\nmod m:\n  my y = x\nmy x = 1\n");
    let lower = lower_module_map(&cst);
    let root = lower.modules.root_id();
    let m = lower.modules.module_decls(root, &Name("m".into()))[0].module;
    let y_order = lower.modules.value_decls(m, &Name("y".into()))[0].order;
    let x_decls = lower.modules.value_decls(root, &Name("x".into()));

    assert_eq!(
        lower
            .modules
            .lexical_value_at(m, &Name("x".into()), y_order),
        Some(x_decls[0].def)
    );
}

#[test]
fn my_visibility_direct_namespace_matrix_keeps_requester_fixed() {
    let mut lower = lower_source(
        "pub mod owner:\n  my value = 1\n  type Hidden\n  my mod private:\n    pub value = 2\n  pub mod child:\n    pub mod grandchild:\n      pub witness = 0\npub mod sibling:\n  pub witness = 0\npub mod unrelated:\n  pub witness = 0\n",
    );
    let modules = &lower.modules;
    let root = modules.root_id();
    let owner = modules.module_decls(root, &Name("owner".into()))[0].module;
    let child = modules.module_decls(owner, &Name("child".into()))[0].module;
    let grandchild = modules.module_decls(child, &Name("grandchild".into()))[0].module;
    let sibling = modules.module_decls(root, &Name("sibling".into()))[0].module;
    let unrelated = modules.module_decls(root, &Name("unrelated".into()))[0].module;
    assert_eq!(
        modules.value_decls(owner, &Name("value".into()))[0].vis,
        Vis::My
    );
    assert!(!modules.is_descendant_or_same(sibling, owner));
    let hidden = lower.modules.nodes[owner.0].types[&Name("Hidden".into())].clone();
    let hidden_origin = lower
        .modules
        .private_origin_for(owner, Vis::My, None)
        .expect("my visibility has an origin");
    for id in hidden {
        let decl = &mut lower.modules.nodes[owner.0].decls[id.0];
        decl.vis = Vis::My;
        decl.private_origin = Some(hidden_origin);
    }
    let modules = &lower.modules;
    let site = ModuleOrder::from_index(u32::MAX);
    let value_path = [Name("owner".into()), Name("value".into())];
    let type_path = [Name("owner".into()), Name("Hidden".into())];
    let private_path = [Name("owner".into()), Name("private".into())];
    assert!(matches!(
        modules.value_at(sibling, owner, &Name("value".into()), site),
        Lookup::Private(_)
    ));

    for (relationship, requester, allowed) in [
        ("same module", owner, true),
        ("child", child, true),
        ("grandchild", grandchild, true),
        ("parent reaching into child", root, false),
        ("sibling", sibling, false),
        ("unrelated", unrelated, false),
    ] {
        let value = modules.value_path_at(requester, &value_path, site);
        let ty = modules.type_path_at(requester, &type_path, site);
        let module = modules.module_path_with_imports_from(requester, &private_path, site);
        if allowed {
            assert!(matches!(value, Lookup::Found(_)), "value {relationship}");
            assert!(matches!(ty, Lookup::Found(_)), "type {relationship}");
            assert!(matches!(module, Lookup::Found(_)), "module {relationship}");
        } else {
            assert!(
                matches!(value, Lookup::Private(_)),
                "value {relationship}: {value:?}"
            );
            assert!(matches!(ty, Lookup::Private(_)), "type {relationship}");
            assert!(
                matches!(module, Lookup::Private(_)),
                "module {relationship}"
            );
        }
    }
}
