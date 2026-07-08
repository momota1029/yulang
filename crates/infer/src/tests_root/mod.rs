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
fn consecutive_line_doc_comments_stack_for_following_binding() {
    let lower = lower_source("-- first\n-- second\nmy x = 1\n");
    let x = value_def(&lower, "x");
    let doc = lower
        .modules
        .def_doc_comment(x)
        .expect("stacked line doc comments should attach to x");

    assert_eq!(
        doc_unit_kinds(doc),
        vec![DocCommentKind::Line, DocCommentKind::Line]
    );
    assert_eq!(
        doc_unit_texts(doc),
        vec!["-- first".to_string(), "-- second".to_string()]
    );
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
        .into_iter()
        .map(|op| op.name)
        .collect::<Vec<_>>();

    assert_eq!(ops, vec![Name("say".into()), Name("write".into())]);
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
            .act_operation_decls_at(root, &[Name("out".into())], module_path_site())[0]
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
        lower.modules.value_at(root, &Name("a".into()), b_order),
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
        lower.modules.value_at(root, &Name("a".into()), b_order),
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
