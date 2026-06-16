mod tests {
    use super::super::*;

    fn build_annotation(src: &str) -> AnnType {
        let root = parse(src);
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let type_expr = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::TypeExpr)
            .expect("source should contain a type annotation");
        build_ann_type_expr(&lower.modules, module, site, &type_expr)
            .expect("annotation should build")
    }

    fn build_annotation_error(src: &str) -> AnnBuildError {
        let root = parse(src);
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let type_expr = root
            .descendants()
            .find(|node| node.kind() == SyntaxKind::TypeExpr)
            .expect("source should contain a type annotation");
        build_ann_type_expr(&lower.modules, module, site, &type_expr)
            .expect_err("annotation should fail")
    }

    #[test]
    fn builds_builtin_annotations() {
        assert_eq!(
            build_annotation("my site: int = 1\n"),
            AnnType::Builtin(BuiltinType::Int)
        );
        assert_eq!(
            build_annotation("my site: float = 1\n"),
            AnnType::Builtin(BuiltinType::Float)
        );
        assert_eq!(
            build_annotation("my site: unit = 1\n"),
            AnnType::Builtin(BuiltinType::Unit)
        );
    }

    #[test]
    fn builds_unit_paren_annotation_as_builtin_unit() {
        assert_eq!(
            build_annotation("my site: () = 1\n"),
            AnnType::Builtin(BuiltinType::Unit)
        );
    }

    #[test]
    fn builds_local_named_annotation() {
        let root = parse("type User\nmy site: User = 1\n");
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let user = lower.modules.type_decls(module, &Name("User".into()))[0].id;
        let type_expr = first_type_expr(&root);

        assert_eq!(
            build_ann_type_expr(&lower.modules, module, site, &type_expr),
            Ok(AnnType::Named(user))
        );
    }

    #[test]
    fn builds_imported_alias_and_glob_annotations() {
        let alias_root = parse("mod m:\n  type User\nuse m::User as Alias\nmy site: Alias = 1\n");
        let alias_lower = crate::lower_module_map(&alias_root);
        let alias_module = alias_lower.modules.root_id();
        let alias_site = alias_lower
            .modules
            .value_decls(alias_module, &Name("site".into()))[0]
            .order;
        let m = alias_lower
            .modules
            .module_decls(alias_module, &Name("m".into()))[0]
            .module;
        let user = alias_lower.modules.type_decls(m, &Name("User".into()))[0].id;

        assert_eq!(
            build_ann_type_expr(
                &alias_lower.modules,
                alias_module,
                alias_site,
                &first_type_expr(&alias_root)
            ),
            Ok(AnnType::Named(user))
        );

        let glob_root = parse("mod m:\n  type User\nuse m::*\nmy site: User = 1\n");
        let glob_lower = crate::lower_module_map(&glob_root);
        let glob_module = glob_lower.modules.root_id();
        let glob_site = glob_lower
            .modules
            .value_decls(glob_module, &Name("site".into()))[0]
            .order;
        let m = glob_lower
            .modules
            .module_decls(glob_module, &Name("m".into()))[0]
            .module;
        let user = glob_lower.modules.type_decls(m, &Name("User".into()))[0].id;

        assert_eq!(
            build_ann_type_expr(
                &glob_lower.modules,
                glob_module,
                glob_site,
                &first_type_expr(&glob_root)
            ),
            Ok(AnnType::Named(user))
        );
    }

    #[test]
    fn builds_qualified_path_annotation() {
        let root = parse("mod std:\n  mod num:\n    type Int\nmy site: std::num::Int = 1\n");
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let std = lower.modules.module_decls(module, &Name("std".into()))[0].module;
        let num = lower.modules.module_decls(std, &Name("num".into()))[0].module;
        let int = lower.modules.type_decls(num, &Name("Int".into()))[0].id;

        assert_eq!(
            build_ann_type_expr(&lower.modules, module, site, &first_type_expr(&root)),
            Ok(AnnType::Named(int))
        );
    }

    #[test]
    fn builds_right_associative_function_annotations() {
        assert_eq!(
            build_annotation("my site: int -> float -> unit = 1\n"),
            AnnType::Function {
                param: Box::new(AnnType::Builtin(BuiltinType::Int)),
                arg_eff: None,
                ret_eff: None,
                ret: Box::new(AnnType::Function {
                    param: Box::new(AnnType::Builtin(BuiltinType::Float)),
                    arg_eff: None,
                    ret_eff: None,
                    ret: Box::new(AnnType::Builtin(BuiltinType::Unit)),
                }),
            }
        );
    }

    #[test]
    fn builds_effect_row_annotations() {
        let root = parse("type io\ntype Foo\nmy site: Foo '['e] = 1\n");
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let foo = lower.modules.type_decls(module, &Name("Foo".into()))[0].id;

        assert_eq!(
            build_ann_type_expr(&lower.modules, module, site, &first_type_expr(&root)),
            Ok(ann_apply(
                AnnType::Named(foo),
                vec![AnnType::EffectRow(ann_row(Vec::new(), Some(("e", 0))))]
            ))
        );

        let row_root = parse("type io\nmy site: '[io] = 1\n");
        let row_lower = crate::lower_module_map(&row_root);
        let row_module = row_lower.modules.root_id();
        let row_site = row_lower
            .modules
            .value_decls(row_module, &Name("site".into()))[0]
            .order;
        let io = row_lower.modules.type_decls(row_module, &Name("io".into()))[0].id;

        assert_eq!(
            build_ann_type_expr(
                &row_lower.modules,
                row_module,
                row_site,
                &first_type_expr(&row_root)
            ),
            Ok(AnnType::EffectRow(ann_row(vec![AnnType::Named(io)], None)))
        );
    }

    #[test]
    fn builds_wildcard_effect_row_atom() {
        assert_eq!(
            build_annotation("my site: [_] int = 1\n"),
            AnnType::Effectful {
                eff: AnnEffectRow {
                    items: vec![AnnEffectAtom::Wildcard],
                    tail: None,
                },
                ret: Box::new(AnnType::Builtin(BuiltinType::Int)),
            }
        );
    }

    #[test]
    fn shares_type_vars_by_name_in_function_annotation() {
        let root = parse("type io\nmy site: 'a [io; 'e] -> ['e] 'a = 1\n");
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let io = lower.modules.type_decls(module, &Name("io".into()))[0].id;

        assert_eq!(
            build_ann_type_expr(&lower.modules, module, site, &first_type_expr(&root)),
            Ok(AnnType::Function {
                param: Box::new(ann_var_id("a", 0)),
                arg_eff: Some(ann_row(vec![AnnType::Named(io)], Some(("e", 1)))),
                ret_eff: Some(ann_row(Vec::new(), Some(("e", 1)))),
                ret: Box::new(ann_var_id("a", 0)),
            })
        );
    }

    #[test]
    fn shared_builder_reuses_type_vars_across_type_exprs() {
        let root = parse("my left: 'a = 1\nmy right: 'a = 2\n");
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("right".into()))[0].order;
        let mut builder = AnnTypeBuilder::new(&lower.modules, module, site);
        let mut type_exprs = root
            .descendants()
            .filter(|node| node.kind() == SyntaxKind::TypeExpr);
        let left = type_exprs.next().expect("left annotation should exist");
        let right = type_exprs.next().expect("right annotation should exist");

        assert_eq!(builder.build_type_expr(&left), Ok(ann_var_id("a", 0)));
        assert_eq!(builder.build_type_expr(&right), Ok(ann_var_id("a", 0)));
    }

    #[test]
    fn self_alias_expands_in_builder_type_var_scope() {
        let root = parse("type box 'a\nmy site: self = 1\n");
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let owner = lower.modules.type_decls(module, &Name("box".into()))[0].id;
        let mut builder = AnnTypeBuilder::with_self_alias(
            &lower.modules,
            module,
            site,
            AnnSelfAlias {
                owner,
                type_vars: vec!["a".into()],
            },
        );

        assert_eq!(
            builder.build_type_expr(&first_type_expr(&root)),
            Ok(ann_apply(AnnType::Named(owner), vec![ann_var_id("a", 0)]))
        );
    }

    #[test]
    fn reports_unresolved_type_name() {
        assert_eq!(
            build_annotation_error("my site: Missing = 1\n"),
            AnnBuildError::UnresolvedTypeName {
                path: vec![Name("Missing".into())]
            }
        );
    }

    #[test]
    fn builds_type_application_annotations() {
        let root = parse(
            "type list\ntype dict\ntype string\nmod std:\n  mod num:\n    type Int\nmy site: dict(string, std::num::Int) = 1\n",
        );
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let dict = lower.modules.type_decls(module, &Name("dict".into()))[0].id;
        let string = lower.modules.type_decls(module, &Name("string".into()))[0].id;
        let std = lower.modules.module_decls(module, &Name("std".into()))[0].module;
        let num = lower.modules.module_decls(std, &Name("num".into()))[0].module;
        let int = lower.modules.type_decls(num, &Name("Int".into()))[0].id;

        assert_eq!(
            build_ann_type_expr(&lower.modules, module, site, &first_type_expr(&root)),
            Ok(ann_apply(
                AnnType::Named(dict),
                vec![AnnType::Named(string), AnnType::Named(int)]
            ))
        );

        let list_root = parse("type list\nmy site: list int = 1\n");
        let list_lower = crate::lower_module_map(&list_root);
        let list_module = list_lower.modules.root_id();
        let list_site = list_lower
            .modules
            .value_decls(list_module, &Name("site".into()))[0]
            .order;
        let list = list_lower
            .modules
            .type_decls(list_module, &Name("list".into()))[0]
            .id;

        assert_eq!(
            build_ann_type_expr(
                &list_lower.modules,
                list_module,
                list_site,
                &first_type_expr(&list_root)
            ),
            Ok(ann_apply(
                AnnType::Named(list),
                vec![AnnType::Builtin(BuiltinType::Int)]
            ))
        );

        let result_root = parse("type result\nmy site: result 't = 1\n");
        let result_lower = crate::lower_module_map(&result_root);
        let result_module = result_lower.modules.root_id();
        let result_site = result_lower
            .modules
            .value_decls(result_module, &Name("site".into()))[0]
            .order;
        let result = result_lower
            .modules
            .type_decls(result_module, &Name("result".into()))[0]
            .id;

        assert_eq!(
            build_ann_type_expr(
                &result_lower.modules,
                result_module,
                result_site,
                &first_type_expr(&result_root)
            ),
            Ok(ann_apply(AnnType::Named(result), vec![ann_var_id("t", 0)]))
        );
    }

    #[test]
    fn effect_row_type_argument_lowers_as_effect_tail() {
        let root = parse("type io\ntype Box\nmy site: Box '[io] = 1\n");
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let io = lower.modules.type_decls(module, &Name("io".into()))[0].id;
        let expected = type_decl_path(&lower.modules, io);
        let ann = build_ann_type_expr(&lower.modules, module, site, &first_type_expr(&root))
            .expect("annotation should build");
        let mut infer = crate::Arena::new();

        let bounds = AnnConstraintLowerer::new(&mut infer, &lower.modules)
            .lower_value_bounds(&ann)
            .expect("annotation constraints should lower");

        let types = infer.constraints().types();
        let Pos::Con(_, args) = types.pos(bounds.pos) else {
            panic!("expected constructor lower bound");
        };
        let [arg] = args.as_slice() else {
            panic!("expected one type argument");
        };
        let Neu::Bounds(lower, upper) = types.neu(*arg) else {
            panic!("expected invariant type argument bounds");
        };
        assert!(
            matches!(types.pos(*lower), Pos::Con(path, args) if path == &expected && args.is_empty()),
            "effect row argument lower should expose the row item as the effect tail type, got {:?}",
            types.pos(*lower)
        );
        let Neg::Stack { inner, weight } = types.neg(*upper) else {
            panic!(
                "effect row argument upper should be subtractable, got {:?}",
                types.neg(*upper)
            );
        };
        assert!(matches!(types.neg(*inner), Neg::Var(_)));
        let entry = single_stack_entry(weight);
        assert!(weight_has_set_path(weight, entry.id, &expected));
    }

    #[test]
    fn builds_tuple_annotation() {
        assert_eq!(
            build_annotation("my site: (int, float) = 1\n"),
            AnnType::Tuple(vec![
                AnnType::Builtin(BuiltinType::Int),
                AnnType::Builtin(BuiltinType::Float),
            ])
        );
    }

    #[test]
    fn connects_effectful_annotation_with_stacked_inner_lower() {
        let root = parse("type handled\nmy site: [handled] 'a = 1\n");
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let handled = lower.modules.type_decls(module, &Name("handled".into()))[0].id;
        let ann = build_ann_type_expr(&lower.modules, module, site, &first_type_expr(&root))
            .expect("annotation should build");
        let mut infer = crate::Arena::new();
        let value = infer.fresh_type_var();
        let effect = infer.fresh_type_var();

        let subtracts = AnnConstraintLowerer::new(&mut infer, &lower.modules)
            .connect_computation(AnnComputationTarget { value, effect }, &ann)
            .expect("annotation constraints should lower");

        assert_eq!(subtracts.len(), 1);
        let expected = type_decl_path(&lower.modules, handled);
        let bounds = infer
            .constraints()
            .bounds()
            .of(effect)
            .expect("effect should receive stacked inner lower bound");
        // 注釈残差は fresh な内側変数として立ち、push 重み付きで effect の下界に入る。
        // effect 自身への self edge は作らない（replay で重みが際限なく合成されるため）。
        assert!(
            bounds.lowers().iter().any(|bound| {
                matches!(infer.constraints().types().pos(bound.pos), Pos::Var(var) if *var != effect)
                    && weight_has_set_path(&bound.weights.left, subtracts[0], &expected)
            }),
            "effect bounds: {:?}",
            bounds
        );
        assert!(
            !bounds.lowers().iter().any(|bound| {
                matches!(infer.constraints().types().pos(bound.pos), Pos::Var(var) if *var == effect)
                    && !bound.weights.is_empty()
            }),
            "effect must not have weighted self edges: {:?}",
            bounds
        );
    }

    #[test]
    fn tail_only_effectful_annotation_is_current_effect() {
        let root = parse("my site: ['e] 'a = 1\n");
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let ann = build_ann_type_expr(&lower.modules, module, site, &first_type_expr(&root))
            .expect("annotation should build");
        let mut infer = crate::Arena::new();
        let value = infer.fresh_type_var();
        let effect = infer.fresh_type_var();

        let connection = AnnConstraintLowerer::new(&mut infer, &lower.modules)
            .connect_computation_detailed(AnnComputationTarget { value, effect }, &ann)
            .expect("annotation constraints should lower");

        assert_eq!(connection.subtracts, Vec::new());
        let stack = connection
            .effect_stack
            .expect("effectful annotation should report an effect connection");
        assert_eq!(stack.subtracts, Vec::new());
        assert!(stack.weight.is_empty());
        let tail = stack.inner;
        let types = infer.constraints().types();
        let effect_bounds = infer
            .constraints()
            .bounds()
            .of(effect)
            .expect("target effect should receive tail relation");
        assert!(
            effect_bounds
                .lowers()
                .iter()
                .any(|bound| matches!(types.pos(bound.pos), Pos::Var(var) if *var == tail)),
            "effect bounds: {:?}",
            effect_bounds
        );
        let tail_bounds = infer
            .constraints()
            .bounds()
            .of(tail)
            .expect("tail should receive target effect relation");
        assert!(
            tail_bounds
                .lowers()
                .iter()
                .any(|bound| matches!(types.pos(bound.pos), Pos::Var(var) if *var == effect)),
            "tail bounds: {:?}",
            tail_bounds
        );
    }

    #[test]
    fn function_return_effect_annotation_wraps_output_computation_with_stack() {
        let root = parse("type io\ntype handled\nmy site: 'a [io] -> [handled] 'a = 1\n");
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let ann = build_ann_type_expr(&lower.modules, module, site, &first_type_expr(&root))
            .expect("annotation should build");
        let mut infer = crate::Arena::new();
        let target = infer.fresh_type_var();

        AnnConstraintLowerer::new(&mut infer, &lower.modules)
            .connect_value(target, &ann)
            .expect("annotation constraints should lower");

        let bounds = infer
            .constraints()
            .bounds()
            .of(target)
            .expect("target should receive function lower bound");
        let types = infer.constraints().types();
        let fun = bounds
            .lowers()
            .iter()
            .find_map(|bound| match types.pos(bound.pos) {
                Pos::Fun { ret_eff, ret, .. } => Some((*ret_eff, *ret)),
                _ => None,
            })
            .expect("function annotation should lower to function bound");

        let subtract = match types.pos(fun.0) {
            Pos::Stack { inner, weight } => {
                assert!(matches!(types.pos(*inner), Pos::Var(_)));
                let entry = single_stack_entry(weight);
                assert_eq!(entry.pops, 0);
                assert_eq!(entry.stack.len(), 1);
                entry.id
            }
            other => panic!("expected stacked return effect, got {other:?}"),
        };
        assert_non_subtract_var(types, fun.1, subtract);
    }

    #[test]
    fn function_arg_effect_annotation_adds_only_lower_row_to_fresh_arg_effect() {
        let root = parse("type io\nmy site: 'a [io] -> 'a = 1\n");
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let ann = build_ann_type_expr(&lower.modules, module, site, &first_type_expr(&root))
            .expect("annotation should build");
        let mut infer = crate::Arena::new();
        let target = infer.fresh_type_var();

        AnnConstraintLowerer::new(&mut infer, &lower.modules)
            .connect_value(target, &ann)
            .expect("annotation constraints should lower");

        let types = infer.constraints().types();
        let fun = infer
            .constraints()
            .bounds()
            .of(target)
            .expect("target should receive function lower bound")
            .lowers()
            .iter()
            .find_map(|bound| match types.pos(bound.pos) {
                Pos::Fun { arg_eff, .. } => Some(*arg_eff),
                _ => None,
            })
            .expect("function annotation should lower to function bound");
        let arg_effect = match types.neg(fun) {
            Neg::Var(var) => *var,
            other => panic!("expected arg effect variable, got {other:?}"),
        };
        let bounds = infer
            .constraints()
            .bounds()
            .of(arg_effect)
            .expect("arg effect should receive row lower bound");

        assert!(
            !bounds
                .uppers()
                .iter()
                .any(|bound| matches!(types.neg(bound.neg), Neg::Row(_, _)))
        );
        assert!(
            bounds.lowers().iter().any(|bound| {
                matches!(types.pos(bound.pos), Pos::Row(items) if !items.is_empty())
            })
        );
    }

    #[test]
    fn function_return_effect_with_tail_uses_fresh_stacked_proxy() {
        let root = parse("type handled\nmy site: 'a -> [handled; 'e] 'a = 1\n");
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let ann = build_ann_type_expr(&lower.modules, module, site, &first_type_expr(&root))
            .expect("annotation should build");
        let mut infer = crate::Arena::new();
        let target = infer.fresh_type_var();

        let subtracts = AnnConstraintLowerer::new(&mut infer, &lower.modules)
            .connect_value(target, &ann)
            .expect("annotation constraints should lower");

        let [subtract] = subtracts.as_slice() else {
            panic!("expected one subtract id, got {subtracts:?}");
        };
        let types = infer.constraints().types();
        let ret_eff = infer
            .constraints()
            .bounds()
            .of(target)
            .expect("target should receive function lower bound")
            .lowers()
            .iter()
            .find_map(|bound| match types.pos(bound.pos) {
                Pos::Fun { ret_eff, .. } => Some(*ret_eff),
                _ => None,
            })
            .expect("function annotation should lower to function bound");
        let proxy = match types.pos(ret_eff) {
            Pos::Stack { inner, weight } if weight.contains(*subtract) => match types.pos(*inner) {
                Pos::Var(proxy) => *proxy,
                other => panic!("expected proxy variable, got {other:?}"),
            },
            other => panic!("expected stacked return effect, got {other:?}"),
        };

        let proxy_bounds = infer
            .constraints()
            .bounds()
            .of(proxy)
            .expect("proxy should receive tail lower bound");
        assert!(
            proxy_bounds
                .lowers()
                .iter()
                .any(|bound| { matches!(types.pos(bound.pos), Pos::Var(tail) if *tail != proxy) })
        );
    }

    #[test]
    fn computation_connection_does_not_add_weighted_self_edges() {
        let root = parse("type handled\nmy site: 'a -> [handled] 'a = 1\n");
        let lower = crate::lower_module_map(&root);
        let module = lower.modules.root_id();
        let site = lower.modules.value_decls(module, &Name("site".into()))[0].order;
        let ann = build_ann_type_expr(&lower.modules, module, site, &first_type_expr(&root))
            .expect("annotation should build");
        let mut infer = crate::Arena::new();
        let value = infer.fresh_type_var();
        let effect = infer.fresh_type_var();

        AnnConstraintLowerer::new(&mut infer, &lower.modules)
            .connect_computation(AnnComputationTarget { value, effect }, &ann)
            .expect("annotation constraints should lower");

        // 重み付き self edge は bounds replay の合成で重みが際限なく育つため作らない。
        for target in [value, effect] {
            let Some(bounds) = infer.constraints().bounds().of(target) else {
                continue;
            };
            assert!(
                !bounds.lowers().iter().any(|bound| {
                    matches!(
                        infer.constraints().types().pos(bound.pos),
                        Pos::Var(var) if *var == target && !bound.weights.is_empty()
                    )
                }),
                "weighted self edge on {target:?}: {bounds:?}"
            );
        }
    }

    fn parse(src: &str) -> Cst {
        SyntaxNode::new_root(parser::parse_module_to_green(src))
    }

    fn type_decl_path(modules: &ModuleTable, id: TypeDeclId) -> Vec<String> {
        let decl = modules.type_decl_by_id(id).expect("type decl");
        modules
            .type_decl_path(&decl)
            .segments
            .into_iter()
            .map(|name| name.0)
            .collect()
    }

    fn single_stack_entry(weight: &StackWeight) -> &poly::types::StackWeightEntry {
        let [entry] = weight.entries() else {
            panic!("expected one stack entry, got {:?}", weight.entries());
        };
        entry
    }

    fn weight_has_set_path(
        weight: &StackWeight,
        subtract: SubtractId,
        expected: &[String],
    ) -> bool {
        weight.entries().iter().any(|entry| {
            entry.id == subtract
                && entry.stack.iter().any(|subtractability| {
                    matches!(
                        subtractability,
                        Subtractability::Set(path, args) if path == expected && args.is_empty()
                    )
                })
        })
    }

    fn assert_non_subtract_var(
        types: &poly::types::TypeArena,
        pos: PosId,
        subtract: SubtractId,
    ) -> TypeVar {
        let Pos::NonSubtract(inner, actual) = types.pos(pos) else {
            panic!(
                "expected non-subtract return value, got {:?}",
                types.pos(pos)
            );
        };
        assert_eq!(*actual, subtract);
        match types.pos(*inner) {
            Pos::Var(var) => *var,
            other => panic!("expected non-subtract inner var, got {other:?}"),
        }
    }

    fn first_type_expr(root: &Cst) -> Cst {
        root.descendants()
            .find(|node| node.kind() == SyntaxKind::TypeExpr)
            .expect("source should contain a type annotation")
    }

    fn ann_var_id(name: &str, id: u32) -> AnnType {
        AnnType::Var(AnnTypeVar {
            id: AnnTypeVarId(id),
            name: name.to_string(),
        })
    }

    fn ann_apply(callee: AnnType, args: Vec<AnnType>) -> AnnType {
        AnnType::Apply {
            callee: Box::new(callee),
            args,
        }
    }

    fn ann_row(items: Vec<AnnType>, tail: Option<(&str, u32)>) -> AnnEffectRow {
        AnnEffectRow {
            items: items.into_iter().map(AnnEffectAtom::Type).collect(),
            tail: tail.map(|(name, id)| AnnTypeVar {
                id: AnnTypeVarId(id),
                name: name.to_string(),
            }),
        }
    }
}
