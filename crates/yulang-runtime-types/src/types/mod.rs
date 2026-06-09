use std::collections::{BTreeMap, BTreeSet, HashSet};

use yulang_typed_ir as typed_ir;

use crate::ir::{
    Expr, ExprKind, JoinEvidence, MatchArm, Pattern, RecordExprField, RecordPatternField,
    RecordSpreadExpr, RecordSpreadPattern, ResumeBinding, Stmt, Type as RuntimeType,
};

mod choice;
mod compat;
mod core_view;
mod effect;
mod meaning;
mod project;
mod runtime;
mod shape;
mod substitution;

pub use choice::*;
pub use compat::*;
pub use core_view::*;
pub use effect::effect_is_empty;
pub use effect::*;
pub use meaning::*;
pub use project::*;
pub use runtime::*;
pub use shape::*;
pub use substitution::*;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn project_runtime_type_erases_observation_intersections() {
        let label = named("std::flow::label_loop::label");
        let raw = typed_ir::Type::Inter(vec![
            typed_ir::Type::Var(typed_ir::TypeVar("t0".to_string())),
            typed_ir::Type::Fun {
                param: Box::new(typed_ir::Type::Union(vec![
                    typed_ir::Type::Var(typed_ir::TypeVar("t1".to_string())),
                    label.clone(),
                ])),
                param_effect: Box::new(typed_ir::Type::Never),
                ret_effect: Box::new(typed_ir::Type::Row {
                    items: Vec::new(),
                    tail: Box::new(typed_ir::Type::Any),
                }),
                ret: Box::new(typed_ir::Type::Inter(vec![
                    typed_ir::Type::Var(typed_ir::TypeVar("t2".to_string())),
                    typed_ir::Type::Fun {
                        param: Box::new(named("unit")),
                        param_effect: Box::new(typed_ir::Type::Never),
                        ret_effect: Box::new(typed_ir::Type::Never),
                        ret: Box::new(typed_ir::Type::Any),
                    },
                ])),
            },
        ]);

        let projected = project_runtime_type(&raw);

        assert!(!contains_non_runtime_type(&projected), "{projected:?}");
        assert!(matches!(
            projected,
            typed_ir::Type::Fun { param, ret, .. }
                if *param == label && matches!(*ret, typed_ir::Type::Fun { .. })
        ));
    }

    #[test]
    fn project_runtime_type_keeps_principal_vars_only() {
        let principal = typed_ir::TypeVar("a".to_string());
        let observed = typed_ir::TypeVar("t0".to_string());
        let mut allowed = BTreeSet::new();
        allowed.insert(principal.clone());
        let raw = typed_ir::Type::Named {
            path: typed_ir::Path::from_name(typed_ir::Name("list".to_string())),
            args: vec![typed_ir::TypeArg::Type(typed_ir::Type::Union(vec![
                typed_ir::Type::Var(principal.clone()),
                typed_ir::Type::Var(observed),
            ]))],
        };

        let projected = project_runtime_type_with_vars(&raw, &allowed);

        assert_eq!(
            projected,
            typed_ir::Type::Named {
                path: typed_ir::Path::from_name(typed_ir::Name("list".to_string())),
                args: vec![typed_ir::TypeArg::Type(typed_ir::Type::Var(principal))],
            }
        );
    }

    #[test]
    fn project_runtime_type_erases_unallowed_value_vars() {
        let raw = typed_ir::Type::Fun {
            param: Box::new(typed_ir::Type::Var(typed_ir::TypeVar("t0".to_string()))),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(typed_ir::Type::Never),
            ret: Box::new(typed_ir::Type::Var(typed_ir::TypeVar("t1".to_string()))),
        };

        let projected = project_runtime_type_with_vars(&raw, &BTreeSet::new());

        assert_eq!(
            projected,
            typed_ir::Type::Fun {
                param: Box::new(typed_ir::Type::Unknown),
                param_effect: Box::new(typed_ir::Type::Never),
                ret_effect: Box::new(typed_ir::Type::Never),
                ret: Box::new(typed_ir::Type::Unknown),
            }
        );
    }

    #[test]
    fn project_runtime_hint_type_preserves_closed_value_union() {
        let raw = typed_ir::Type::Union(vec![named("bool"), named("int")]);

        let projected = project_runtime_hint_type_with_vars(&raw, &BTreeSet::new());

        assert_eq!(projected, raw);
    }

    #[test]
    fn project_hir_type_uses_unknown_for_unallowed_value_vars() {
        let raw = typed_ir::Type::Var(typed_ir::TypeVar("t0".to_string()));

        let projected = project_runtime_hir_type_with_vars(&raw, &BTreeSet::new());

        assert_eq!(projected, RuntimeType::Unknown);
    }

    #[test]
    fn project_hir_wraps_effect_variable_intersection_parameter() {
        let value = typed_ir::TypeVar("a".to_string());
        let effect = typed_ir::TypeVar("e".to_string());
        let mut allowed = BTreeSet::new();
        allowed.insert(value.clone());
        allowed.insert(effect.clone());
        let raw = typed_ir::Type::Fun {
            param: Box::new(typed_ir::Type::Var(value.clone())),
            param_effect: Box::new(typed_ir::Type::Inter(vec![
                typed_ir::Type::Var(effect.clone()),
                typed_ir::Type::Row {
                    items: Vec::new(),
                    tail: Box::new(typed_ir::Type::Any),
                },
            ])),
            ret_effect: Box::new(typed_ir::Type::Never),
            ret: Box::new(typed_ir::Type::Var(value.clone())),
        };

        let projected = project_runtime_hir_type_with_vars(&raw, &allowed);

        let RuntimeType::Fun { param, ret } = projected else {
            panic!("expected function");
        };
        assert_eq!(*ret, RuntimeType::value(typed_ir::Type::Var(value.clone())));
        assert_eq!(
            *param,
            RuntimeType::thunk(
                typed_ir::Type::Var(effect),
                RuntimeType::value(typed_ir::Type::Var(value))
            )
        );
    }

    #[test]
    fn project_runtime_type_prefers_concrete_lower_bound_for_type_arg() {
        let int = named("int");
        let raw = typed_ir::Type::Named {
            path: typed_ir::Path::from_name(typed_ir::Name("list".to_string())),
            args: vec![typed_ir::TypeArg::Bounds(typed_ir::TypeBounds {
                lower: Some(Box::new(typed_ir::Type::Union(vec![
                    typed_ir::Type::Var(typed_ir::TypeVar("t0".to_string())),
                    int.clone(),
                ]))),
                upper: Some(Box::new(typed_ir::Type::Any)),
            })],
        };

        let projected = project_runtime_type(&raw);

        assert_eq!(
            projected,
            typed_ir::Type::Named {
                path: typed_ir::Path::from_name(typed_ir::Name("list".to_string())),
                args: vec![typed_ir::TypeArg::Type(int)],
            }
        );
    }

    #[test]
    fn project_runtime_type_preserves_effect_row_type_arg() {
        let state = named("&state");
        let int = named("int");
        let effect = typed_ir::Type::Row {
            items: vec![state.clone()],
            tail: Box::new(typed_ir::Type::Never),
        };
        let raw = typed_ir::Type::Named {
            path: typed_ir::Path::new(vec![
                typed_ir::Name("std".to_string()),
                typed_ir::Name("control".to_string()),
                typed_ir::Name("var".to_string()),
                typed_ir::Name("ref".to_string()),
            ]),
            args: vec![
                typed_ir::TypeArg::Type(effect.clone()),
                typed_ir::TypeArg::Type(int.clone()),
            ],
        };

        let projected = project_runtime_type(&raw);

        assert_eq!(
            projected,
            typed_ir::Type::Named {
                path: typed_ir::Path::new(vec![
                    typed_ir::Name("std".to_string()),
                    typed_ir::Name("control".to_string()),
                    typed_ir::Name("var".to_string()),
                    typed_ir::Name("ref".to_string()),
                ]),
                args: vec![
                    typed_ir::TypeArg::Type(effect),
                    typed_ir::TypeArg::Type(int)
                ],
            }
        );
        assert!(!contains_non_runtime_type(&projected), "{projected:?}");
    }

    #[test]
    fn never_is_compatible_with_value_expected_type() {
        assert!(type_compatible(&named("unit"), &typed_ir::Type::Never));
        assert!(!type_compatible(&typed_ir::Type::Never, &named("unit")));
    }

    #[test]
    fn project_runtime_effect_merges_rows_and_erases_holes() {
        let io = named("io");
        let yield_effect = named("yield");
        let raw = typed_ir::Type::Union(vec![
            typed_ir::Type::Row {
                items: vec![io.clone()],
                tail: Box::new(typed_ir::Type::Any),
            },
            typed_ir::Type::Union(vec![
                typed_ir::Type::Var(typed_ir::TypeVar("t0".to_string())),
                typed_ir::Type::Row {
                    items: vec![yield_effect.clone(), io.clone()],
                    tail: Box::new(typed_ir::Type::Never),
                },
            ]),
        ]);

        let projected = project_runtime_effect(&raw);

        assert_eq!(
            projected,
            typed_ir::Type::Row {
                items: vec![io, yield_effect],
                tail: Box::new(typed_ir::Type::Never),
            }
        );
    }

    #[test]
    fn project_runtime_effect_erases_open_effect_atom_args() {
        let raw = typed_ir::Type::Row {
            items: vec![
                named("std::flow::sub"),
                effect_with_type_arg("std::flow::sub", typed_ir::Type::Unknown),
            ],
            tail: Box::new(typed_ir::Type::Never),
        };

        let projected = project_runtime_effect(&raw);

        assert_eq!(
            projected,
            typed_ir::Type::Row {
                items: vec![named("std::flow::sub")],
                tail: Box::new(typed_ir::Type::Never),
            }
        );
    }

    #[test]
    fn project_runtime_effect_keeps_closed_effect_atom_args() {
        let sub_int = effect_with_type_arg("std::flow::sub", named("int"));

        let projected = project_runtime_effect(&sub_int);

        assert_eq!(projected, sub_int);
    }

    #[test]
    fn closed_projection_erases_synthetic_ref_effect_args_in_rows() {
        let loop_effect = named("std::flow::loop");
        let ref_effect = effect_with_type_arg("&count#1", typed_ir::Type::Unknown);
        let expected_ref_effect = named("&count#1");
        let tail = typed_ir::TypeVar("tail".to_string());
        let template = typed_ir::Type::Row {
            items: vec![loop_effect.clone()],
            tail: Box::new(typed_ir::Type::Var(tail.clone())),
        };
        let actual = typed_ir::Type::Row {
            items: vec![loop_effect, ref_effect],
            tail: Box::new(typed_ir::Type::Never),
        };
        let mut params = BTreeSet::new();
        params.insert(tail.clone());
        let mut substitutions = BTreeMap::new();
        let mut conflicts = BTreeSet::new();

        project_closed_substitutions_from_type(
            &template,
            &actual,
            &params,
            &mut substitutions,
            &mut conflicts,
            true,
            64,
        );

        assert!(conflicts.is_empty(), "{conflicts:?}");
        assert_eq!(substitutions.get(&tail), Some(&expected_ref_effect));
    }

    #[test]
    fn int_is_compatible_with_float_by_runtime_widening() {
        assert!(type_compatible(&named("float"), &named("int")));
        assert!(needs_runtime_coercion(&named("float"), &named("int")));
        assert!(!needs_runtime_coercion(&named("int"), &named("float")));
    }

    #[test]
    fn str_is_compatible_with_path_by_runtime_widening() {
        assert!(type_compatible(
            &named("std::path::path"),
            &named("std::str::str"),
        ));
        assert!(needs_runtime_coercion(
            &named("std::path::path"),
            &named("std::str::str"),
        ));
        assert!(!needs_runtime_coercion(
            &named("std::str::str"),
            &named("std::path::path"),
        ));
    }

    #[test]
    fn full_path_numeric_widening_requires_registered_primitive_order() {
        let order = typed_ir::PrimitiveTypeOrder::from_primitive_types(&[
            primitive_type_node(typed_ir::PrimitiveTypeFamily::Int, "std::int::int"),
            primitive_type_node(typed_ir::PrimitiveTypeFamily::Frac, "std::frac::frac"),
            primitive_type_node(typed_ir::PrimitiveTypeFamily::Float, "std::float::float"),
        ]);

        assert!(!needs_runtime_coercion(
            &named("std::float::float"),
            &named("std::int::int")
        ));
        assert!(needs_runtime_coercion_with_order(
            &order,
            &named("std::float::float"),
            &named("std::int::int")
        ));
        assert!(!needs_runtime_coercion_with_order(
            &order,
            &named("std::float::float"),
            &named("int")
        ));
    }

    #[test]
    fn type_compatibility_depth_exhaustion_is_not_success() {
        assert!(type_compatible_inner(&named("int"), &named("int"), 0));
        assert!(!type_compatible_inner(&named("int"), &named("bool"), 0));
    }

    #[test]
    fn function_type_compatibility_checks_effect_slots() {
        let with_ret_effect = |effect| typed_ir::Type::Fun {
            param: Box::new(named("unit")),
            param_effect: Box::new(typed_ir::Type::Never),
            ret_effect: Box::new(effect),
            ret: Box::new(named("int")),
        };

        assert!(!type_compatible(
            &with_ret_effect(named("io")),
            &with_ret_effect(named("state")),
        ));
        assert!(type_compatible(
            &with_ret_effect(typed_ir::Type::Row {
                items: vec![named("io"), named("state")],
                tail: Box::new(typed_ir::Type::Never),
            }),
            &with_ret_effect(named("io")),
        ));
    }

    #[test]
    fn row_type_compatibility_does_not_depend_on_effect_order() {
        let left = typed_ir::Type::Row {
            items: vec![named("io"), named("state")],
            tail: Box::new(typed_ir::Type::Never),
        };
        let right = typed_ir::Type::Row {
            items: vec![named("state"), named("io")],
            tail: Box::new(typed_ir::Type::Never),
        };

        assert!(type_compatible(&left, &right));
        assert!(type_compatible(&right, &left));
    }

    #[test]
    fn row_type_compatibility_uses_effect_path_matching_for_items() {
        let parent = typed_ir::Type::Row {
            items: vec![named("std::flow::loop")],
            tail: Box::new(typed_ir::Type::Never),
        };
        let child = typed_ir::Type::Row {
            items: vec![named("std::flow::loop::last")],
            tail: Box::new(typed_ir::Type::Never),
        };

        assert!(type_compatible(&parent, &child));
        assert!(type_compatible(&child, &parent));
    }

    #[test]
    fn collect_type_vars_ignores_recursive_binder() {
        let var = typed_ir::TypeVar("a".to_string());
        let ty = typed_ir::Type::Recursive {
            var: var.clone(),
            body: Box::new(typed_ir::Type::Var(var)),
        };
        let mut vars = BTreeSet::new();

        collect_type_vars(&ty, &mut vars);

        assert!(vars.is_empty());
    }

    #[test]
    fn collect_type_vars_preserves_same_named_free_var_outside_recursive_scope() {
        let var = typed_ir::TypeVar("a".to_string());
        let ty = typed_ir::Type::Tuple(vec![
            typed_ir::Type::Var(var.clone()),
            typed_ir::Type::Recursive {
                var: var.clone(),
                body: Box::new(typed_ir::Type::Var(var.clone())),
            },
        ]);
        let mut vars = BTreeSet::new();

        collect_type_vars(&ty, &mut vars);

        assert_eq!(vars, BTreeSet::from([var]));
    }

    fn named(path: &str) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: typed_ir::Path::new(
                path.split("::")
                    .map(|segment| typed_ir::Name(segment.to_string()))
                    .collect(),
            ),
            args: Vec::new(),
        }
    }

    fn primitive_type_node(
        family: typed_ir::PrimitiveTypeFamily,
        path: &str,
    ) -> typed_ir::PrimitiveTypeGraphNode {
        typed_ir::PrimitiveTypeGraphNode {
            family,
            path: typed_ir::Path::new(
                path.split("::")
                    .map(|segment| typed_ir::Name(segment.to_string()))
                    .collect(),
            ),
        }
    }

    fn effect_with_type_arg(path: &str, arg: typed_ir::Type) -> typed_ir::Type {
        typed_ir::Type::Named {
            path: typed_ir::Path::new(
                path.split("::")
                    .map(|segment| typed_ir::Name(segment.to_string()))
                    .collect(),
            ),
            args: vec![typed_ir::TypeArg::Type(arg)],
        }
    }
}
