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

pub(crate) use choice::*;
pub(crate) use compat::*;
pub(crate) use core_view::*;
pub(crate) use effect::*;
pub(crate) use meaning::*;
pub(crate) use project::*;
pub(crate) use runtime::*;
pub(crate) use shape::*;
pub(crate) use substitution::*;

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
        assert_eq!(*ret, RuntimeType::core(typed_ir::Type::Var(value.clone())));
        assert_eq!(
            *param,
            RuntimeType::thunk(
                typed_ir::Type::Var(effect),
                RuntimeType::core(typed_ir::Type::Var(value))
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
