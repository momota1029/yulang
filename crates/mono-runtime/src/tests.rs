use mono::{
    Block, CatchArm, Expr, ExprKind, FunctionAdapterHygiene, GuardMarker, Instance, InstanceId,
    InstanceSource, Lit, Pat, Program, Root, SelectResolution, Signature, Stmt, Type, Vis,
};

use super::{Value, run_program};

#[test]
fn runs_literal_root() {
    let program = Program {
        roots: vec![Root::Expr(Expr::new(ExprKind::Lit(Lit::Int(1))))],
        instances: Vec::new(),
    };

    assert_eq!(run_program(&program), Ok(vec![Value::Int(1)]));
}

#[test]
fn stores_root_instance_for_later_instance_ref() {
    let program = Program {
        roots: vec![
            Root::Instance(InstanceId(0)),
            Root::Expr(Expr::new(ExprKind::InstanceRef(InstanceId(0)))),
        ],
        instances: vec![Instance {
            id: InstanceId(0),
            source: InstanceSource::Def(mono::DefId(0)),
            signature: Signature { ty: int_type() },
            body: Expr::new(ExprKind::Lit(Lit::Int(1))),
        }],
    };

    assert_eq!(
        run_program(&program),
        Ok(vec![Value::Int(1), Value::Int(1)])
    );
}

#[test]
fn runs_lambda_application() {
    let param = mono::DefId(10);
    let program = Program {
        roots: vec![Root::Expr(Expr::new(ExprKind::Apply(
            Box::new(Expr::new(ExprKind::Lambda(
                Pat::Var(param),
                Box::new(Expr::new(ExprKind::Local(param))),
            ))),
            Box::new(Expr::new(ExprKind::Lit(Lit::Int(7)))),
        )))],
        instances: Vec::new(),
    };

    assert_eq!(run_program(&program), Ok(vec![Value::Int(7)]));
}

#[test]
fn runs_block_let_and_tail() {
    let local = mono::DefId(2);
    let program = Program {
        roots: vec![Root::Expr(Expr::new(ExprKind::Block(Block {
            stmts: vec![Stmt::Let(
                Vis::My,
                Pat::Var(local),
                Expr::new(ExprKind::Lit(Lit::Int(3))),
            )],
            tail: Some(Box::new(Expr::new(ExprKind::Local(local)))),
        })))],
        instances: Vec::new(),
    };

    assert_eq!(run_program(&program), Ok(vec![Value::Int(3)]));
}

#[test]
fn forces_thunk_only_at_force_node() {
    let program = Program {
        roots: vec![Root::Expr(Expr::new(ExprKind::ForceThunk {
            source: mono::EffectiveThunkType {
                effect: Type::pure_effect(),
                value: int_type(),
            },
            target: mono::ComputationType {
                effect: Type::pure_effect(),
                value: int_type(),
            },
            thunk: Box::new(Expr::new(ExprKind::MakeThunk {
                source: mono::ComputationType {
                    effect: Type::pure_effect(),
                    value: int_type(),
                },
                target: mono::EffectiveThunkType {
                    effect: Type::pure_effect(),
                    value: int_type(),
                },
                body: Box::new(Expr::new(ExprKind::Lit(Lit::Int(9)))),
            })),
        }))],
        instances: Vec::new(),
    };

    assert_eq!(run_program(&program), Ok(vec![Value::Int(9)]));
}

#[test]
fn force_thunk_reaches_nested_computation_when_target_value_is_plain() {
    let inner = make_thunk_expr(
        Type::pure_effect(),
        unit_type(),
        Expr::new(ExprKind::Lit(Lit::Unit)),
    );
    let outer_value = thunk_type(Type::pure_effect(), unit_type());
    let outer = make_thunk_expr(Type::pure_effect(), outer_value, inner);

    let program = Program {
        roots: vec![Root::Expr(force_thunk_expr(
            outer,
            Type::pure_effect(),
            unit_type(),
        ))],
        instances: Vec::new(),
    };

    assert_eq!(run_program(&program), Ok(vec![Value::Unit]));
}

#[test]
fn catches_matching_effect_request() {
    let payload = mono::DefId(1);
    let program = Program {
        roots: vec![Root::Expr(Expr::new(ExprKind::Catch {
            body: Box::new(effect_call(
                path(&["out", "say"]),
                ExprKind::Lit(Lit::Int(1)),
            )),
            arms: vec![CatchArm {
                operation_path: Some(path(&["out", "say"])),
                pat: Pat::Var(payload),
                continuation: Some(Pat::Wild),
                guard: None,
                body: Expr::new(ExprKind::Local(payload)),
            }],
        }))],
        instances: Vec::new(),
    };

    assert_eq!(run_program(&program), Ok(vec![Value::Int(1)]));
}

#[test]
fn handler_continuation_resumes_block_after_request() {
    let payload = mono::DefId(1);
    let continuation = mono::DefId(2);
    let local = mono::DefId(3);
    let program = Program {
        roots: vec![Root::Expr(Expr::new(ExprKind::Catch {
            body: Box::new(Expr::new(ExprKind::Block(Block {
                stmts: vec![Stmt::Let(
                    Vis::My,
                    Pat::Var(local),
                    effect_call(path(&["ask", "value"]), ExprKind::Lit(Lit::Unit)),
                )],
                tail: Some(Box::new(Expr::new(ExprKind::Local(local)))),
            }))),
            arms: vec![CatchArm {
                operation_path: Some(path(&["ask", "value"])),
                pat: Pat::Var(payload),
                continuation: Some(Pat::Var(continuation)),
                guard: None,
                body: continuation_call(continuation, ExprKind::Lit(Lit::Int(7))),
            }],
        }))],
        instances: Vec::new(),
    };

    assert_eq!(run_program(&program), Ok(vec![Value::Int(7)]));
}

#[test]
fn shallow_handler_searches_past_unhandled_request_until_matching_one() {
    let skip_continuation = mono::DefId(1);
    let target_payload = mono::DefId(2);
    let program = Program {
        roots: vec![Root::Expr(Expr::new(ExprKind::Catch {
            body: Box::new(Expr::new(ExprKind::Catch {
                body: Box::new(Expr::new(ExprKind::Block(Block {
                    stmts: vec![Stmt::Expr(effect_call(
                        path(&["skip", "go"]),
                        ExprKind::Lit(Lit::Unit),
                    ))],
                    tail: Some(Box::new(effect_call(
                        path(&["target", "hit"]),
                        ExprKind::Lit(Lit::Int(1)),
                    ))),
                }))),
                arms: vec![CatchArm {
                    operation_path: Some(path(&["target", "hit"])),
                    pat: Pat::Var(target_payload),
                    continuation: Some(Pat::Wild),
                    guard: None,
                    body: Expr::new(ExprKind::Local(target_payload)),
                }],
            })),
            arms: vec![CatchArm {
                operation_path: Some(path(&["skip", "go"])),
                pat: Pat::Wild,
                continuation: Some(Pat::Var(skip_continuation)),
                guard: None,
                body: continuation_call(skip_continuation, ExprKind::Lit(Lit::Unit)),
            }],
        }))],
        instances: Vec::new(),
    };

    assert_eq!(run_program(&program), Ok(vec![Value::Int(1)]));
}

#[test]
fn resumes_tuple_construction_after_effect_request() {
    let payload = mono::DefId(1);
    let continuation = mono::DefId(2);
    let program = Program {
        roots: vec![Root::Expr(Expr::new(ExprKind::Catch {
            body: Box::new(Expr::new(ExprKind::Tuple(vec![
                Expr::new(ExprKind::Lit(Lit::Int(1))),
                effect_call(path(&["ask", "tuple"]), ExprKind::Lit(Lit::Unit)),
                Expr::new(ExprKind::Lit(Lit::Int(3))),
            ]))),
            arms: vec![CatchArm {
                operation_path: Some(path(&["ask", "tuple"])),
                pat: Pat::Var(payload),
                continuation: Some(Pat::Var(continuation)),
                guard: None,
                body: continuation_call(continuation, ExprKind::Lit(Lit::Int(2))),
            }],
        }))],
        instances: Vec::new(),
    };

    assert_eq!(
        run_program(&program),
        Ok(vec![Value::Tuple(vec![
            Value::Int(1),
            Value::Int(2),
            Value::Int(3)
        ])])
    );
}

#[test]
fn resumes_record_construction_after_effect_request() {
    let continuation = mono::DefId(2);
    let program = Program {
        roots: vec![Root::Expr(Expr::new(ExprKind::Catch {
            body: Box::new(Expr::new(ExprKind::Record {
                fields: vec![
                    mono::RecordField {
                        name: "a".to_string(),
                        value: Expr::new(ExprKind::Lit(Lit::Int(1))),
                    },
                    mono::RecordField {
                        name: "b".to_string(),
                        value: effect_call(path(&["ask", "record"]), ExprKind::Lit(Lit::Unit)),
                    },
                ],
                spread: mono::RecordSpread::None,
            })),
            arms: vec![CatchArm {
                operation_path: Some(path(&["ask", "record"])),
                pat: Pat::Wild,
                continuation: Some(Pat::Var(continuation)),
                guard: None,
                body: continuation_call(continuation, ExprKind::Lit(Lit::Int(2))),
            }],
        }))],
        instances: Vec::new(),
    };

    assert_eq!(
        run_program(&program),
        Ok(vec![Value::Record(vec![
            super::ValueField {
                name: "a".to_string(),
                value: Value::Int(1),
            },
            super::ValueField {
                name: "b".to_string(),
                value: Value::Int(2),
            },
        ])])
    );
}

#[test]
fn resumes_poly_variant_construction_after_effect_request() {
    let continuation = mono::DefId(2);
    let program = Program {
        roots: vec![Root::Expr(Expr::new(ExprKind::Catch {
            body: Box::new(Expr::new(ExprKind::PolyVariant {
                tag: "some".to_string(),
                payloads: vec![effect_call(
                    path(&["ask", "variant"]),
                    ExprKind::Lit(Lit::Unit),
                )],
            })),
            arms: vec![CatchArm {
                operation_path: Some(path(&["ask", "variant"])),
                pat: Pat::Wild,
                continuation: Some(Pat::Var(continuation)),
                guard: None,
                body: continuation_call(continuation, ExprKind::Lit(Lit::Int(4))),
            }],
        }))],
        instances: Vec::new(),
    };

    assert_eq!(
        run_program(&program),
        Ok(vec![Value::PolyVariant {
            tag: "some".to_string(),
            payloads: vec![Value::Int(4)],
        }])
    );
}

#[test]
fn resumes_case_guard_after_effect_request() {
    let continuation = mono::DefId(1);
    let program = Program {
        roots: vec![Root::Expr(Expr::new(ExprKind::Catch {
            body: Box::new(Expr::new(ExprKind::Case {
                scrutinee: Box::new(Expr::new(ExprKind::Lit(Lit::Unit))),
                arms: vec![
                    mono::CaseArm {
                        pat: Pat::Wild,
                        guard: Some(effect_call(
                            path(&["ask", "guard"]),
                            ExprKind::Lit(Lit::Unit),
                        )),
                        body: Expr::new(ExprKind::Lit(Lit::Int(1))),
                    },
                    mono::CaseArm {
                        pat: Pat::Wild,
                        guard: None,
                        body: Expr::new(ExprKind::Lit(Lit::Int(2))),
                    },
                ],
            })),
            arms: vec![CatchArm {
                operation_path: Some(path(&["ask", "guard"])),
                pat: Pat::Wild,
                continuation: Some(Pat::Var(continuation)),
                guard: None,
                body: continuation_call(continuation, ExprKind::Lit(Lit::Bool(true))),
            }],
        }))],
        instances: Vec::new(),
    };

    assert_eq!(run_program(&program), Ok(vec![Value::Int(1)]));
}

#[test]
fn resumes_catch_request_guard_after_effect_request() {
    let guard_continuation = mono::DefId(1);
    let target_payload = mono::DefId(2);
    let program = Program {
        roots: vec![Root::Expr(Expr::new(ExprKind::Catch {
            body: Box::new(Expr::new(ExprKind::Catch {
                body: Box::new(effect_call(
                    path(&["target", "hit"]),
                    ExprKind::Lit(Lit::Int(1)),
                )),
                arms: vec![CatchArm {
                    operation_path: Some(path(&["target", "hit"])),
                    pat: Pat::Var(target_payload),
                    continuation: Some(Pat::Wild),
                    guard: Some(effect_call(
                        path(&["ask", "guard"]),
                        ExprKind::Lit(Lit::Unit),
                    )),
                    body: Expr::new(ExprKind::Local(target_payload)),
                }],
            })),
            arms: vec![CatchArm {
                operation_path: Some(path(&["ask", "guard"])),
                pat: Pat::Wild,
                continuation: Some(Pat::Var(guard_continuation)),
                guard: None,
                body: continuation_call(guard_continuation, ExprKind::Lit(Lit::Bool(true))),
            }],
        }))],
        instances: Vec::new(),
    };

    assert_eq!(run_program(&program), Ok(vec![Value::Int(1)]));
}

#[test]
fn hygiene_blocks_inner_handler_for_foreign_thunk_argument() {
    let thunk_arg = mono::DefId(10);
    let outer_payload = mono::DefId(11);
    let blocked = path(&["blocked", "fire"]);
    let allowed = path(&["allowed", "run"]);
    let thunk_effect = effect_row(&["blocked", "fire"]);
    let thunk_arg_type = thunk_type(thunk_effect.clone(), int_type());
    let source = pure_function_type(thunk_arg_type.clone(), int_type());
    let target = pure_function_type(thunk_arg_type.clone(), int_type());
    let function = Expr::new(ExprKind::Lambda(
        Pat::Var(thunk_arg),
        Box::new(Expr::new(ExprKind::Catch {
            body: Box::new(force_thunk_expr(
                Expr::new(ExprKind::Local(thunk_arg)),
                thunk_effect.clone(),
                int_type(),
            )),
            arms: vec![CatchArm {
                operation_path: Some(blocked.clone()),
                pat: Pat::Wild,
                continuation: Some(Pat::Wild),
                guard: None,
                body: Expr::new(ExprKind::Lit(Lit::Int(99))),
            }],
        })),
    ));
    let adapter = function_adapter(function, source, target, allowed, 0);
    let arg = make_thunk_expr(
        thunk_effect,
        int_type(),
        effect_call(blocked.clone(), ExprKind::Lit(Lit::Int(7))),
    );
    let program = Program {
        roots: vec![Root::Expr(Expr::new(ExprKind::Catch {
            body: Box::new(Expr::new(ExprKind::Apply(Box::new(adapter), Box::new(arg)))),
            arms: vec![CatchArm {
                operation_path: Some(blocked),
                pat: Pat::Var(outer_payload),
                continuation: Some(Pat::Wild),
                guard: None,
                body: Expr::new(ExprKind::Local(outer_payload)),
            }],
        }))],
        instances: Vec::new(),
    };

    assert_eq!(run_program(&program), Ok(vec![Value::Int(7)]));
}

#[test]
fn hygiene_keeps_allowed_path_readable_inside_marker_frame() {
    let thunk_arg = mono::DefId(20);
    let allowed = path(&["allowed", "run"]);
    let thunk_effect = effect_row(&["allowed", "run"]);
    let thunk_arg_type = thunk_type(thunk_effect.clone(), int_type());
    let source = pure_function_type(thunk_arg_type.clone(), int_type());
    let target = pure_function_type(thunk_arg_type.clone(), int_type());
    let function = Expr::new(ExprKind::Lambda(
        Pat::Var(thunk_arg),
        Box::new(Expr::new(ExprKind::Catch {
            body: Box::new(force_thunk_expr(
                Expr::new(ExprKind::Local(thunk_arg)),
                thunk_effect.clone(),
                int_type(),
            )),
            arms: vec![CatchArm {
                operation_path: Some(allowed.clone()),
                pat: Pat::Wild,
                continuation: Some(Pat::Wild),
                guard: None,
                body: Expr::new(ExprKind::Lit(Lit::Int(99))),
            }],
        })),
    ));
    let adapter = function_adapter(function, source, target, allowed.clone(), 0);
    let arg = make_thunk_expr(
        thunk_effect,
        int_type(),
        effect_call(allowed, ExprKind::Lit(Lit::Int(7))),
    );
    let program = Program {
        roots: vec![Root::Expr(Expr::new(ExprKind::Apply(
            Box::new(adapter),
            Box::new(arg),
        )))],
        instances: Vec::new(),
    };

    assert_eq!(run_program(&program), Ok(vec![Value::Int(99)]));
}

#[test]
fn hygiene_depth_one_blocks_inner_handler_when_marked_function_runs() {
    let callback = mono::DefId(30);
    let outer_payload = mono::DefId(31);
    let blocked = path(&["blocked", "fire"]);
    let allowed = path(&["allowed", "run"]);
    let callback_type = pure_function_type(unit_type(), int_type());
    let source = pure_function_type(callback_type.clone(), int_type());
    let target = pure_function_type(callback_type.clone(), int_type());
    let function = Expr::new(ExprKind::Lambda(
        Pat::Var(callback),
        Box::new(Expr::new(ExprKind::Catch {
            body: Box::new(Expr::new(ExprKind::Apply(
                Box::new(Expr::new(ExprKind::Local(callback))),
                Box::new(Expr::new(ExprKind::Lit(Lit::Unit))),
            ))),
            arms: vec![CatchArm {
                operation_path: Some(blocked.clone()),
                pat: Pat::Wild,
                continuation: Some(Pat::Wild),
                guard: None,
                body: Expr::new(ExprKind::Lit(Lit::Int(99))),
            }],
        })),
    ));
    let callback_arg = Expr::new(ExprKind::Lambda(
        Pat::Wild,
        Box::new(effect_call(blocked.clone(), ExprKind::Lit(Lit::Int(7)))),
    ));
    let adapter = function_adapter(function, source, target, allowed, 1);
    let program = Program {
        roots: vec![Root::Expr(Expr::new(ExprKind::Catch {
            body: Box::new(Expr::new(ExprKind::Apply(
                Box::new(adapter),
                Box::new(callback_arg),
            ))),
            arms: vec![CatchArm {
                operation_path: Some(blocked),
                pat: Pat::Var(outer_payload),
                continuation: Some(Pat::Wild),
                guard: None,
                body: Expr::new(ExprKind::Local(outer_payload)),
            }],
        }))],
        instances: Vec::new(),
    };

    assert_eq!(run_program(&program), Ok(vec![Value::Int(7)]));
}

#[test]
fn hygiene_allows_distinct_handler_created_inside_marked_function() {
    let outer = path(&["outer", "return"]);
    let inner = path(&["inner", "return"]);
    let source = pure_function_type(unit_type(), int_type());
    let target = pure_function_type(unit_type(), int_type());
    let function = Expr::new(ExprKind::Lambda(
        Pat::Wild,
        Box::new(Expr::new(ExprKind::MarkerFrame {
            path: path(&["inner"]),
            body: Box::new(Expr::new(ExprKind::Catch {
                body: Box::new(effect_call(inner.clone(), ExprKind::Lit(Lit::Int(7)))),
                arms: vec![CatchArm {
                    operation_path: Some(inner),
                    pat: Pat::Wild,
                    continuation: Some(Pat::Wild),
                    guard: None,
                    body: Expr::new(ExprKind::Lit(Lit::Int(99))),
                }],
            })),
        })),
    ));
    let adapter = function_adapter(function, source, target, outer, 0);
    let program = Program {
        roots: vec![Root::Expr(Expr::new(ExprKind::Apply(
            Box::new(adapter),
            Box::new(Expr::new(ExprKind::Lit(Lit::Unit))),
        )))],
        instances: Vec::new(),
    };

    assert_eq!(run_program(&program), Ok(vec![Value::Int(99)]));
}

#[test]
fn hygiene_marker_propagates_through_record_projection_to_returned_thunk() {
    let outer_payload = mono::DefId(41);
    let blocked = path(&["blocked", "fire"]);
    let allowed = path(&["allowed", "run"]);
    let thunk_effect = effect_row(&["blocked", "fire"]);
    let thunk_value = int_type();
    let thunk = thunk_type(thunk_effect.clone(), thunk_value.clone());
    let record = Type::Record(vec![mono::TypeField {
        name: "run".to_string(),
        value: thunk.clone(),
        optional: false,
    }]);
    let source = pure_function_type(unit_type(), record.clone());
    let target = pure_function_type(unit_type(), record);
    let function = Expr::new(ExprKind::Lambda(
        Pat::Wild,
        Box::new(Expr::new(ExprKind::Record {
            fields: vec![mono::RecordField {
                name: "run".to_string(),
                value: make_thunk_expr(
                    thunk_effect.clone(),
                    thunk_value.clone(),
                    Expr::new(ExprKind::Catch {
                        body: Box::new(effect_call(blocked.clone(), ExprKind::Lit(Lit::Int(7)))),
                        arms: vec![CatchArm {
                            operation_path: Some(blocked.clone()),
                            pat: Pat::Wild,
                            continuation: Some(Pat::Wild),
                            guard: None,
                            body: Expr::new(ExprKind::Lit(Lit::Int(99))),
                        }],
                    }),
                ),
            }],
            spread: mono::RecordSpread::None,
        })),
    ));
    let adapter = function_adapter(function, source, target, allowed, 0);
    let selected = Expr::new(ExprKind::Select {
        base: Box::new(Expr::new(ExprKind::Apply(
            Box::new(adapter),
            Box::new(Expr::new(ExprKind::Lit(Lit::Unit))),
        ))),
        name: "run".to_string(),
        resolution: Some(SelectResolution::RecordField),
    });
    let program = Program {
        roots: vec![Root::Expr(Expr::new(ExprKind::Catch {
            body: Box::new(force_thunk_expr(selected, thunk_effect, thunk_value)),
            arms: vec![CatchArm {
                operation_path: Some(blocked),
                pat: Pat::Var(outer_payload),
                continuation: Some(Pat::Wild),
                guard: None,
                body: Expr::new(ExprKind::Local(outer_payload)),
            }],
        }))],
        instances: Vec::new(),
    };

    assert_eq!(run_program(&program), Ok(vec![Value::Int(7)]));
}

#[test]
fn value_boundary_supports_record_field_functions_that_differ_only_by_effect_shape() {
    let source = record_with_update_effect(effect_row(&["source", "effect"]));
    let target = record_with_update_effect(effect_row(&["target", "effect"]));

    assert!(super::value_boundary_supported(&source, &target));
    assert!(super::value_boundary_supported(&target, &source));
}

#[test]
fn hygiene_marker_frame_is_restored_when_outer_handler_resumes() {
    let resume_continuation = mono::DefId(50);
    let second_payload = mono::DefId(51);
    let first = path(&["blocked", "first"]);
    let second = path(&["blocked", "second"]);
    let allowed = path(&["allowed", "run"]);
    let source = pure_function_type(unit_type(), int_type());
    let target = pure_function_type(unit_type(), int_type());
    let function = Expr::new(ExprKind::Lambda(
        Pat::Wild,
        Box::new(Expr::new(ExprKind::Block(Block {
            stmts: vec![Stmt::Expr(effect_call(
                first.clone(),
                ExprKind::Lit(Lit::Unit),
            ))],
            tail: Some(Box::new(Expr::new(ExprKind::Catch {
                body: Box::new(effect_call(second.clone(), ExprKind::Lit(Lit::Int(2)))),
                arms: vec![CatchArm {
                    operation_path: Some(second.clone()),
                    pat: Pat::Wild,
                    continuation: Some(Pat::Wild),
                    guard: None,
                    body: Expr::new(ExprKind::Lit(Lit::Int(99))),
                }],
            }))),
        }))),
    ));
    let adapter = function_adapter(function, source, target, allowed, 0);
    let program = Program {
        roots: vec![Root::Expr(Expr::new(ExprKind::Catch {
            body: Box::new(Expr::new(ExprKind::Catch {
                body: Box::new(Expr::new(ExprKind::Apply(
                    Box::new(adapter),
                    Box::new(Expr::new(ExprKind::Lit(Lit::Unit))),
                ))),
                arms: vec![CatchArm {
                    operation_path: Some(first),
                    pat: Pat::Wild,
                    continuation: Some(Pat::Var(resume_continuation)),
                    guard: None,
                    body: continuation_call(resume_continuation, ExprKind::Lit(Lit::Unit)),
                }],
            })),
            arms: vec![CatchArm {
                operation_path: Some(second),
                pat: Pat::Var(second_payload),
                continuation: Some(Pat::Wild),
                guard: None,
                body: Expr::new(ExprKind::Local(second_payload)),
            }],
        }))],
        instances: Vec::new(),
    };

    assert_eq!(run_program(&program), Ok(vec![Value::Int(2)]));
}

#[test]
fn runs_specialized_string_input_generic_call() {
    let lowering = lower_source("my id x = x\nid(1)\n");
    let program = specialize::specialize(&lowering.session.poly)
        .expect("source should specialize to mono program");

    assert_eq!(run_program(&program), Ok(vec![Value::Int(1)]));
}

fn lower_source(source: &str) -> infer::lowering::BodyLowering {
    let files = sources::load(vec![sources::SourceFile {
        module_path: sources::Path::default(),
        source: source.to_string(),
    }]);
    let output = infer::dump::dump_loaded_files(&files).expect("source should lower");
    assert!(
        output.lowering.errors.is_empty(),
        "body lowering errors: {:?}",
        output.lowering.errors
    );
    output.lowering
}

fn int_type() -> Type {
    Type::Con {
        path: vec!["int".to_string()],
        args: Vec::new(),
    }
}

fn unit_type() -> Type {
    Type::unit()
}

fn effect_row(parts: &[&str]) -> Type {
    Type::EffectRow(vec![effect_type(parts)])
}

fn effect_type(parts: &[&str]) -> Type {
    Type::Con {
        path: path(parts),
        args: Vec::new(),
    }
}

fn thunk_type(effect: Type, value: Type) -> Type {
    Type::Thunk {
        effect: Box::new(effect),
        value: Box::new(value),
    }
}

fn record_with_update_effect(effect: Type) -> Type {
    Type::Record(vec![mono::TypeField {
        name: "update_effect".to_string(),
        value: pure_function_type(unit_type(), thunk_type(effect, unit_type())),
        optional: false,
    }])
}

fn pure_function_type(arg: Type, ret: Type) -> Type {
    Type::Fun {
        arg: Box::new(arg),
        arg_effect: Box::new(Type::pure_effect()),
        ret_effect: Box::new(Type::pure_effect()),
        ret: Box::new(ret),
    }
}

fn function_adapter(
    function: Expr,
    source: Type,
    target: Type,
    path: Vec<String>,
    depth: u32,
) -> Expr {
    Expr::new(ExprKind::FunctionAdapter {
        source,
        target,
        function: Box::new(function),
        hygiene: FunctionAdapterHygiene {
            markers: vec![GuardMarker {
                path,
                depth,
                guard_own_path: false,
                guard_foreign_path: true,
                preserve_own_on_resume: false,
            }],
            arg_markers: Vec::new(),
            ret_markers: Vec::new(),
        },
    })
}

fn make_thunk_expr(effect: Type, value: Type, body: Expr) -> Expr {
    Expr::new(ExprKind::MakeThunk {
        source: mono::ComputationType {
            effect: effect.clone(),
            value: value.clone(),
        },
        target: mono::EffectiveThunkType { effect, value },
        body: Box::new(body),
    })
}

fn force_thunk_expr(thunk: Expr, effect: Type, value: Type) -> Expr {
    Expr::new(ExprKind::ForceThunk {
        source: mono::EffectiveThunkType {
            effect: effect.clone(),
            value: value.clone(),
        },
        target: mono::ComputationType { effect, value },
        thunk: Box::new(thunk),
    })
}

fn path(parts: &[&str]) -> Vec<String> {
    parts.iter().map(|part| part.to_string()).collect()
}

fn effect_call(path: Vec<String>, payload: ExprKind) -> Expr {
    let effect = Type::EffectRow(vec![Type::Con {
        path: path.clone(),
        args: Vec::new(),
    }]);
    force_thunk_expr(
        Expr::new(ExprKind::Apply(
            Box::new(Expr::new(ExprKind::EffectOp { def: None, path })),
            Box::new(Expr::new(payload)),
        )),
        effect,
        Type::Any,
    )
}

fn continuation_call(continuation: mono::DefId, arg: ExprKind) -> Expr {
    force_thunk_expr(
        Expr::new(ExprKind::Apply(
            Box::new(Expr::new(ExprKind::Local(continuation))),
            Box::new(Expr::new(arg)),
        )),
        Type::Any,
        Type::Any,
    )
}
