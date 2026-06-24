//! Function adapter に載せる runtime guard marker plan を作る。
//!
//! `specialize` は runtime lower が call spine から hygiene を推測しなくてよいように、
//! 関数値が producer-consumer 境界を越えた時点で必要な marker を mono IR に残す。

use mono::{FunctionAdapterHygiene, GuardMarker, Type};
use poly::expr as poly_expr;

use crate::equivalent_boundary_types;

pub(crate) fn function_adapter_hygiene(source: &Type, target: &Type) -> FunctionAdapterHygiene {
    function_adapter_hygiene_with_argument_contract(source, target, None)
}

pub(crate) fn function_adapter_hygiene_with_argument_contract(
    source: &Type,
    target: &Type,
    argument_effect_contract: Option<&poly_expr::ArgEffectContract>,
) -> FunctionAdapterHygiene {
    let mut markers = Vec::new();
    let mut arg_markers = Vec::new();
    let mut ret_markers = Vec::new();
    collect_function_boundary_markers(
        source,
        target,
        argument_effect_contract,
        &mut markers,
        &mut arg_markers,
        &mut ret_markers,
    );
    FunctionAdapterHygiene {
        markers,
        arg_markers,
        ret_markers,
    }
}

fn collect_function_boundary_markers(
    source: &Type,
    target: &Type,
    argument_effect_contract: Option<&poly_expr::ArgEffectContract>,
    markers: &mut Vec<GuardMarker>,
    arg_markers: &mut Vec<GuardMarker>,
    ret_markers: &mut Vec<GuardMarker>,
) {
    let (
        Type::Fun {
            arg: source_arg,
            ret: source_ret,
            ..
        },
        Type::Fun {
            arg: target_arg,
            ret: target_ret,
            ..
        },
    ) = (source, target)
    else {
        return;
    };

    if let Some(contract) = argument_effect_contract {
        collect_argument_contract_markers(contract, arg_markers);
    }
    collect_actual_runtime_shape_markers(target_arg, source_arg, 0, markers, ret_markers);
    collect_actual_runtime_shape_markers(source_ret, target_ret, 0, markers, ret_markers);
}

fn collect_argument_contract_markers(
    contract: &poly_expr::ArgEffectContract,
    markers: &mut Vec<GuardMarker>,
) {
    for marker in &contract.markers {
        match marker.resume {
            poly_expr::ContractResumePolicy::PreserveMatchingPath => {
                push_guard_marker_with_resume(
                    markers,
                    marker.depth,
                    &marker.path,
                    true,
                    false,
                    true,
                );
            }
            poly_expr::ContractResumePolicy::ForeignOnly => {
                push_guard_marker(markers, marker.depth, &marker.path, false, true);
            }
        }
    }
}

fn collect_actual_runtime_shape_markers(
    actual: &Type,
    expected: &Type,
    depth: u32,
    markers: &mut Vec<GuardMarker>,
    value_markers: &mut Vec<GuardMarker>,
) {
    if equivalent_boundary_types(actual, expected) {
        return;
    }

    match (actual, expected) {
        (
            Type::Thunk {
                effect: actual_effect,
                value: actual_value,
            },
            Type::Thunk {
                effect: expected_effect,
                value: expected_value,
            },
        ) => {
            if !equivalent_boundary_types(actual_effect, expected_effect) {
                collect_effect_markers_not_in_expected(
                    actual_effect,
                    expected_effect,
                    depth,
                    markers,
                    value_markers,
                );
            }
            collect_actual_runtime_shape_markers(
                actual_value,
                expected_value,
                depth,
                markers,
                value_markers,
            );
        }
        (
            Type::Thunk {
                effect,
                value: actual_value,
            },
            expected,
        ) => {
            collect_effect_markers(effect, depth, markers);
            collect_actual_runtime_shape_markers(
                actual_value,
                expected,
                depth,
                markers,
                value_markers,
            );
        }
        (
            actual,
            Type::Thunk {
                value: expected_value,
                ..
            },
        ) => {
            collect_actual_runtime_shape_markers(
                actual,
                expected_value,
                depth,
                markers,
                value_markers,
            );
        }
        (
            Type::Fun {
                arg: actual_arg,
                ret: actual_ret,
                ..
            },
            Type::Fun {
                arg: expected_arg,
                ret: expected_ret,
                ..
            },
        ) => {
            let nested_depth = depth.saturating_add(1);
            collect_actual_runtime_shape_markers(
                expected_arg,
                actual_arg,
                nested_depth,
                markers,
                value_markers,
            );
            collect_actual_runtime_shape_markers(
                actual_ret,
                expected_ret,
                nested_depth,
                markers,
                value_markers,
            );
        }
        (
            Type::Con {
                path: actual_path,
                args: actual_args,
            },
            Type::Con {
                path: expected_path,
                args: expected_args,
            },
        ) if actual_path == expected_path => {
            collect_actual_runtime_shape_marker_pairs(
                actual_args,
                expected_args,
                depth,
                markers,
                value_markers,
            );
        }
        (Type::Tuple(actual_items), Type::Tuple(expected_items)) => {
            collect_actual_runtime_shape_marker_pairs(
                actual_items,
                expected_items,
                depth,
                markers,
                value_markers,
            );
        }
        (Type::Record(actual_fields), Type::Record(expected_fields)) => {
            for actual_field in actual_fields {
                if let Some(expected_field) = expected_fields
                    .iter()
                    .find(|expected_field| expected_field.name == actual_field.name)
                {
                    collect_actual_runtime_shape_markers(
                        &actual_field.value,
                        &expected_field.value,
                        depth,
                        markers,
                        value_markers,
                    );
                } else {
                    collect_runtime_shape_markers(&actual_field.value, depth, markers);
                }
            }
        }
        (Type::PolyVariant(actual_variants), Type::PolyVariant(expected_variants)) => {
            for actual_variant in actual_variants {
                if let Some(expected_variant) = expected_variants
                    .iter()
                    .find(|expected_variant| expected_variant.name == actual_variant.name)
                {
                    collect_actual_runtime_shape_marker_pairs(
                        &actual_variant.payloads,
                        &expected_variant.payloads,
                        depth,
                        markers,
                        value_markers,
                    );
                } else {
                    for payload in &actual_variant.payloads {
                        collect_runtime_shape_markers(payload, depth, markers);
                    }
                }
            }
        }
        (Type::Union(actual_left, actual_right), Type::Union(expected_left, expected_right))
        | (
            Type::Intersection(actual_left, actual_right),
            Type::Intersection(expected_left, expected_right),
        ) => {
            collect_actual_runtime_shape_markers(
                actual_left,
                expected_left,
                depth,
                markers,
                value_markers,
            );
            collect_actual_runtime_shape_markers(
                actual_right,
                expected_right,
                depth,
                markers,
                value_markers,
            );
        }
        (
            Type::Stack { inner: actual, .. },
            Type::Stack {
                inner: expected, ..
            },
        ) => {
            collect_actual_runtime_shape_markers(actual, expected, depth, markers, value_markers);
        }
        _ => collect_runtime_shape_markers(actual, depth, markers),
    }
}

fn collect_actual_runtime_shape_marker_pairs(
    actual_items: &[Type],
    expected_items: &[Type],
    depth: u32,
    markers: &mut Vec<GuardMarker>,
    value_markers: &mut Vec<GuardMarker>,
) {
    let shared_len = actual_items.len().min(expected_items.len());
    for index in 0..shared_len {
        collect_actual_runtime_shape_markers(
            &actual_items[index],
            &expected_items[index],
            depth,
            markers,
            value_markers,
        );
    }
    for actual_item in &actual_items[shared_len..] {
        collect_runtime_shape_markers(actual_item, depth, markers);
    }
}

fn collect_runtime_shape_markers(ty: &Type, depth: u32, markers: &mut Vec<GuardMarker>) {
    match ty {
        Type::Thunk { effect, value } => {
            collect_effect_markers(effect, depth, markers);
            collect_runtime_shape_markers(value, depth, markers);
        }
        Type::Fun { arg, ret, .. } => {
            let nested_depth = depth.saturating_add(1);
            collect_runtime_shape_markers(arg, nested_depth, markers);
            collect_runtime_shape_markers(ret, nested_depth, markers);
        }
        Type::Con { args, .. } | Type::Tuple(args) => {
            for arg in args {
                collect_runtime_shape_markers(arg, depth, markers);
            }
        }
        Type::EffectRow(_) => {
            collect_effect_markers(ty, depth, markers);
        }
        Type::Record(fields) => {
            for field in fields {
                collect_runtime_shape_markers(&field.value, depth, markers);
            }
        }
        Type::PolyVariant(variants) => {
            for variant in variants {
                for payload in &variant.payloads {
                    collect_runtime_shape_markers(payload, depth, markers);
                }
            }
        }
        Type::Stack { inner, .. } => {
            collect_runtime_shape_markers(inner, depth, markers);
        }
        Type::Union(left, right) | Type::Intersection(left, right) => {
            collect_runtime_shape_markers(left, depth, markers);
            collect_runtime_shape_markers(right, depth, markers);
        }
        Type::Any | Type::Never | Type::OpenVar(_) => {}
    }
}

fn collect_effect_markers(effect: &Type, depth: u32, markers: &mut Vec<GuardMarker>) {
    if effect.is_pure_effect() {
        return;
    }
    match effect {
        Type::EffectRow(items) => {
            for item in items {
                collect_effect_markers(item, depth, markers);
            }
        }
        Type::Con { path, .. } => {
            push_guard_marker(markers, depth, path, true, false);
        }
        Type::Stack { inner, .. } => {
            collect_effect_markers(inner, depth, markers);
        }
        Type::Union(left, right) | Type::Intersection(left, right) => {
            collect_effect_markers(left, depth, markers);
            collect_effect_markers(right, depth, markers);
        }
        Type::Thunk { value, .. } => {
            collect_runtime_shape_markers(value, depth, markers);
        }
        Type::Fun { arg, ret, .. } => {
            let nested_depth = depth.saturating_add(1);
            collect_runtime_shape_markers(arg, nested_depth, markers);
            collect_runtime_shape_markers(ret, nested_depth, markers);
        }
        Type::Record(_)
        | Type::PolyVariant(_)
        | Type::Tuple(_)
        | Type::Any
        | Type::Never
        | Type::OpenVar(_) => {}
    }
}

fn collect_effect_markers_not_in_expected(
    actual: &Type,
    expected: &Type,
    depth: u32,
    markers: &mut Vec<GuardMarker>,
    value_markers: &mut Vec<GuardMarker>,
) {
    if actual.is_pure_effect() {
        return;
    }
    match actual {
        Type::EffectRow(items) => {
            for item in items {
                collect_effect_markers_not_in_expected(
                    item,
                    expected,
                    depth,
                    markers,
                    value_markers,
                );
            }
        }
        Type::Con { path, .. } => {
            if !effect_contains_path(expected, path) {
                push_guard_marker(markers, depth, path, true, false);
            }
        }
        Type::Stack { inner, .. } => {
            collect_effect_markers_not_in_expected(inner, expected, depth, markers, value_markers);
        }
        Type::Union(left, right) | Type::Intersection(left, right) => {
            collect_effect_markers_not_in_expected(left, expected, depth, markers, value_markers);
            collect_effect_markers_not_in_expected(right, expected, depth, markers, value_markers);
        }
        Type::Thunk { value, .. } => {
            collect_actual_runtime_shape_markers(value, expected, depth, markers, value_markers);
        }
        Type::Fun { arg, ret, .. } => {
            let nested_depth = depth.saturating_add(1);
            collect_effect_markers_not_in_expected(
                arg,
                expected,
                nested_depth,
                markers,
                value_markers,
            );
            collect_effect_markers_not_in_expected(
                ret,
                expected,
                nested_depth,
                markers,
                value_markers,
            );
        }
        Type::Record(_)
        | Type::PolyVariant(_)
        | Type::Tuple(_)
        | Type::Any
        | Type::Never
        | Type::OpenVar(_) => {}
    }
}

fn effect_contains_path(effect: &Type, path: &[String]) -> bool {
    if effect.is_pure_effect() {
        return false;
    }
    match effect {
        Type::EffectRow(items) => items.iter().any(|item| effect_contains_path(item, path)),
        Type::Con {
            path: effect_path, ..
        } => effect_path == path,
        Type::Stack { inner, .. } => effect_contains_path(inner, path),
        Type::Union(left, right) | Type::Intersection(left, right) => {
            effect_contains_path(left, path) || effect_contains_path(right, path)
        }
        Type::Thunk { value, .. } => effect_contains_path(value, path),
        Type::Fun { arg, ret, .. } => {
            effect_contains_path(arg, path) || effect_contains_path(ret, path)
        }
        Type::Record(fields) => fields
            .iter()
            .any(|field| effect_contains_path(&field.value, path)),
        Type::PolyVariant(variants) => variants.iter().any(|variant| {
            variant
                .payloads
                .iter()
                .any(|payload| effect_contains_path(payload, path))
        }),
        Type::Tuple(items) => items.iter().any(|item| effect_contains_path(item, path)),
        Type::Any | Type::Never | Type::OpenVar(_) => false,
    }
}

fn push_guard_marker(
    markers: &mut Vec<GuardMarker>,
    depth: u32,
    path: &[String],
    guard_own_path: bool,
    guard_foreign_path: bool,
) {
    push_guard_marker_with_resume(
        markers,
        depth,
        path,
        guard_own_path,
        guard_foreign_path,
        false,
    );
}

fn push_guard_marker_with_resume(
    markers: &mut Vec<GuardMarker>,
    depth: u32,
    path: &[String],
    guard_own_path: bool,
    guard_foreign_path: bool,
    preserve_own_on_resume: bool,
) {
    if path.is_empty() {
        return;
    }
    if let Some(marker) = markers
        .iter_mut()
        .find(|marker| marker.depth == depth && marker.path == path)
    {
        marker.guard_own_path |= guard_own_path;
        marker.guard_foreign_path |= guard_foreign_path;
        marker.preserve_own_on_resume |= preserve_own_on_resume;
        return;
    }
    markers.push(GuardMarker {
        path: path.to_vec(),
        depth,
        guard_own_path,
        guard_foreign_path,
        preserve_own_on_resume,
    });
}
