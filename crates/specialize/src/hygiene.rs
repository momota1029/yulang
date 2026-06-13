//! Function adapter に載せる runtime guard marker plan を作る。
//!
//! `specialize` は runtime lower が call spine から hygiene を推測しなくてよいように、
//! 関数値が producer-consumer 境界を越えた時点で必要な marker を mono IR に残す。

use mono::{FunctionAdapterHygiene, GuardMarker, Type};

use crate::equivalent_boundary_types;

pub(crate) fn function_adapter_hygiene(source: &Type, target: &Type) -> FunctionAdapterHygiene {
    let mut markers = Vec::new();
    collect_function_boundary_markers(source, target, &mut markers);
    FunctionAdapterHygiene { markers }
}

fn collect_function_boundary_markers(source: &Type, target: &Type, markers: &mut Vec<GuardMarker>) {
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

    collect_runtime_shape_pair(source_arg, target_arg, 0, markers);
    collect_runtime_shape_pair(source_ret, target_ret, 0, markers);
}

fn collect_runtime_shape_pair(
    source: &Type,
    target: &Type,
    depth: u32,
    markers: &mut Vec<GuardMarker>,
) {
    if equivalent_boundary_types(source, target) {
        return;
    }

    match (source, target) {
        (
            Type::Thunk {
                effect: source_effect,
                value: source_value,
            },
            Type::Thunk {
                effect: target_effect,
                value: target_value,
            },
        ) => {
            if !equivalent_boundary_types(source_effect, target_effect) {
                collect_effect_markers(source_effect, depth, markers);
                collect_effect_markers(target_effect, depth, markers);
            }
            collect_runtime_shape_pair(source_value, target_value, depth, markers);
        }
        (
            Type::Thunk {
                effect,
                value: source_value,
            },
            target,
        ) => {
            collect_effect_markers(effect, depth, markers);
            collect_runtime_shape_pair(source_value, target, depth, markers);
        }
        (
            source,
            Type::Thunk {
                effect,
                value: target_value,
            },
        ) => {
            collect_effect_markers(effect, depth, markers);
            collect_runtime_shape_pair(source, target_value, depth, markers);
        }
        (
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
        ) => {
            let nested_depth = depth.saturating_add(1);
            collect_runtime_shape_pair(source_arg, target_arg, nested_depth, markers);
            collect_runtime_shape_pair(source_ret, target_ret, nested_depth, markers);
        }
        (
            Type::Con {
                path: source_path,
                args: source_args,
            },
            Type::Con {
                path: target_path,
                args: target_args,
            },
        ) if source_path == target_path => {
            collect_runtime_shape_pairs(source_args, target_args, depth, markers);
        }
        (Type::Tuple(source_items), Type::Tuple(target_items)) => {
            collect_runtime_shape_pairs(source_items, target_items, depth, markers);
        }
        (Type::Record(source_fields), Type::Record(target_fields)) => {
            for source_field in source_fields {
                if let Some(target_field) = target_fields
                    .iter()
                    .find(|target_field| target_field.name == source_field.name)
                {
                    collect_runtime_shape_pair(
                        &source_field.value,
                        &target_field.value,
                        depth,
                        markers,
                    );
                } else {
                    collect_runtime_shape_markers(&source_field.value, depth, markers);
                }
            }
            for target_field in target_fields {
                if !source_fields
                    .iter()
                    .any(|source_field| source_field.name == target_field.name)
                {
                    collect_runtime_shape_markers(&target_field.value, depth, markers);
                }
            }
        }
        (Type::PolyVariant(source_variants), Type::PolyVariant(target_variants)) => {
            for source_variant in source_variants {
                if let Some(target_variant) = target_variants
                    .iter()
                    .find(|target_variant| target_variant.name == source_variant.name)
                {
                    collect_runtime_shape_pairs(
                        &source_variant.payloads,
                        &target_variant.payloads,
                        depth,
                        markers,
                    );
                } else {
                    for payload in &source_variant.payloads {
                        collect_runtime_shape_markers(payload, depth, markers);
                    }
                }
            }
            for target_variant in target_variants {
                if !source_variants
                    .iter()
                    .any(|source_variant| source_variant.name == target_variant.name)
                {
                    for payload in &target_variant.payloads {
                        collect_runtime_shape_markers(payload, depth, markers);
                    }
                }
            }
        }
        (Type::Union(source_left, source_right), Type::Union(target_left, target_right))
        | (
            Type::Intersection(source_left, source_right),
            Type::Intersection(target_left, target_right),
        ) => {
            collect_runtime_shape_pair(source_left, target_left, depth, markers);
            collect_runtime_shape_pair(source_right, target_right, depth, markers);
        }
        (Type::Stack { inner: source, .. }, Type::Stack { inner: target, .. }) => {
            collect_runtime_shape_pair(source, target, depth, markers);
        }
        _ => {
            collect_runtime_shape_markers(source, depth, markers);
            collect_runtime_shape_markers(target, depth, markers);
        }
    }
}

fn collect_runtime_shape_pairs(
    source_items: &[Type],
    target_items: &[Type],
    depth: u32,
    markers: &mut Vec<GuardMarker>,
) {
    let shared_len = source_items.len().min(target_items.len());
    for index in 0..shared_len {
        collect_runtime_shape_pair(&source_items[index], &target_items[index], depth, markers);
    }
    for source_item in &source_items[shared_len..] {
        collect_runtime_shape_markers(source_item, depth, markers);
    }
    for target_item in &target_items[shared_len..] {
        collect_runtime_shape_markers(target_item, depth, markers);
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
            push_guard_marker(markers, depth, path);
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

fn push_guard_marker(markers: &mut Vec<GuardMarker>, depth: u32, path: &[String]) {
    if path.is_empty()
        || markers
            .iter()
            .any(|marker| marker.depth == depth && marker.path == path)
    {
        return;
    }
    markers.push(GuardMarker {
        path: path.to_vec(),
        depth,
    });
}
