use std::collections::HashSet;

use crate::diagnostic::TypeErrorKind;
use crate::ids::{PosId, TypeVar};
use crate::scheme::OwnedSchemeInstance;
use crate::simplify::compact::CompactType;
use crate::solve::{EffectMethodInfo, Infer};
use crate::symbols::{ModuleId, Name, Path, Visibility};
use crate::types::Pos;

#[derive(Debug, Clone)]
pub(in crate::solve::selection) enum EffectMethodResolution {
    None,
    Unique(EffectMethodInfo),
    Ambiguous(Vec<EffectMethodInfo>),
}

impl Infer {
    pub(in crate::solve::selection) fn resolve_effect_method_info_from(
        &self,
        module: ModuleId,
        recv_eff: TypeVar,
        name: &Name,
    ) -> EffectMethodResolution {
        let Some(methods) = self.effect_methods.get(name) else {
            return EffectMethodResolution::None;
        };
        let mut seen = HashSet::new();
        let effects = self.collect_effect_paths_from_tv(recv_eff, &mut seen);
        let mut candidates = Vec::new();
        for effect in effects {
            candidates.extend(
                methods
                    .iter()
                    .filter(|info| {
                        effect_method_path_matches(&info.effect, &effect)
                            && effect_method_is_accessible_from(module, info)
                    })
                    .cloned(),
            );
        }
        dedup_effect_method_candidates(&mut candidates);
        match candidates.as_slice() {
            [] => EffectMethodResolution::None,
            [info] => EffectMethodResolution::Unique(info.clone()),
            _ => EffectMethodResolution::Ambiguous(candidates),
        }
    }

    pub(in crate::solve::selection) fn report_ambiguous_effect_method(
        &self,
        name: &Name,
        candidates: &[EffectMethodInfo],
        result_tv: TypeVar,
    ) {
        self.report_synthetic_type_error(
            TypeErrorKind::AmbiguousEffectMethod {
                method: name.0.clone(),
                effects: candidates
                    .iter()
                    .map(|info| path_string(&info.effect))
                    .collect(),
            },
            format!("effect method call {}", result_tv.0),
        );
    }

    fn collect_effect_paths_from_tv(&self, tv: TypeVar, seen: &mut HashSet<TypeVar>) -> Vec<Path> {
        if !seen.insert(tv) {
            return Vec::new();
        }
        let mut out = Vec::new();
        for lower in self.lower_refs_of(tv) {
            self.collect_effect_paths_from_pos(lower, seen, &mut out);
        }
        for instance in self.compact_lower_instances_of(tv) {
            self.collect_effect_paths_from_compact_instance(&instance, seen, &mut out);
        }
        out
    }

    fn collect_effect_paths_from_pos(
        &self,
        pos: PosId,
        seen: &mut HashSet<TypeVar>,
        out: &mut Vec<Path>,
    ) {
        match self.arena.get_pos(pos) {
            Pos::Atom(atom) => push_unique_path(out, atom.path.clone()),
            Pos::Row(items, tail) => {
                for item in items {
                    self.collect_effect_paths_from_pos(item, seen, out);
                }
                self.collect_effect_paths_from_pos(tail, seen, out);
            }
            Pos::Var(inner) | Pos::Raw(inner) => {
                for effect in self.collect_effect_paths_from_tv(inner, seen) {
                    push_unique_path(out, effect);
                }
            }
            Pos::Union(lhs, rhs) => {
                self.collect_effect_paths_from_pos(lhs, seen, out);
                self.collect_effect_paths_from_pos(rhs, seen, out);
            }
            _ => {}
        }
    }

    fn collect_effect_paths_from_compact_instance(
        &self,
        instance: &OwnedSchemeInstance,
        seen: &mut HashSet<TypeVar>,
        out: &mut Vec<Path>,
    ) {
        self.collect_effect_paths_from_compact_type(
            &instance.scheme.compact.cty.lower,
            instance.subst.as_slice(),
            seen,
            out,
        );
    }

    fn collect_effect_paths_from_compact_type(
        &self,
        ty: &CompactType,
        subst: &[(TypeVar, TypeVar)],
        seen: &mut HashSet<TypeVar>,
        out: &mut Vec<Path>,
    ) {
        for row in &ty.rows {
            for item in &row.items {
                collect_effect_item_paths(item, out);
                for tv in &item.vars {
                    for effect in
                        self.collect_effect_paths_from_tv(lookup_small_subst(subst, *tv), seen)
                    {
                        push_unique_path(out, effect);
                    }
                }
            }
            self.collect_effect_paths_from_compact_type(&row.tail, subst, seen, out);
        }
        for tv in &ty.vars {
            for effect in self.collect_effect_paths_from_tv(lookup_small_subst(subst, *tv), seen) {
                push_unique_path(out, effect);
            }
        }
    }
}

fn collect_effect_item_paths(item: &CompactType, out: &mut Vec<Path>) {
    for path in &item.prims {
        push_unique_path(out, path.clone());
    }
    for con in &item.cons {
        push_unique_path(out, con.path.clone());
    }
}

fn dedup_effect_method_candidates(candidates: &mut Vec<EffectMethodInfo>) {
    let mut seen = HashSet::new();
    candidates.retain(|candidate| seen.insert(candidate.def));
}

fn effect_method_is_accessible_from(module: ModuleId, info: &EffectMethodInfo) -> bool {
    match info.visibility {
        Visibility::My => module == info.module,
        Visibility::Our | Visibility::Pub => true,
    }
}

fn effect_method_path_matches(method_effect: &Path, receiver_effect: &Path) -> bool {
    method_effect == receiver_effect
        || fully_qualified_prefix_path(receiver_effect, method_effect)
        || fully_qualified_prefix_path(method_effect, receiver_effect)
}

fn fully_qualified_prefix_path(prefix: &Path, path: &Path) -> bool {
    prefix.segments.len() > 1
        && path.segments.len() > prefix.segments.len()
        && path.segments.starts_with(prefix.segments.as_slice())
}

fn lookup_small_subst(subst: &[(TypeVar, TypeVar)], tv: TypeVar) -> TypeVar {
    subst
        .iter()
        .find_map(|(from, to)| (*from == tv).then_some(*to))
        .unwrap_or(tv)
}

fn push_unique_path(out: &mut Vec<Path>, path: Path) {
    if !out.contains(&path) {
        out.push(path);
    }
}

fn path_string(path: &Path) -> String {
    path.segments
        .iter()
        .map(|segment| segment.0.as_str())
        .collect::<Vec<_>>()
        .join("::")
}
