//! User-defined cast の raw table。
//!
//! cast 解決は、型推論中に「cast 関数を適用した結果の制約」を追加するための補助情報を読む。
//! ここでは source / target の型 constructor path、宣言 identity、その変換に使う scheme を保持する。

use poly::cast_resolution::{OrdinaryCastResolution, classify_ordinary_cast_candidates};
use poly::expr::{CastRuleKind, DefId};
use poly::types::Scheme;
use rustc_hash::FxHashMap;

pub type TypeConstructorPath = Vec<String>;

#[derive(Clone, Default)]
pub struct CastTable {
    casts: FxHashMap<CastKey, CastRuleBucket>,
}

impl CastTable {
    pub fn new() -> Self {
        Self::default()
    }

    #[cfg(test)]
    pub fn insert(
        &mut self,
        source: TypeConstructorPath,
        target: TypeConstructorPath,
        scheme: Scheme,
    ) {
        self.insert_value_rule(None, source, target, scheme);
    }

    pub fn insert_value(
        &mut self,
        def: DefId,
        source: TypeConstructorPath,
        target: TypeConstructorPath,
        scheme: Scheme,
    ) {
        self.insert_value_rule(Some(def), source, target, scheme);
    }

    fn insert_value_rule(
        &mut self,
        def: Option<DefId>,
        source: TypeConstructorPath,
        target: TypeConstructorPath,
        scheme: Scheme,
    ) {
        let key = CastKey {
            source: source.clone(),
            target: target.clone(),
        };
        self.casts.entry(key).or_default().value.push(CastRule {
            def,
            source,
            target,
            scheme,
            kind: CastRuleKind::Value,
        });
    }

    pub fn candidates(&self, source: &[String], target: &[String]) -> &[CastRule] {
        self.casts
            .get(&CastKey {
                source: source.to_vec(),
                target: target.to_vec(),
            })
            .map(|bucket| bucket.value.as_slice())
            .unwrap_or(&[])
    }

    /// Resolve ordinary value declarations for one exact constructor pair by cardinality.
    pub fn resolve_value(
        &self,
        source: &[String],
        target: &[String],
    ) -> OrdinaryCastResolution<CastRule> {
        classify_ordinary_cast_candidates(
            self.candidates(source, target)
                .iter()
                .filter(|rule| {
                    rule.kind == CastRuleKind::Value
                        && rule.source.as_slice() == source
                        && rule.target.as_slice() == target
                })
                .cloned(),
        )
    }

    pub fn insert_effect_up(
        &mut self,
        def: DefId,
        source: TypeConstructorPath,
        target: TypeConstructorPath,
        scheme: Scheme,
    ) {
        let key = CastKey {
            source: source.clone(),
            target: target.clone(),
        };
        self.casts.entry(key).or_default().effect_up.push(CastRule {
            def: Some(def),
            source,
            target,
            scheme,
            kind: CastRuleKind::EffectUp,
        });
    }

    pub fn effect_up_candidates(&self, source: &[String], target: &[String]) -> &[CastRule] {
        self.casts
            .get(&CastKey {
                source: source.to_vec(),
                target: target.to_vec(),
            })
            .map(|bucket| bucket.effect_up.as_slice())
            .unwrap_or(&[])
    }

    pub fn effect_up_defs_for_target(&self, target: &[String]) -> Vec<DefId> {
        let mut defs = self
            .casts
            .iter()
            .filter(|(key, _)| key.target == target)
            .flat_map(|(_, bucket)| bucket.effect_up.iter().filter_map(|rule| rule.def))
            .collect::<Vec<_>>();
        defs.sort_by_key(|def| def.0);
        defs.dedup();
        defs
    }

    pub fn is_empty(&self) -> bool {
        self.casts.is_empty()
    }
}

#[derive(Clone, Default)]
struct CastRuleBucket {
    value: Vec<CastRule>,
    effect_up: Vec<CastRule>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct CastKey {
    source: TypeConstructorPath,
    target: TypeConstructorPath,
}

#[derive(Clone)]
pub struct CastRule {
    pub def: Option<DefId>,
    pub source: TypeConstructorPath,
    pub target: TypeConstructorPath,
    pub scheme: Scheme,
    pub kind: CastRuleKind,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum OrdinaryCastShadowSeam {
    NominalConstraint,
    CompactDiscovery,
}

#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum OrdinaryCastShadowOutcome {
    Missing,
    Unique,
    Ambiguous,
}

#[cfg(test)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct OrdinaryCastShadowWitness {
    pub(crate) seam: OrdinaryCastShadowSeam,
    pub(crate) source: TypeConstructorPath,
    pub(crate) target: TypeConstructorPath,
    pub(crate) outcome: OrdinaryCastShadowOutcome,
    pub(crate) candidate_defs: Vec<Option<DefId>>,
}

#[cfg(test)]
thread_local! {
    static ORDINARY_CAST_SHADOW_WITNESSES:
        std::cell::RefCell<Option<Vec<OrdinaryCastShadowWitness>>> = const {
            std::cell::RefCell::new(None)
        };
}

#[cfg(test)]
pub(crate) fn begin_ordinary_cast_shadow_capture() {
    ORDINARY_CAST_SHADOW_WITNESSES.with(|witnesses| {
        *witnesses.borrow_mut() = Some(Vec::new());
    });
}

#[cfg(test)]
pub(crate) fn finish_ordinary_cast_shadow_capture() -> Vec<OrdinaryCastShadowWitness> {
    ORDINARY_CAST_SHADOW_WITNESSES
        .with(|witnesses| witnesses.borrow_mut().take().unwrap_or_default())
}

#[cfg(test)]
pub(crate) fn observe_ordinary_cast_resolution(
    casts: &CastTable,
    seam: OrdinaryCastShadowSeam,
    source: &[String],
    target: &[String],
) {
    let capture_enabled =
        ORDINARY_CAST_SHADOW_WITNESSES.with(|witnesses| witnesses.borrow().is_some());
    if !capture_enabled {
        return;
    }

    let resolution = casts.resolve_value(source, target);
    let (outcome, candidate_defs) = match resolution {
        OrdinaryCastResolution::Missing => (OrdinaryCastShadowOutcome::Missing, Vec::new()),
        OrdinaryCastResolution::Unique(rule) => (OrdinaryCastShadowOutcome::Unique, vec![rule.def]),
        OrdinaryCastResolution::Ambiguous(rules) => (
            OrdinaryCastShadowOutcome::Ambiguous,
            rules.into_iter().map(|rule| rule.def).collect(),
        ),
    };
    let witness = OrdinaryCastShadowWitness {
        seam,
        source: source.to_vec(),
        target: target.to_vec(),
        outcome,
        candidate_defs,
    };
    ORDINARY_CAST_SHADOW_WITNESSES.with(|witnesses| {
        if let Some(witnesses) = witnesses.borrow_mut().as_mut() {
            witnesses.push(witness);
        }
    });
}

#[cfg(test)]
mod tests {
    use poly::types::{PosId, Scheme};

    use super::*;

    #[test]
    fn stores_cast_candidates_by_constructor_pair() {
        let mut table = CastTable::new();
        table.insert(
            vec!["int".into()],
            vec!["user_id".into()],
            Scheme {
                quantifiers: Vec::new(),
                role_predicates: Vec::new(),
                recursive_bounds: Vec::new(),
                stack_quantifiers: Vec::new(),
                predicate: PosId(0),
            },
        );

        let candidates = table.candidates(&["int".into()], &["user_id".into()]);

        assert_eq!(candidates.len(), 1);
        assert!(candidates[0].def.is_none());
        assert_eq!(candidates[0].source, vec!["int".to_string()]);
        assert_eq!(candidates[0].target, vec!["user_id".to_string()]);
        assert_eq!(candidates[0].kind, CastRuleKind::Value);
        assert!(
            table
                .candidates(&["user_id".into()], &["int".into()])
                .is_empty()
        );
    }

    #[test]
    fn resolve_value_filters_kind_and_exact_paths_before_classification() {
        let mut table = CastTable::new();
        let source = vec!["int".into()];
        let target = vec!["user_id".into()];
        let scheme = Scheme {
            quantifiers: Vec::new(),
            role_predicates: Vec::new(),
            recursive_bounds: Vec::new(),
            stack_quantifiers: Vec::new(),
            predicate: PosId(0),
        };
        table.insert_value(DefId(1), source.clone(), target.clone(), scheme.clone());
        let bucket = table
            .casts
            .get_mut(&CastKey {
                source: source.clone(),
                target: target.clone(),
            })
            .expect("exact-pair bucket");
        bucket.value.push(CastRule {
            def: Some(DefId(2)),
            source: source.clone(),
            target: target.clone(),
            scheme: scheme.clone(),
            kind: CastRuleKind::EffectUp,
        });
        bucket.value.push(CastRule {
            def: Some(DefId(3)),
            source: vec!["other".into()],
            target: target.clone(),
            scheme,
            kind: CastRuleKind::Value,
        });

        let OrdinaryCastResolution::Unique(rule) = table.resolve_value(&source, &target) else {
            panic!("only the exact value rule should reach the classifier")
        };
        assert_eq!(rule.def, Some(DefId(1)));
    }
}
