//! User-defined cast の raw table。
//!
//! cast 解決は、型推論中に「cast 関数を適用した結果の制約」を追加するための補助情報を読む。
//! ここでは source / target の型 constructor path と、その変換に使う scheme だけを保持する。

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

    pub fn insert(
        &mut self,
        source: TypeConstructorPath,
        target: TypeConstructorPath,
        scheme: Scheme,
    ) {
        let key = CastKey {
            source: source.clone(),
            target: target.clone(),
        };
        self.casts.entry(key).or_default().value.push(CastRule {
            def: None,
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
}
