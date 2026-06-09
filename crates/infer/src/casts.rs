//! User-defined cast の raw table。
//!
//! cast 解決は、型推論中に「cast 関数を適用した結果の制約」を追加するための補助情報を読む。
//! ここでは source / target の型 constructor path と、その変換に使う scheme だけを保持する。

use poly::types::Scheme;
use rustc_hash::FxHashMap;

pub type TypeConstructorPath = Vec<String>;

#[derive(Clone, Default)]
pub struct CastTable {
    casts: FxHashMap<CastKey, Vec<CastRule>>,
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
        self.casts.entry(key).or_default().push(CastRule {
            source,
            target,
            scheme,
        });
    }

    pub fn candidates(&self, source: &[String], target: &[String]) -> &[CastRule] {
        self.casts
            .get(&CastKey {
                source: source.to_vec(),
                target: target.to_vec(),
            })
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    pub fn is_empty(&self) -> bool {
        self.casts.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct CastKey {
    source: TypeConstructorPath,
    target: TypeConstructorPath,
}

#[derive(Clone)]
pub struct CastRule {
    pub source: TypeConstructorPath,
    pub target: TypeConstructorPath,
    pub scheme: Scheme,
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
                predicate: PosId(0),
                subtracts: Vec::new(),
            },
        );

        let candidates = table.candidates(&["int".into()], &["user_id".into()]);

        assert_eq!(candidates.len(), 1);
        assert_eq!(candidates[0].source, vec!["int".to_string()]);
        assert_eq!(candidates[0].target, vec!["user_id".to_string()]);
        assert!(
            table
                .candidates(&["user_id".into()], &["int".into()])
                .is_empty()
        );
    }
}
