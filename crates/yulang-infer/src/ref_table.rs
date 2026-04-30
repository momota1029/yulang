use std::collections::HashMap;

use crate::ids::{DefId, RefId, TypeVar};
use crate::symbols::{ModuleId, Path};

// ── RefTable ─────────────────────────────────────────────────────────────────

/// RefId → DefId の対応表。
/// lowering ワンパスで名前解決しながら積み上げる。
/// 解決できなかった RefId は unresolved に残る。
#[derive(Debug, Default)]
pub struct RefTable {
    resolved: HashMap<RefId, ResolvedRef>,
    unresolved: Vec<(RefId, UnresolvedRef)>,
}

#[derive(Debug, Clone, Copy)]
pub struct ResolvedRef {
    pub def_id: DefId,
    pub ref_tv: TypeVar,
    pub owner: Option<DefId>,
}

/// まだ解決できていない参照の情報。
#[derive(Debug, Clone)]
pub struct UnresolvedRef {
    /// 参照されたパス（単純名なら segments.len() == 1）
    pub path: Path,
    /// どのモジュール文脈でこの参照を見たか。
    pub module: ModuleId,
    /// その参照を見た時点で有効だった `use` path。
    pub use_paths: Vec<Path>,
    /// この参照ノード自身の型変数。
    pub ref_tv: TypeVar,
    /// この参照を含む owner。
    pub owner: Option<DefId>,
}

impl RefTable {
    pub fn resolve(&mut self, ref_id: RefId, def_id: DefId, ref_tv: TypeVar, owner: Option<DefId>) {
        self.resolved.insert(
            ref_id,
            ResolvedRef {
                def_id,
                ref_tv,
                owner,
            },
        );
    }

    pub fn push_unresolved(&mut self, ref_id: RefId, info: UnresolvedRef) {
        self.unresolved.push((ref_id, info));
    }

    pub fn get(&self, ref_id: RefId) -> Option<DefId> {
        self.resolved.get(&ref_id).map(|resolved| resolved.def_id)
    }

    pub fn unresolved(&self) -> &[(RefId, UnresolvedRef)] {
        &self.unresolved
    }

    pub fn has_unresolved(&self) -> bool {
        !self.unresolved.is_empty()
    }

    pub fn resolved(&self) -> &HashMap<RefId, ResolvedRef> {
        &self.resolved
    }

    pub fn resolve_pending<F>(&mut self, mut f: F)
    where
        F: FnMut(&UnresolvedRef) -> Option<DefId>,
    {
        let unresolved = std::mem::take(&mut self.unresolved);
        for (ref_id, info) in unresolved {
            if let Some(def_id) = f(&info) {
                self.resolve(ref_id, def_id, info.ref_tv, info.owner);
            } else {
                self.unresolved.push((ref_id, info));
            }
        }
    }
}
