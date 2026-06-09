//! use-site ごとの推論メタデータ。
//!
//! `poly` には `RefId -> DefId` と `SelectId -> resolution` だけを残す。
//! しかし推論中は、各 use-site がどの parent def の中にあり、どの型 slot で使われたかが必要になる。
//! その情報を `poly` に混ぜず、この module の table に分ける。

use poly::expr::{DefId, RefId, SelectId};
use poly::types::TypeVar;
use rustc_hash::FxHashMap;

#[derive(Debug, Clone, Default)]
/// `DefId` に対応する型 slot。
///
/// `typing::Typing` と役割が近いが、こちらは use-site table と同じ module に置いた軽量 table。
/// 後でどちらを入口にするか整理できるよう、意味は「定義そのものの型」に限定する。
pub struct DefTypes {
    defs: FxHashMap<DefId, TypeVar>,
}

impl DefTypes {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn set(&mut self, def: DefId, ty: TypeVar) -> Option<TypeVar> {
        self.defs.insert(def, ty)
    }

    pub fn get(&self, def: DefId) -> Option<TypeVar> {
        self.defs.get(&def).copied()
    }
}

#[derive(Debug, Clone, Default)]
/// 参照 use-site の table。
///
/// `RefId` の解決先は `poly::Arena` に書き戻す。一方で、SCC edge を張るには
/// 「どの parent def からの use か」と「この use-site の値型 slot」が必要になるため、
/// その2つだけをここに置く。
pub struct RefUseTable {
    uses: FxHashMap<RefId, RefUse>,
}

impl RefUseTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, id: RefId, use_site: RefUse) -> Option<RefUse> {
        self.uses.insert(id, use_site)
    }

    pub fn get(&self, id: RefId) -> Option<&RefUse> {
        self.uses.get(&id)
    }

    pub fn parent(&self, id: RefId) -> Option<DefId> {
        self.get(id).map(|use_site| use_site.parent)
    }

    pub fn value(&self, id: RefId) -> Option<TypeVar> {
        self.get(id).map(|use_site| use_site.value)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// 1つの `RefId` use-site に対応する推論メタデータ。
pub struct RefUse {
    pub parent: DefId,
    pub value: TypeVar,
}

#[derive(Debug, Clone, Default)]
/// selection use-site の table。
///
/// dot selection は、receiver の下界が増えた時に解ける場合と、`ref '[e] a` の payload `a` の
/// 下界が増えた時に解ける場合がある。そのため watcher を receiver 用と ref payload 用の2枠に分ける。
pub struct SelectionUseTable {
    uses: FxHashMap<SelectId, SelectionUse>,
    pending_by_receiver: FxHashMap<TypeVar, Vec<SelectId>>,
    pending_by_ref_payload: FxHashMap<TypeVar, Vec<SelectId>>,
}

impl SelectionUseTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, id: SelectId, use_site: SelectionUse) -> Option<SelectionUse> {
        self.uses.insert(id, use_site)
    }

    pub fn get(&self, id: SelectId) -> Option<&SelectionUse> {
        self.uses.get(&id)
    }

    pub fn iter(&self) -> impl Iterator<Item = (SelectId, &SelectionUse)> {
        self.uses.iter().map(|(id, use_site)| (*id, use_site))
    }

    pub fn watch_receiver(&mut self, var: TypeVar, select: SelectId) {
        push_unique(self.pending_by_receiver.entry(var).or_default(), select);
    }

    pub fn watch_ref_payload(&mut self, var: TypeVar, select: SelectId) {
        push_unique(self.pending_by_ref_payload.entry(var).or_default(), select);
    }

    pub fn pending_for_lower_bound(&self, var: TypeVar) -> Vec<SelectId> {
        let mut pending = Vec::new();
        if let Some(selects) = self.pending_by_receiver.get(&var) {
            pending.extend(selects.iter().copied());
        }
        if let Some(selects) = self.pending_by_ref_payload.get(&var) {
            for select in selects {
                push_unique(&mut pending, *select);
            }
        }
        pending
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// 1つの `SelectId` use-site に対応する推論メタデータ。
///
/// `receiver_value` は selection を解くために見る receiver の型 slot。
/// `method_value` は method として解けた場合に hidden use として instantiate / SCC に渡す slot。
/// method の結果型や effect は method 自身の型から制約で出るため、ここには持たせない。
pub struct SelectionUse {
    pub parent: DefId,
    pub receiver_value: TypeVar,
    pub method_value: TypeVar,
}

fn push_unique<T: Copy + PartialEq>(items: &mut Vec<T>, item: T) {
    if !items.contains(&item) {
        items.push(item);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ref_use_records_parent_and_use_site_type() {
        let mut table = RefUseTable::new();
        let reference = RefId(0);
        let use_site = RefUse {
            parent: DefId(1),
            value: TypeVar(2),
        };

        table.insert(reference, use_site);

        assert_eq!(table.parent(reference), Some(DefId(1)));
        assert_eq!(table.value(reference), Some(TypeVar(2)));
    }

    #[test]
    fn selection_use_has_receiver_and_ref_payload_watch_sets() {
        let mut table = SelectionUseTable::new();
        let select = SelectId(0);
        table.insert(
            select,
            SelectionUse {
                parent: DefId(1),
                receiver_value: TypeVar(2),
                method_value: TypeVar(3),
            },
        );
        table.watch_receiver(TypeVar(2), select);
        table.watch_ref_payload(TypeVar(4), select);
        table.watch_ref_payload(TypeVar(4), select);

        assert_eq!(table.pending_for_lower_bound(TypeVar(2)), vec![select]);
        assert_eq!(table.pending_for_lower_bound(TypeVar(4)), vec![select]);
        assert_eq!(table.get(select).unwrap().method_value, TypeVar(3));
    }
}
