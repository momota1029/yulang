//! use-site ごとの推論メタデータ。
//!
//! `poly` には `RefId -> DefId` と `SelectId -> resolution` だけを残す。
//! しかし推論中は、各 use-site がどの parent def の中にあり、どの型 slot で使われたかが必要になる。
//! その情報を `poly` に混ぜず、この module の table に分ける。

use poly::expr::{DefId, RefId, SelectId};
use poly::types::TypeVar;
use rustc_hash::FxHashMap;

use crate::{ModuleId, SourceSpan};

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
/// source 上の局所 def に対応する推論メタデータ。
///
/// `Def::Arg` は scheme を持たないため、hover などの source tool は lowering 中の
/// value slot をここから読む。`poly` の定義種別には混ぜず、use-site metadata と同じ層に置く。
pub struct LocalDefUseTable {
    defs: FxHashMap<DefId, LocalDefUse>,
}

impl LocalDefUseTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, def: DefId, use_site: LocalDefUse) -> Option<LocalDefUse> {
        self.defs.insert(def, use_site)
    }

    pub fn get(&self, def: DefId) -> Option<&LocalDefUse> {
        self.defs.get(&def)
    }

    pub fn get_mut(&mut self, def: DefId) -> Option<&mut LocalDefUse> {
        self.defs.get_mut(&def)
    }

    pub fn source_spans(&self) -> impl Iterator<Item = (DefId, &SourceSpan)> {
        self.defs
            .iter()
            .filter_map(|(def, use_site)| use_site.source_span.as_ref().map(|span| (*def, span)))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// 1つの局所 def に対応する推論メタデータ。
pub struct LocalDefUse {
    pub value: TypeVar,
    pub source_span: Option<SourceSpan>,
    pub role: LocalDefRole,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LocalDefRole {
    Value,
    Input,
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

    pub fn iter(&self) -> impl Iterator<Item = (RefId, &RefUse)> {
        self.uses.iter().map(|(id, use_site)| (*id, use_site))
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
/// 1つの `RefId` use-site に対応する推論メタデータ。
pub struct RefUse {
    pub parent: DefId,
    pub value: TypeVar,
    pub source_span: Option<SourceSpan>,
}

#[derive(Debug, Clone, Default)]
/// selection use-site の table。
///
/// `uses` に残っている `SelectId` は未解決 selection だけを表す。解決結果は
/// `poly::expr::Select.resolution` に書き戻されるため、ここでは解決後の use-site を保持しない。
///
/// dot selection は、`method_value` の関数上界に入っている receiver の下界、
/// `ref '[e] a` の payload `a` の下界、receiver effect の row/subtract fact が増えた時に
/// 解ける場合がある。
pub struct SelectionUseTable {
    uses: FxHashMap<SelectId, SelectionUse>,
    source_spans: FxHashMap<SelectId, SourceSpan>,
    resolved: FxHashMap<SelectId, ResolvedSelectionUse>,
    pending_by_receiver: FxHashMap<TypeVar, Vec<SelectId>>,
    pending_by_ref_payload: FxHashMap<TypeVar, Vec<SelectId>>,
    pending_by_effect: FxHashMap<TypeVar, Vec<SelectId>>,
}

impl SelectionUseTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, id: SelectId, use_site: SelectionUse) -> Option<SelectionUse> {
        self.uses.insert(id, use_site)
    }

    pub fn insert_source_span(&mut self, id: SelectId, source_span: SourceSpan) {
        self.source_spans.insert(id, source_span);
    }

    pub fn get(&self, id: SelectId) -> Option<&SelectionUse> {
        self.uses.get(&id)
    }

    pub fn source_span(&self, id: SelectId) -> Option<&SourceSpan> {
        self.source_spans.get(&id)
    }

    pub fn source_spans(&self) -> impl Iterator<Item = (SelectId, &SourceSpan)> {
        self.source_spans
            .iter()
            .map(|(select, span)| (*select, span))
    }

    pub fn insert_resolved(&mut self, id: SelectId, use_site: ResolvedSelectionUse) {
        self.resolved.insert(id, use_site);
    }

    pub fn resolved(&self, id: SelectId) -> Option<&ResolvedSelectionUse> {
        self.resolved.get(&id)
    }

    pub fn remove(&mut self, id: SelectId) -> Option<SelectionUse> {
        self.uses.remove(&id)
    }

    pub fn iter(&self) -> impl Iterator<Item = (SelectId, &SelectionUse)> {
        self.uses.iter().map(|(id, use_site)| (*id, use_site))
    }

    pub fn unresolved(&self) -> impl Iterator<Item = SelectId> + '_ {
        self.uses.keys().copied()
    }

    pub fn watch_receiver(&mut self, var: TypeVar, select: SelectId) {
        push_unique(self.pending_by_receiver.entry(var).or_default(), select);
    }

    pub fn watch_ref_payload(&mut self, var: TypeVar, select: SelectId) {
        push_unique(self.pending_by_ref_payload.entry(var).or_default(), select);
    }

    pub fn watch_effect(&mut self, var: TypeVar, select: SelectId) {
        push_unique(self.pending_by_effect.entry(var).or_default(), select);
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
        if let Some(selects) = self.pending_by_effect.get(&var) {
            for select in selects {
                push_unique(&mut pending, *select);
            }
        }
        pending
    }

    pub fn pending_for_effect_fact(&self, var: TypeVar) -> Vec<SelectId> {
        self.pending_by_effect
            .get(&var)
            .cloned()
            .unwrap_or_default()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// 1つの `SelectId` use-site に対応する推論メタデータ。
///
/// `method_value` は、selection lowering が作った method 関数 slot。
/// `receiver_value` は dot selection の subject で、typeclass method 解決時の role demand に使う。
/// `receiver_effect` は receiver 式の評価 effect で、effect method 探索に使う。
pub struct SelectionUse {
    pub parent: DefId,
    pub method_value: TypeVar,
    pub selected_value: TypeVar,
    pub receiver_value: TypeVar,
    pub receiver_effect: TypeVar,
    pub local_method_scope: Option<ModuleId>,
    pub recursive_self_value: Option<TypeVar>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// 解決済み selection の hover/definition 用メタデータ。
///
/// `SelectionUse` 本体は未解決 selection queue から取り除かれるため、source 表示に
/// 必要な type slots だけを別 table に残す。
pub struct ResolvedSelectionUse {
    pub parent: DefId,
    pub method_value: TypeVar,
    pub selected_value: TypeVar,
    pub receiver_value: TypeVar,
    pub receiver_effect: TypeVar,
}

impl From<SelectionUse> for ResolvedSelectionUse {
    fn from(use_site: SelectionUse) -> Self {
        Self {
            parent: use_site.parent,
            method_value: use_site.method_value,
            selected_value: use_site.selected_value,
            receiver_value: use_site.receiver_value,
            receiver_effect: use_site.receiver_effect,
        }
    }
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
            source_span: None,
        };

        table.insert(reference, use_site);

        assert_eq!(table.parent(reference), Some(DefId(1)));
        assert_eq!(table.value(reference), Some(TypeVar(2)));
    }

    #[test]
    fn local_def_use_records_type_slot_and_source_span() {
        let mut table = LocalDefUseTable::new();
        let def = DefId(3);
        let source_span = SourceSpan {
            file: sources::Path::default(),
            range: sources::SourceRange { start: 1, end: 4 },
        };

        table.insert(
            def,
            LocalDefUse {
                value: TypeVar(8),
                source_span: Some(source_span.clone()),
                role: LocalDefRole::Value,
            },
        );

        assert_eq!(table.get(def).unwrap().value, TypeVar(8));
        assert_eq!(table.get(def).unwrap().role, LocalDefRole::Value);
        assert_eq!(
            table.source_spans().collect::<Vec<_>>(),
            vec![(def, &source_span)]
        );
    }

    #[test]
    fn selection_use_keeps_unresolved_slots_and_watch_sets() {
        let mut table = SelectionUseTable::new();
        let select = SelectId(0);
        table.insert(
            select,
            SelectionUse {
                parent: DefId(1),
                method_value: TypeVar(4),
                selected_value: TypeVar(5),
                receiver_value: TypeVar(2),
                receiver_effect: TypeVar(3),
                local_method_scope: None,
                recursive_self_value: None,
            },
        );
        table.watch_receiver(TypeVar(2), select);
        table.watch_ref_payload(TypeVar(4), select);
        table.watch_ref_payload(TypeVar(4), select);
        table.watch_effect(TypeVar(3), select);
        table.watch_effect(TypeVar(3), select);

        assert_eq!(table.pending_for_lower_bound(TypeVar(2)), vec![select]);
        assert_eq!(table.pending_for_lower_bound(TypeVar(4)), vec![select]);
        assert_eq!(table.pending_for_lower_bound(TypeVar(3)), vec![select]);
        assert_eq!(table.pending_for_effect_fact(TypeVar(3)), vec![select]);
        assert_eq!(table.get(select).unwrap().method_value, TypeVar(4));
        assert_eq!(table.get(select).unwrap().receiver_value, TypeVar(2));
        assert_eq!(table.remove(select).unwrap().parent, DefId(1));
        assert!(table.get(select).is_none());
    }

    #[test]
    fn selection_source_span_survives_resolution_removal() {
        let mut table = SelectionUseTable::new();
        let select = SelectId(0);
        let source_span = SourceSpan {
            file: sources::Path::default(),
            range: sources::SourceRange { start: 2, end: 5 },
        };
        table.insert(
            select,
            SelectionUse {
                parent: DefId(1),
                method_value: TypeVar(4),
                selected_value: TypeVar(5),
                receiver_value: TypeVar(2),
                receiver_effect: TypeVar(3),
                local_method_scope: None,
                recursive_self_value: None,
            },
        );
        table.insert_source_span(select, source_span.clone());

        table.remove(select);

        assert!(table.get(select).is_none());
        assert_eq!(table.source_span(select), Some(&source_span));
    }

    #[test]
    fn resolved_selection_metadata_survives_resolution_removal() {
        let mut table = SelectionUseTable::new();
        let select = SelectId(0);
        let use_site = SelectionUse {
            parent: DefId(1),
            method_value: TypeVar(4),
            selected_value: TypeVar(5),
            receiver_value: TypeVar(2),
            receiver_effect: TypeVar(3),
            local_method_scope: None,
            recursive_self_value: None,
        };
        table.insert(select, use_site);

        let removed = table.remove(select).unwrap();
        table.insert_resolved(select, removed.into());

        assert!(table.get(select).is_none());
        assert_eq!(table.resolved(select).unwrap().selected_value, TypeVar(5));
    }
}
