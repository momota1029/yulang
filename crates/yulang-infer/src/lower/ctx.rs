use std::collections::{HashMap, HashSet};

use crate::ids::{DefId, RefId, TypeVar, fresh_def_id, fresh_ref_id, fresh_type_var};
use crate::lower::builtin_types::canonical_builtin_type_path;
use crate::ref_table::RefTable;
use crate::symbols::{ModuleId, ModuleTable, Name, OperatorFixity, Path, Visibility};

// ── LowerCtx ─────────────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedType {
    pub def: DefId,
    pub canonical_path: Path,
}

/// lowering ワンパスで使うスコープ・名前解決の文脈。
/// 制約生成はこれを包む上位クレートで行う。
pub struct LowerCtx {
    pub modules: ModuleTable,
    pub refs: RefTable,
    canonical_value_paths: HashMap<DefId, Path>,
    canonical_type_paths: HashMap<DefId, Path>,
    operator_defs: HashSet<DefId>,
    operator_fixities: HashMap<DefId, OperatorFixity>,

    /// ローカルスコープのスタック（値名前空間のみ）。
    /// push_local / pop_local でフレームを管理する。
    locals: Vec<HashMap<Name, DefId>>,
    /// `$x` 読み取り専用の `&x -> synthetic act` alias。
    var_ref_aliases: Vec<HashMap<Name, Name>>,
    /// 特定のローカル値のフィールド参照を既知 helper path へ束縛する。
    field_aliases: Vec<HashMap<(DefId, Name), Path>>,
    /// 現在 lowering 中のモジュール。
    pub current_module: ModuleId,

    /// `use` インポートの検索順（先頭が優先）。
    use_search: Vec<ModuleId>,
    use_paths: Vec<Path>,
}

impl LowerCtx {
    pub fn new() -> Self {
        let mut modules = ModuleTable::default();
        let root = modules.new_module();
        Self {
            modules,
            refs: RefTable::default(),
            canonical_value_paths: HashMap::new(),
            canonical_type_paths: HashMap::new(),
            operator_defs: HashSet::new(),
            operator_fixities: HashMap::new(),
            // ルートレベルのベースフレーム。
            // module-level `my` は module private として modules 側へ積む。
            locals: vec![HashMap::new()],
            var_ref_aliases: vec![HashMap::new()],
            field_aliases: vec![HashMap::new()],
            current_module: root,
            use_search: vec![],
            use_paths: vec![],
        }
    }

    // ── ID 発行 ──────────────────────────────────────────────────────────────

    pub fn fresh_def(&self) -> DefId {
        fresh_def_id()
    }

    pub fn fresh_ref(&self) -> RefId {
        fresh_ref_id()
    }

    pub fn fresh_tv(&self) -> TypeVar {
        fresh_type_var()
    }

    pub fn collect_binding_paths(&self) -> Vec<(Path, DefId)> {
        let mut out = Vec::new();

        if let Some(root_locals) = self.locals.first() {
            let mut locals = root_locals.iter().collect::<Vec<_>>();
            locals.sort_by(|(lhs_name, lhs_def), (rhs_name, rhs_def)| {
                lhs_name
                    .0
                    .cmp(&rhs_name.0)
                    .then_with(|| lhs_def.0.cmp(&rhs_def.0))
            });
            for (name, &def) in locals {
                out.push((
                    Path {
                        segments: vec![name.clone()],
                    },
                    def,
                ));
            }
        }

        self.collect_module_binding_paths(ModuleId(0), Vec::new(), &mut out);
        sort_binding_paths(&mut out);
        out
    }

    pub fn collect_all_binding_paths(&self) -> Vec<(Path, DefId)> {
        let mut out = Vec::new();

        if let Some(root_locals) = self.locals.first() {
            for (name, &def) in root_locals {
                out.push((
                    Path {
                        segments: vec![name.clone()],
                    },
                    def,
                ));
            }
        }

        for module_id in self.modules.module_ids() {
            if self.modules.node(module_id).parent.is_none() {
                self.collect_module_binding_paths(module_id, Vec::new(), &mut out);
            }
        }

        out.sort_by(|(lhs_path, lhs_def), (rhs_path, rhs_def)| {
            let lhs_key = lhs_path
                .segments
                .iter()
                .map(|name| name.0.as_str())
                .collect::<Vec<_>>();
            let rhs_key = rhs_path
                .segments
                .iter()
                .map(|name| name.0.as_str())
                .collect::<Vec<_>>();
            lhs_key
                .cmp(&rhs_key)
                .then_with(|| lhs_def.0.cmp(&rhs_def.0))
        });
        out.dedup_by(|(lhs_path, lhs_def), (rhs_path, rhs_def)| {
            lhs_def == rhs_def && lhs_path.segments == rhs_path.segments
        });
        out
    }

    pub fn collect_all_type_paths(&self) -> Vec<(Path, DefId)> {
        let mut out = Vec::new();

        for module_id in self.modules.module_ids() {
            if self.modules.node(module_id).parent.is_none() {
                self.collect_module_type_paths(module_id, Vec::new(), &mut out);
            }
        }

        out.sort_by(|(lhs_path, lhs_def), (rhs_path, rhs_def)| {
            let lhs_key = lhs_path
                .segments
                .iter()
                .map(|name| name.0.as_str())
                .collect::<Vec<_>>();
            let rhs_key = rhs_path
                .segments
                .iter()
                .map(|name| name.0.as_str())
                .collect::<Vec<_>>();
            lhs_key
                .cmp(&rhs_key)
                .then_with(|| lhs_def.0.cmp(&rhs_def.0))
        });
        out.dedup_by(|(lhs_path, lhs_def), (rhs_path, rhs_def)| {
            lhs_def == rhs_def && lhs_path.segments == rhs_path.segments
        });
        out
    }

    pub fn canonical_value_paths(&self) -> HashMap<DefId, Path> {
        self.canonical_value_paths.clone()
    }

    pub fn record_canonical_value_path(&mut self, def: DefId, path: Path) {
        self.canonical_value_paths.entry(def).or_insert(path);
    }

    pub fn is_canonical_value_path(&self, def: DefId, path: &Path) -> bool {
        self.canonical_value_paths
            .get(&def)
            .is_some_and(|canonical| canonical == path)
    }

    pub fn canonical_type_path_for_def(&self, def: DefId) -> Option<Path> {
        self.canonical_type_paths.get(&def).cloned().or_else(|| {
            self.collect_all_type_paths()
                .into_iter()
                .find_map(|(path, current)| (current == def).then_some(path))
        })
    }

    pub fn record_canonical_type_path(&mut self, def: DefId, path: Path) {
        self.canonical_type_paths.entry(def).or_insert(path);
    }

    pub fn is_canonical_type_path(&self, def: DefId, path: &Path) -> bool {
        self.canonical_type_paths
            .get(&def)
            .is_some_and(|canonical| canonical == path)
    }

    pub fn collect_observable_binding_paths(&self) -> Vec<(Path, DefId)> {
        self.collect_binding_paths()
            .into_iter()
            .filter(|(path, _)| is_observable_binding_path(path))
            .collect()
    }

    pub fn collect_exported_binding_paths(&self) -> Vec<(Path, DefId)> {
        let mut out = Vec::new();
        for module_id in self.modules.module_ids() {
            if self.modules.node(module_id).parent.is_none() {
                self.collect_module_exported_binding_paths(module_id, Vec::new(), &mut out);
            }
        }
        sort_binding_paths(&mut out);
        out
    }

    pub fn module_path(&self, module: ModuleId) -> Path {
        let mut segments = Vec::new();
        let mut current = module;
        while let Some(parent) = self.modules.node(current).parent {
            let name = self
                .modules
                .node(parent)
                .modules
                .iter()
                .find_map(|(name, &child)| (child == current).then_some(name.clone()));
            let Some(name) = name else {
                break;
            };
            segments.push(name);
            current = parent;
        }
        segments.reverse();
        Path { segments }
    }

    pub fn current_module_path(&self) -> Path {
        self.module_path(self.current_module)
    }

    // ── ローカルスコープ ──────────────────────────────────────────────────────

    /// 新しいスコープフレームを開く（lambda・let の body に入るとき）。
    pub fn push_local(&mut self) {
        self.locals.push(HashMap::new());
        self.var_ref_aliases.push(HashMap::new());
        self.field_aliases.push(HashMap::new());
    }

    /// 直前の push_local に対応するフレームを閉じる。
    pub fn pop_local(&mut self) {
        self.locals.pop();
        self.var_ref_aliases.pop();
        self.field_aliases.pop();
    }

    /// 直前の push_local に対応する値名前空間フレームを取り出して閉じる。
    pub fn pop_local_frame(&mut self) -> HashMap<Name, DefId> {
        self.var_ref_aliases.pop();
        self.field_aliases.pop();
        self.locals.pop().unwrap_or_default()
    }

    /// 現在のフレームにローカル束縛を追加する。
    pub fn bind_local(&mut self, name: Name, def: DefId) {
        if let Some(frame) = self.locals.last_mut() {
            frame.insert(name, def);
        }
    }

    pub fn bind_local_operator(&mut self, name: Name, fixity: OperatorFixity, def: DefId) {
        self.mark_operator_def(def, fixity);
        self.bind_local(name, def);
    }

    pub fn local_depth(&self) -> usize {
        self.locals.len()
    }

    pub fn bind_var_ref_alias(&mut self, name: Name, act_name: Name) {
        if let Some(frame) = self.var_ref_aliases.last_mut() {
            frame.insert(name, act_name);
        }
    }

    pub fn resolve_var_ref_alias(&self, name: &Name) -> Option<Name> {
        for frame in self.var_ref_aliases.iter().rev() {
            if let Some(act_name) = frame.get(name) {
                return Some(act_name.clone());
            }
        }
        None
    }

    pub fn bind_field_alias(&mut self, def: DefId, field: Name, path: Path) {
        if let Some(frame) = self.field_aliases.last_mut() {
            frame.insert((def, field), path);
        }
    }

    pub fn resolve_field_alias(&self, def: DefId, field: &Name) -> Option<Path> {
        for frame in self.field_aliases.iter().rev() {
            if let Some(path) = frame.get(&(def, field.clone())) {
                return Some(path.clone());
            }
        }
        None
    }

    // ── モジュール操作 ────────────────────────────────────────────────────────

    /// 子モジュールを作って current_module に登録し、そこへ移動する。
    /// 戻り値は「元の current_module」なので呼び出し側で保存して戻すこと。
    pub fn enter_module(&mut self, name: Name) -> ModuleId {
        let child = self.modules.new_module();
        self.modules.insert_module(self.current_module, name, child);
        let parent = self.current_module;
        self.current_module = child;
        parent
    }

    pub fn leave_module(&mut self, saved: ModuleId) {
        self.current_module = saved;
    }

    pub fn enter_module_path(&mut self, path: &Path) -> (ModuleId, Vec<ModuleId>, Vec<Path>) {
        let saved_module = self.current_module;
        let saved_use_search = std::mem::take(&mut self.use_search);
        let saved_use_paths = std::mem::take(&mut self.use_paths);
        self.current_module = ModuleId(0);
        for segment in &path.segments {
            let next = if let Some(&existing) =
                self.modules.node(self.current_module).modules.get(segment)
            {
                existing
            } else {
                let created = self.modules.new_module();
                self.modules
                    .insert_module(self.current_module, segment.clone(), created);
                created
            };
            self.current_module = next;
        }
        (saved_module, saved_use_search, saved_use_paths)
    }

    pub fn leave_module_path(&mut self, saved: (ModuleId, Vec<ModuleId>, Vec<Path>)) {
        self.current_module = saved.0;
        self.use_search = saved.1;
        self.use_paths = saved.2;
    }

    /// `use path` を現在のスコープに追加する。
    /// path が指す ModuleId を解決して use_search に積む。
    pub fn add_use(&mut self, path: &Path) -> Option<()> {
        self.use_paths.push(path.clone());
        let module_id = self.resolve_module_path(path)?;
        self.use_search.push(module_id);
        Some(())
    }

    pub fn current_use_paths(&self) -> Vec<Path> {
        self.use_paths.clone()
    }

    // ── 名前解決 ─────────────────────────────────────────────────────────────

    /// 単純名を値名前空間で解決する。
    /// 優先順: ローカル（インナー優先）→ 現在モジュール → use インポート順
    pub fn resolve_value(&self, name: &Name) -> Option<DefId> {
        self.resolve_value_candidates_from(self.current_module, name)
            .into_iter()
            .next()
    }

    pub fn resolve_operator_value(&self, name: &Name, fixity: OperatorFixity) -> Option<DefId> {
        self.resolve_operator_value_candidates_from(self.current_module, name, fixity)
            .into_iter()
            .next()
    }

    pub fn resolve_value_candidates(&self, name: &Name) -> Vec<DefId> {
        self.resolve_value_candidates_from(self.current_module, name)
    }

    pub fn resolve_operator_value_candidates(
        &self,
        name: &Name,
        fixity: OperatorFixity,
    ) -> Vec<DefId> {
        self.resolve_operator_value_candidates_from(self.current_module, name, fixity)
    }

    /// ローカルスコープだけで単純名を解決する。
    pub fn resolve_local_value(&self, name: &Name) -> Option<DefId> {
        for frame in self.locals.iter().rev() {
            if let Some(&def) = frame.get(name) {
                return Some(def);
            }
        }
        None
    }

    /// ローカルスコープだけで operator を解決する。
    pub fn resolve_local_operator_value(
        &self,
        name: &Name,
        fixity: OperatorFixity,
    ) -> Option<DefId> {
        for frame in self.locals.iter().rev() {
            if let Some(&def) = frame.get(name)
                && self.operator_fixity(def) == Some(fixity)
            {
                return Some(def);
            }
        }
        None
    }

    /// let/パターン束縛の接続用に、ローカルと現在モジュールの lexical chain だけを見る。
    pub fn resolve_bound_value(&self, name: &Name) -> Option<DefId> {
        if let Some(def) = self.resolve_local_value(name) {
            return Some(def);
        }
        let mut current = Some(self.current_module);
        while let Some(mid) = current {
            if let Some(&def) = self.modules.node(mid).values.get(name) {
                if is_accessible_from(
                    self.current_module,
                    mid,
                    self.modules.value_visibility(mid, name),
                ) {
                    return Some(def);
                }
            }
            current = self.modules.node(mid).parent;
        }
        None
    }

    pub fn resolve_value_from(&self, module: ModuleId, name: &Name) -> Option<DefId> {
        self.resolve_value_candidates_from(module, name)
            .into_iter()
            .next()
    }

    pub fn resolve_operator_value_from(
        &self,
        module: ModuleId,
        name: &Name,
        fixity: OperatorFixity,
    ) -> Option<DefId> {
        self.resolve_operator_value_candidates_from(module, name, fixity)
            .into_iter()
            .next()
    }

    pub fn resolve_value_candidates_from(&self, module: ModuleId, name: &Name) -> Vec<DefId> {
        let mut out = Vec::new();

        for frame in self.locals.iter().rev() {
            if let Some(&def) = frame.get(name) {
                push_unique(&mut out, def);
            }
        }

        for mid in lexical_modules(&self.modules, module) {
            if let Some(&def) = self.modules.node(mid).values.get(name) {
                if is_accessible_from(module, mid, self.modules.value_visibility(mid, name)) {
                    push_unique(&mut out, def);
                }
            }
        }

        for &mid in &self.use_search {
            if let Some(&def) = self.modules.node(mid).values.get(name) {
                if is_accessible_from(module, mid, self.modules.value_visibility(mid, name)) {
                    push_unique(&mut out, def);
                }
            }
        }

        out
    }

    pub fn resolve_operator_value_candidates_from(
        &self,
        module: ModuleId,
        name: &Name,
        fixity: OperatorFixity,
    ) -> Vec<DefId> {
        let mut out = Vec::new();

        for frame in self.locals.iter().rev() {
            if let Some(&def) = frame.get(name) {
                if self.operator_fixity(def) == Some(fixity) {
                    push_unique(&mut out, def);
                }
            }
        }

        for mid in lexical_modules(&self.modules, module) {
            if let Some(&def) = self
                .modules
                .node(mid)
                .operator_values
                .get(&(name.clone(), fixity))
            {
                if is_accessible_from(
                    module,
                    mid,
                    self.modules.operator_visibility(mid, name, fixity),
                ) {
                    push_unique(&mut out, def);
                }
            }
        }

        for &mid in &self.use_search {
            if let Some(&def) = self
                .modules
                .node(mid)
                .operator_values
                .get(&(name.clone(), fixity))
            {
                if is_accessible_from(
                    module,
                    mid,
                    self.modules.operator_visibility(mid, name, fixity),
                ) {
                    push_unique(&mut out, def);
                }
            }
        }

        out
    }

    /// 単純名を型名前空間で解決する。
    /// ローカルスコープは値専用なので、モジュール → use の順。
    pub fn resolve_type(&self, name: &Name) -> Option<DefId> {
        self.resolve_type_candidates_from(self.current_module, name)
            .into_iter()
            .next()
    }

    pub fn resolve_type_from(&self, module: ModuleId, name: &Name) -> Option<DefId> {
        self.resolve_type_candidates_from(module, name)
            .into_iter()
            .next()
    }

    pub fn resolve_type_candidates(&self, name: &Name) -> Vec<DefId> {
        self.resolve_type_candidates_from(self.current_module, name)
    }

    pub fn resolve_type_candidates_from(&self, module: ModuleId, name: &Name) -> Vec<DefId> {
        let mut out = Vec::new();
        for mid in lexical_modules(&self.modules, module) {
            if let Some(&def) = self.modules.node(mid).types.get(name) {
                if is_accessible_from(module, mid, self.modules.type_visibility(mid, name)) {
                    push_unique(&mut out, def);
                }
            }
        }
        for &mid in &self.use_search {
            if let Some(&def) = self.modules.node(mid).types.get(name) {
                if is_accessible_from(module, mid, self.modules.type_visibility(mid, name)) {
                    push_unique(&mut out, def);
                }
            }
        }
        out
    }

    /// 修飾パス（`a::b::c`）を値名前空間で解決する。
    /// 最初のセグメントはモジュール名前空間で引く。
    /// `a` はローカルが勝たず常にモジュールとして探す。
    pub fn resolve_path_value(&self, path: &Path) -> Option<DefId> {
        self.resolve_path_value_candidates_from(self.current_module, path)
            .into_iter()
            .next()
    }

    pub fn resolve_path_value_from(&self, module: ModuleId, path: &Path) -> Option<DefId> {
        self.resolve_path_value_candidates_from(module, path)
            .into_iter()
            .next()
    }

    pub fn resolve_path_value_candidates(&self, path: &Path) -> Vec<DefId> {
        self.resolve_path_value_candidates_from(self.current_module, path)
    }

    pub fn resolve_path_value_candidates_from(&self, module: ModuleId, path: &Path) -> Vec<DefId> {
        let Some((last, module_segs)) = path.segments.split_last() else {
            return Vec::new();
        };
        if module_segs.is_empty() {
            return self.resolve_value_candidates_from(module, last);
        }
        let module_path = Path {
            segments: module_segs.to_vec(),
        };
        let mut out = Vec::new();
        for mid in self.resolve_module_path_candidates_from(module, &module_path) {
            if let Some(&def) = self.modules.node(mid).values.get(last) {
                if is_accessible_from(module, mid, self.modules.value_visibility(mid, last)) {
                    push_unique(&mut out, def);
                }
            }
        }
        out
    }

    pub fn mark_operator_def(&mut self, def: DefId, fixity: OperatorFixity) {
        self.operator_defs.insert(def);
        self.operator_fixities.insert(def, fixity);
    }

    pub fn is_operator_def(&self, def: DefId) -> bool {
        self.operator_defs.contains(&def)
    }

    pub fn operator_fixity(&self, def: DefId) -> Option<OperatorFixity> {
        self.operator_fixities.get(&def).copied()
    }

    /// 修飾パスを型名前空間で解決する。
    pub fn resolve_path_type(&self, path: &Path) -> Option<DefId> {
        self.resolve_path_type_candidates_from(self.current_module, path)
            .into_iter()
            .next()
    }

    pub fn resolve_type_path_in(&self, module: ModuleId, path: &Path) -> Option<ResolvedType> {
        if let Some(def) = self.resolve_path_type_from(module, path) {
            let canonical_path = self
                .canonical_type_path_for_def(def)
                .unwrap_or_else(|| path.clone());
            return Some(ResolvedType {
                def,
                canonical_path,
            });
        }

        let canonical_path = canonical_builtin_type_path(path)?;
        let def = self.resolve_path_type_from(module, &canonical_path)?;
        Some(ResolvedType {
            def,
            canonical_path,
        })
    }

    pub fn resolve_current_type_path(&self, path: &Path) -> Option<ResolvedType> {
        self.resolve_type_path_in(self.current_module, path)
    }

    pub fn canonical_type_path_in(&self, module: ModuleId, path: &Path) -> Path {
        self.resolve_type_path_in(module, path)
            .map(|resolved| resolved.canonical_path)
            .or_else(|| canonical_builtin_type_path(path))
            .unwrap_or_else(|| path.clone())
    }

    pub fn canonical_current_type_path(&self, path: &Path) -> Path {
        self.canonical_type_path_in(self.current_module, path)
    }

    pub fn resolve_path_type_from(&self, module: ModuleId, path: &Path) -> Option<DefId> {
        self.resolve_path_type_candidates_from(module, path)
            .into_iter()
            .next()
    }

    pub fn resolve_path_type_candidates(&self, path: &Path) -> Vec<DefId> {
        self.resolve_path_type_candidates_from(self.current_module, path)
    }

    pub fn resolve_path_type_candidates_from(&self, module: ModuleId, path: &Path) -> Vec<DefId> {
        let Some((last, module_segs)) = path.segments.split_last() else {
            return Vec::new();
        };
        if module_segs.is_empty() {
            return self.resolve_type_candidates_from(module, last);
        }
        let module_path = Path {
            segments: module_segs.to_vec(),
        };
        let mut out = Vec::new();
        for mid in self.resolve_module_path_candidates_from(module, &module_path) {
            if let Some(&def) = self.modules.node(mid).types.get(last) {
                if is_accessible_from(module, mid, self.modules.type_visibility(mid, last)) {
                    push_unique(&mut out, def);
                }
            }
        }
        out
    }

    /// パスをモジュールとして解決する。
    /// 最初のセグメントは現在モジュール → use_search の順で探す。
    pub fn resolve_module_path(&self, path: &Path) -> Option<ModuleId> {
        self.resolve_module_path_candidates_from(self.current_module, path)
            .into_iter()
            .next()
    }

    pub fn resolve_module_path_from(&self, module: ModuleId, path: &Path) -> Option<ModuleId> {
        self.resolve_module_path_candidates_from(module, path)
            .into_iter()
            .next()
    }

    pub fn resolve_module_path_candidates(&self, path: &Path) -> Vec<ModuleId> {
        self.resolve_module_path_candidates_from(self.current_module, path)
    }

    pub fn resolve_module_path_candidates_from(
        &self,
        module: ModuleId,
        path: &Path,
    ) -> Vec<ModuleId> {
        let mut current = vec![module];
        for (i, seg) in path.segments.iter().enumerate() {
            let mut next = Vec::new();
            if i == 0 {
                for candidate in find_module_candidates_by_name_from(
                    &self.modules,
                    &self.use_search,
                    module,
                    seg,
                ) {
                    push_unique(&mut next, candidate);
                }
            } else {
                for mid in current {
                    if let Some(&child) = self.modules.node(mid).modules.get(seg) {
                        if is_accessible_from(module, mid, self.modules.module_visibility(mid, seg))
                        {
                            push_unique(&mut next, child);
                        }
                    }
                }
            }
            if next.is_empty() {
                return Vec::new();
            }
            current = next;
        }
        current
    }

    fn collect_module_binding_paths(
        &self,
        module_id: ModuleId,
        prefix: Vec<Name>,
        out: &mut Vec<(Path, DefId)>,
    ) {
        let node = self.modules.node(module_id);

        let mut values = node.values.iter().collect::<Vec<_>>();
        values.sort_by(|(lhs_name, lhs_def), (rhs_name, rhs_def)| {
            lhs_name
                .0
                .cmp(&rhs_name.0)
                .then_with(|| lhs_def.0.cmp(&rhs_def.0))
        });
        for (name, &def) in values {
            let mut path = prefix.clone();
            path.push(name.clone());
            out.push((Path { segments: path }, def));
        }

        let mut operators = node.operator_values.iter().collect::<Vec<_>>();
        operators.sort_by(
            |((lhs_name, lhs_fixity), lhs_def), ((rhs_name, rhs_fixity), rhs_def)| {
                lhs_name
                    .0
                    .cmp(&rhs_name.0)
                    .then_with(|| {
                        operator_fixity_sort_key(*lhs_fixity)
                            .cmp(&operator_fixity_sort_key(*rhs_fixity))
                    })
                    .then_with(|| lhs_def.0.cmp(&rhs_def.0))
            },
        );
        for ((name, fixity), &def) in operators {
            let mut path = prefix.clone();
            path.push(operator_binding_name(name, *fixity));
            out.push((Path { segments: path }, def));
        }

        let mut modules = node.modules.iter().collect::<Vec<_>>();
        modules.sort_by(|(lhs_name, lhs_child), (rhs_name, rhs_child)| {
            lhs_name
                .0
                .cmp(&rhs_name.0)
                .then_with(|| lhs_child.0.cmp(&rhs_child.0))
        });
        for (name, &child) in modules {
            let mut child_prefix = prefix.clone();
            child_prefix.push(name.clone());
            self.collect_module_binding_paths(child, child_prefix, out);
        }
    }

    fn collect_module_exported_binding_paths(
        &self,
        module_id: ModuleId,
        prefix: Vec<Name>,
        out: &mut Vec<(Path, DefId)>,
    ) {
        let node = self.modules.node(module_id);

        let mut values = node.values.iter().collect::<Vec<_>>();
        values.sort_by(|(lhs_name, lhs_def), (rhs_name, rhs_def)| {
            lhs_name
                .0
                .cmp(&rhs_name.0)
                .then_with(|| lhs_def.0.cmp(&rhs_def.0))
        });
        for (name, &def) in values {
            if self.modules.value_visibility(module_id, name) == Visibility::My {
                continue;
            }
            let mut path = prefix.clone();
            path.push(name.clone());
            let path = Path { segments: path };
            if is_observable_binding_path(&path) {
                out.push((path, def));
            }
        }

        let mut operators = node.operator_values.iter().collect::<Vec<_>>();
        operators.sort_by(
            |((lhs_name, lhs_fixity), lhs_def), ((rhs_name, rhs_fixity), rhs_def)| {
                lhs_name
                    .0
                    .cmp(&rhs_name.0)
                    .then_with(|| {
                        operator_fixity_sort_key(*lhs_fixity)
                            .cmp(&operator_fixity_sort_key(*rhs_fixity))
                    })
                    .then_with(|| lhs_def.0.cmp(&rhs_def.0))
            },
        );
        for ((name, fixity), &def) in operators {
            if self.modules.operator_visibility(module_id, name, *fixity) == Visibility::My {
                continue;
            }
            let mut path = prefix.clone();
            path.push(operator_binding_name(name, *fixity));
            let path = Path { segments: path };
            if is_observable_binding_path(&path) {
                out.push((path, def));
            }
        }

        let mut modules = node.modules.iter().collect::<Vec<_>>();
        modules.sort_by(|(lhs_name, lhs_child), (rhs_name, rhs_child)| {
            lhs_name
                .0
                .cmp(&rhs_name.0)
                .then_with(|| lhs_child.0.cmp(&rhs_child.0))
        });
        for (name, &child) in modules {
            let mut child_prefix = prefix.clone();
            child_prefix.push(name.clone());
            self.collect_module_exported_binding_paths(child, child_prefix, out);
        }
    }

    fn collect_module_type_paths(
        &self,
        module_id: ModuleId,
        prefix: Vec<Name>,
        out: &mut Vec<(Path, DefId)>,
    ) {
        let node = self.modules.node(module_id);

        let mut types = node.types.iter().collect::<Vec<_>>();
        types.sort_by(|(lhs_name, lhs_def), (rhs_name, rhs_def)| {
            lhs_name
                .0
                .cmp(&rhs_name.0)
                .then_with(|| lhs_def.0.cmp(&rhs_def.0))
        });
        for (name, &def) in types {
            let mut path = prefix.clone();
            path.push(name.clone());
            out.push((Path { segments: path }, def));
        }

        let mut modules = node.modules.iter().collect::<Vec<_>>();
        modules.sort_by(|(lhs_name, lhs_child), (rhs_name, rhs_child)| {
            lhs_name
                .0
                .cmp(&rhs_name.0)
                .then_with(|| lhs_child.0.cmp(&rhs_child.0))
        });
        for (name, &child) in modules {
            let mut child_prefix = prefix.clone();
            child_prefix.push(name.clone());
            self.collect_module_type_paths(child, child_prefix, out);
        }
    }

    pub fn resolve_pending_refs(&mut self) {
        let modules = &self.modules;
        self.refs.resolve_pending(|unresolved| {
            let use_search =
                resolve_use_paths_from_modules(modules, unresolved.module, &unresolved.use_paths);
            resolve_value_path_candidates_from_modules(
                modules,
                &use_search,
                unresolved.module,
                &unresolved.path,
            )
            .into_iter()
            .next()
        });
    }
}

fn resolve_use_paths_from_modules(
    modules: &ModuleTable,
    module: ModuleId,
    paths: &[Path],
) -> Vec<ModuleId> {
    let mut out = Vec::new();
    for path in paths {
        for mid in resolve_module_path_candidates_from_modules(modules, &[], module, path) {
            push_unique(&mut out, mid);
        }
    }
    out
}

fn lexical_modules(modules: &ModuleTable, module: ModuleId) -> Vec<ModuleId> {
    let mut out = Vec::new();
    let mut current = Some(module);
    while let Some(mid) = current {
        out.push(mid);
        current = modules.node(mid).parent;
    }
    out
}

fn is_accessible_from(requester: ModuleId, owner: ModuleId, visibility: Visibility) -> bool {
    match visibility {
        Visibility::My => requester == owner,
        Visibility::Our | Visibility::Pub => true,
    }
}

fn find_module_candidates_by_name_from(
    modules: &ModuleTable,
    use_search: &[ModuleId],
    module: ModuleId,
    name: &Name,
) -> Vec<ModuleId> {
    let mut out = Vec::new();

    for mid in lexical_modules(modules, module) {
        if let Some(&child) = modules.node(mid).modules.get(name) {
            if is_accessible_from(module, mid, modules.module_visibility(mid, name)) {
                push_unique(&mut out, child);
            }
        }
    }

    for &search_mid in use_search {
        if let Some(&mid) = modules.node(search_mid).modules.get(name) {
            if is_accessible_from(
                module,
                search_mid,
                modules.module_visibility(search_mid, name),
            ) {
                push_unique(&mut out, mid);
            }
        }
    }

    if module != ModuleId(0) {
        if let Some(&mid) = modules.node(ModuleId(0)).modules.get(name) {
            if is_accessible_from(
                module,
                ModuleId(0),
                modules.module_visibility(ModuleId(0), name),
            ) {
                push_unique(&mut out, mid);
            }
        }
    }

    out
}

fn resolve_module_path_candidates_from_modules(
    modules: &ModuleTable,
    use_search: &[ModuleId],
    module: ModuleId,
    path: &Path,
) -> Vec<ModuleId> {
    let mut current = vec![module];
    for (i, seg) in path.segments.iter().enumerate() {
        let mut next = Vec::new();
        if i == 0 {
            for candidate in find_module_candidates_by_name_from(modules, use_search, module, seg) {
                push_unique(&mut next, candidate);
            }
        } else {
            for mid in current {
                if let Some(&child) = modules.node(mid).modules.get(seg) {
                    if is_accessible_from(module, mid, modules.module_visibility(mid, seg)) {
                        push_unique(&mut next, child);
                    }
                }
            }
        }
        if next.is_empty() {
            return Vec::new();
        }
        current = next;
    }
    current
}

fn resolve_value_path_candidates_from_modules(
    modules: &ModuleTable,
    use_search: &[ModuleId],
    module: ModuleId,
    path: &Path,
) -> Vec<DefId> {
    let Some((last, module_segs)) = path.segments.split_last() else {
        return Vec::new();
    };

    if module_segs.is_empty() {
        let mut out = Vec::new();
        for mid in lexical_modules(modules, module) {
            if let Some(&def) = modules.node(mid).values.get(last) {
                if is_accessible_from(module, mid, modules.value_visibility(mid, last)) {
                    push_unique(&mut out, def);
                }
            }
        }
        for &mid in use_search {
            if let Some(&def) = modules.node(mid).values.get(last) {
                if is_accessible_from(module, mid, modules.value_visibility(mid, last)) {
                    push_unique(&mut out, def);
                }
            }
        }
        return out;
    }

    let module_path = Path {
        segments: module_segs.to_vec(),
    };
    let mut out = Vec::new();
    for mid in
        resolve_module_path_candidates_from_modules(modules, use_search, module, &module_path)
    {
        if let Some(&def) = modules.node(mid).values.get(last) {
            if is_accessible_from(module, mid, modules.value_visibility(mid, last)) {
                push_unique(&mut out, def);
            }
        }
    }
    out
}

fn push_unique<T: Copy + Eq>(out: &mut Vec<T>, item: T) {
    if !out.contains(&item) {
        out.push(item);
    }
}

fn is_observable_binding_path(path: &Path) -> bool {
    !path
        .segments
        .iter()
        .any(|name| name.0.starts_with('&') || name.0.starts_with('#'))
}

fn operator_binding_name(name: &Name, fixity: OperatorFixity) -> Name {
    Name(format!("#op:{}:{}", operator_fixity_tag(fixity), name.0))
}

fn operator_fixity_tag(fixity: OperatorFixity) -> &'static str {
    match fixity {
        OperatorFixity::Prefix => "prefix",
        OperatorFixity::Infix => "infix",
        OperatorFixity::Suffix => "suffix",
        OperatorFixity::Nullfix => "nullfix",
    }
}

fn operator_fixity_sort_key(fixity: OperatorFixity) -> u8 {
    match fixity {
        OperatorFixity::Prefix => 0,
        OperatorFixity::Infix => 1,
        OperatorFixity::Suffix => 2,
        OperatorFixity::Nullfix => 3,
    }
}

fn sort_binding_paths(paths: &mut Vec<(Path, DefId)>) {
    paths.sort_by(|(lhs_path, lhs_def), (rhs_path, rhs_def)| {
        binding_path_sort_key(lhs_path)
            .cmp(&binding_path_sort_key(rhs_path))
            .then_with(|| lhs_def.0.cmp(&rhs_def.0))
    });
    paths.dedup_by(|(lhs_path, lhs_def), (rhs_path, rhs_def)| {
        lhs_def == rhs_def && lhs_path.segments == rhs_path.segments
    });
}

fn binding_path_sort_key(path: &Path) -> Vec<&str> {
    path.segments.iter().map(|name| name.0.as_str()).collect()
}
