# yulang-infer コア engine: 潜在的なリファクタ候補

全体的な印象として、yulang-infer のコア engine は**段階的な成長に伴う層の蓄積**と**文脈に応じた複雑な決定木**の感覚が強い。特に以下が懸念:

1. **LowerState** が多数の責務を持つ巨大な構造体で、mutable な副作用が多くのメソッドから散在している。レベル管理(current_level)の操作と効果パス管理がシンプルなら簡潔だが、10個以上の HashMap/HashSet フィールドがあり、invariants が分散。
2. **match 式の粒度が細かい**型変換パスが多く、同じパターンが数回繰り返される。特に `cooccur.rs` と `format.rs` で正負の polarity を分岐させてほぼ同じロジックが重複。
3. **freeze.rs と simplify/compact.rs** が large `_with_non_generic`, `_owned_with_non_generic_and_extra_vars` のような overload 的な関数群を持つ。引数の微妙な差(owned vs ref, extra_vars の有無)で分岐し、内部で同じ処理をしている。
4. **DeferredSelection 機構**が複雑で、複数回のループと mutable borrow 依存が見える。

以下は最も嗅覚的に「もし直すなら」と思う8-12個のスポット:

---

## 1. LowerState: 責務の過度な集約とフィールド増殖

- **場所**: `crates/yulang-infer/src/lower/state.rs:1`
- **匂い**: 巨大な状態ホルダー，分散した invariants，複数責務の混在

```rust
pub struct LowerState {
    pub ctx: LowerCtx,
    pub infer: Infer,
    pub def_tvs: HashMap<DefId, TypeVar>,
    pub def_eff_tvs: HashMap<DefId, TypeVar>,
    pub current_level: u32,
    pub current_owner: Option<DefId>,
    pub current_lambda_owner: Option<DefId>,
    // ...以下30個以上のフィールド...
    pub effect_op_args: HashMap<DefId, Vec<EffectAtom>>,
    pub effect_op_effect_paths: HashMap<DefId, Path>,
    pub same_path_effect_ops: HashMap<DefId, DefId>,
    pub same_path_value_defs: HashMap<DefId, DefId>,
    pub same_path_value_defs_by_effect_op: HashMap<DefId, DefId>,
    pub act_templates: HashMap<DefId, TypedExpr>,
    pub current_act_effect_path: Option<Path>,
    pub do_replacement: Option<DoReplacement>,
    pub companion_modules: HashSet<ModuleId>,
    pub enum_variant_tags: HashMap<DefId, u32>,
    pub enum_variant_patterns: HashMap<DefId, usize>,
    // ...
}
```

**所感**: 3927行のこのファイル自体が、scope/level/owner の管理と effect_op 処理と act template と synthetic path 書き換えが全部ぐちゃぐちゃに詰まってる。コンテキスト部分、type-var キャッシュ、effect 関連、synthetic の書き換え、で分けた方がいいかもね。今のままだと「どの invariant がどこから見えるか」が曖昧になりやすい。

---

## 2. 正負の polarity 分岐が `display/format.rs` で繰り返される

- **場所**: `crates/yulang-infer/src/display/format.rs:121-168`
- **匂い**: ほぼ同じロジックが正負で複製，`(TypeVar, bool)` キーでの in_process 管理が2回ある

```rust
fn coalesce_var(&mut self, tv: TypeVar, positive: bool) -> Type {
    let key = (tv, positive);
    if let Some(rec_tv) = self.in_process_vars.get(&key) {
        self.recursive_var_hits.insert(key);
        return Type::Var(*rec_tv);
    }

    let Some(bounds) = self.scheme.rec_vars.get(&tv) else {
        return Type::Var(tv);
    };

    let rec_tv = fresh_type_var();
    self.in_process_vars.insert(key, rec_tv);
    let body = if positive {
        self.coalesce_type(&bounds.lower, true)
    } else {
        self.coalesce_type(&bounds.upper, false)
    };
    // ...
}

fn coalesce_type(&mut self, ty: &CompactType, positive: bool) -> Type {
    if should_hash_cons_type(ty) {
        let key = (compact_type_key(ty), positive);
        if let Some(rec_tv) = self.in_process_types.get(&key) {
            self.recursive_type_hits.insert(key.clone());
            return Type::Var(*rec_tv);
        }
        let rec_tv = fresh_type_var();
        self.in_process_types.insert(key.clone(), rec_tv);
        let body = self.coalesce_type_body(ty, positive);
        self.in_process_types.remove(&key);
        // ...
    }
}
```

**所感**: 同じ「in-process 履歴を持ちながら recursive hit を追跡」パターンが `_var` と `_type` で重複してる。両者を`Side<TypeVar>` みたいな enum に統一して shared helper を作ったら DRY になるかも。

---

## 3. freeze.rs の関数ファミリー: パラメータの微妙な差による overload

- **場所**: `crates/yulang-infer/src/scheme/freeze.rs:20-92`
- **匂い**: `_with_non_generic`, `_owned_with_non_generic`, `_owned_with_non_generic_and_extra_vars` のような関数チェーンが引数の差だけで分岐

```rust
pub fn freeze_type_var(infer: &Infer, root: TypeVar) -> FrozenScheme {
    freeze_type_var_with_non_generic(infer, root, &HashSet::new())
}

pub fn freeze_type_var_with_non_generic(
    infer: &Infer,
    root: TypeVar,
    non_generic_roots: &HashSet<TypeVar>,
) -> FrozenScheme {
    let compact = compact_type_var(infer, root);
    let scheme = coalesce_by_co_occurrence(&compact);
    freeze_compact_scheme_owned_with_non_generic(infer, scheme, non_generic_roots)
}

pub fn freeze_compact_scheme_with_non_generic(
    infer: &Infer,
    scheme: &CompactTypeScheme,
    non_generic_roots: &HashSet<TypeVar>,
) -> FrozenScheme {
    freeze_compact_scheme_owned_with_non_generic_and_extra_vars(
        infer,
        scheme.clone(),
        &[],
        non_generic_roots,
    )
}

pub(crate) fn freeze_compact_scheme_owned_with_non_generic(
    infer: &Infer,
    scheme: CompactTypeScheme,
    non_generic_roots: &HashSet<TypeVar>,
) -> FrozenScheme {
    freeze_compact_scheme_owned_with_non_generic_and_extra_vars(
        infer,
        scheme,
        &[],
        non_generic_roots,
    )
}
```

**所感**: 結局全部 `freeze_compact_scheme_owned_with_non_generic_and_extra_vars` に到達してるだけ。owned vs ref の微妙な使い分けが最初の few bytes だけで、内部は全部 owned に変換してる。中間の wrapper 層が無駄かもね。default の `extra_quantified: &[]` を optional にして、caller が直接心配事を指定する方がシンプルかも。

---

## 4. ctx.rs の resolution 関数：ローカル + モジュール lexical の繰り返し

- **場所**: `crates/yulang-infer/src/lower/ctx.rs:464-534`
- **匂い**: `resolve_value_from`, `resolve_operator_value_from`, `resolve_value_candidates_from` がほぼ同じパターンを3回ずつ実装

```rust
pub fn resolve_value_from(&self, module: ModuleId, name: &Name) -> Option<DefId> {
    for frame in self.locals.iter().rev() {
        if let Some(&def) = frame.get(name) {
            return Some(def);
        }
    }

    let mut current = Some(module);
    while let Some(mid) = current {
        if let Some(&def) = self.modules.node(mid).values.get(name) {
            if is_accessible_from(module, mid, self.modules.value_visibility(mid, name)) {
                return Some(def);
            }
        }
        current = self.modules.node(mid).parent;
    }

    for &mid in &self.use_search {
        if let Some(&def) = self.modules.node(mid).values.get(name) {
            if is_accessible_from(module, mid, self.modules.value_visibility(mid, name)) {
                return Some(def);
            }
        }
    }

    None
}

pub fn resolve_operator_value_from(
    &self,
    module: ModuleId,
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
    // ... ほぼ同じ処理: モジュール lexical, use_search ...
}
```

**所感**: Local -> Lexical -> Use の3フェーズが「値」と「operator」で重複してる。generic な `resolve_with<T>` を作って、pred と extract を caller が指定する方が保守的かも。

---

## 5. lower/role/impls.rs の長い Cast/Error 処理コード

- **場所**: `crates/yulang-infer/src/lower/role/impls.rs:40-150`
- **匂い**: 相似した cast と error-up impl lowering が各 200行以上で詳細が微妙に異なる

```rust
pub(crate) fn lower_cast_decl(state: &mut LowerState, node: &SyntaxNode) {
    let impl_def = state.fresh_def();
    let Some(pattern) = child_node(node, SyntaxKind::Pattern) else { return; };
    let Some(source_type_expr) = child_node(&pattern, SyntaxKind::TypeAnn)
        .and_then(|ann| child_node(&ann, SyntaxKind::TypeExpr))
    else { return; };
    let target_anns = child_nodes(node, SyntaxKind::TypeAnn);
    let Some(target_type_expr) = target_anns.first()
        .and_then(|ann| child_node(ann, SyntaxKind::TypeExpr))
    else { return; };
    let Some(source_sig) = parse_sig_type_expr(&source_type_expr) else { return; };
    let Some(target_sig) = parse_sig_type_expr(&target_type_expr) else { return; };
    if !cast_sig_is_nominal(&source_sig) || !cast_sig_is_nominal(&target_sig) {
        return;
    }
    // ...さらに50行以上...
}

pub(crate) fn lower_error_up_impl(
    state: &mut LowerState,
    node: &SyntaxNode,
    receiver: SigType,
    receiver_type_param_names: &[String],
) {
    // 相似した impl_def, pattern parsing, validation, scope setup...
}
```

**所感**: cast と error-up の違いは「signature の制約」と「role」だけなのに、両者が 200+ 行同じ流れを踏んでる。パラメータ化した `lower_*_impl_with_validation<T>` を作ってぶらさげた方がいいかもね。

---

## 6. lower/stmt/act/copy_transform.rs: ExprKind の巨大な match-all

- **場所**: `crates/yulang-infer/src/lower/stmt/act/copy_transform.rs:115-331`
- **匂い**: 216行の match 式で ExprKind の全 variant を処理，nested lambda 処理が特に複雑

```rust
fn transform_copied_expr_kind(
    types: &mut CopiedTypeVars<'_>,
    kind: &ExprKind,
    def_subst: &HashMap<DefId, DefId>,
) -> ExprKind {
    match kind {
        ExprKind::PrimitiveOp(op) => ExprKind::PrimitiveOp(*op),
        ExprKind::Lit(lit) => ExprKind::Lit(lit.clone()),
        ExprKind::Var(def) => ExprKind::Var(types.subst_expr_def(*def, def_subst)),
        // ... 10+ arms ...
        ExprKind::Lam(def, body) => {
            let copied_def = types.copy_local_def(*def);
            let source_local_defs = types.state.lambda_local_defs
                .get(def).cloned().unwrap_or_default();
            let copied_local_defs = source_local_defs
                .iter().map(|local_def| types.copy_local_def(*local_def)).collect::<Vec<_>>();
            if !copied_local_defs.is_empty() {
                types.state.lambda_local_defs.insert(copied_def, copied_local_defs);
            }
            // ... 6個の if-let 文で 5つ以上の HashMap から check&insert ...
            let previous = types.enter_local_defs(local_defs.as_slice());
            let body = transform_copied_principal_body_inner(types, body, def_subst);
            types.restore_local_defs(previous);
            ExprKind::Lam(copied_def, Box::new(body))
        }
        // ...
    }
}
```

**所感**: ExprKind::Lam の腕が 50+ 行あって、lambda metadata（param_pats, effect_annotations, etc）を5個の HashMap から繰り返して check & copy している。helper メソッド `copy_lambda_metadata` を分離した方が読みやすいかもね。

---

## 7. simplify/cooccur.rs の 3度のループと pass 連鎖

- **場所**: `crates/yulang-infer/src/simplify/cooccur.rs:93-150`
- **匂い**: 複数の substitution pass が sequential に適用され，each round で analysis を再計算

```rust
fn coalesce_by_co_occurrence_with_role_constraints_report_inner(
    scheme: &CompactTypeScheme,
    constraints: &[CompactRoleConstraint],
    use_representatives: bool,
) -> CoalesceOutput {
    let mut current_scheme = scheme.clone();
    let mut current_constraints = constraints.to_vec();
    let mut rounds = Vec::new();

    loop {
        let protected_vars = centered_constraint_vars(&current_constraints);
        let mut analysis =
            analyze_co_occurrences_with_role_constraints(&current_scheme, &current_constraints);
        let mut rec_vars = current_scheme.rec_vars.clone();
        let mut all_vars = collect_all_vars(&current_scheme, &analysis);
        let group_analysis = analyze_group_co_occurrences_with_role_constraints(
            &current_scheme, &current_constraints,
        );
        let exact_info = ExactInfo::from_analysis(&analysis);
        all_vars.extend(group_analysis.types.keys().copied());
        all_vars.extend(group_analysis.effect_types.keys().copied());
        all_vars.extend(group_analysis.effects.keys().copied());
        // ... sort/dedup ...

        let mut subst = HashMap::<TypeVar, Option<TypeVar>>::new();
        apply_group_co_occurrence_substitutions(
            &group_analysis, &mut analysis, &mut rec_vars, &protected_vars, &mut subst,
        );
        apply_polar_variable_removal(&all_vars, &analysis, &rec_vars, &protected_vars, &mut subst);
        apply_exact_row_unifications(&all_vars, &exact_info, &rec_vars, &protected_vars, &mut subst);
        apply_exact_sandwich_removal(&all_vars, &exact_info, &protected_vars, &mut subst);
        apply_shadow_var_collapse(&all_vars, &analysis, &protected_vars, &mut subst);
        apply_one_sided_exact_alias_collapse(&all_vars, &analysis, &protected_vars, &mut subst);
        // ...
    }
}
```

**所感**: loop の各 iteration で `analysis`, `rec_vars`, `all_vars`, `subst` が mutable に変わり、5個の `apply_*` pass が順序に依存して実行されてる。どの pass が `all_vars` を modify するか、どの pass が `subst` を depend するか、が明示的じゃない。Graph で pass dependence を explicit にして，fixpoint 検出ロジックを清潔にした方が良いかもね。

---

## 8. solve/selection/method.rs: DeferredSelection 解決ループの複雑さ

- **場所**: `crates/yulang-infer/src/solve/selection/method.rs:44-133`
- **匂い**: 10+ の解決試行が if/continue で連鎖，unresolved の推移が陰的

```rust
pub(crate) fn resolve_deferred_selections_for(&self, recv_tv: TypeVar) {
    let Some(selections) = self.deferred_selections.borrow().get(&recv_tv).cloned() else {
        return;
    };

    let mut unresolved = Vec::new();
    for selection in selections {
        if let Some(def) = self.resolve_selection_def(recv_tv, &selection.name) {
            if self.resolve_method_def_selection(recv_tv, &selection, def) {
                continue;  // success: skip this selection
            }
        }

        if !self.role_methods.contains_key(&selection.name)
            && let Some(def) = self.unique_type_method_named(&selection.name)
        {
            if self.resolve_method_def_selection(recv_tv, &selection, def) {
                continue;
            }
        }

        if let Some(def) = self.resolve_ref_selection_def(recv_tv, &selection.name) {
            if self.resolve_method_def_selection(recv_tv, &selection, def) {
                continue;
            }
        }

        if let Some(projection) =
            self.resolve_ref_field_projection_info(recv_tv, &selection.name)
        {
            if self.resolve_ref_field_projection_selection(recv_tv, &selection, projection) {
                continue;
            }
        }

        if let Some(info) = self.role_methods.get(&selection.name).cloned() {
            if self.resolve_deferred_selection(recv_tv, &selection, &info) {
                continue;
            }
        }
        // ... さらに 3+ 試行 ...

        unresolved.push(selection);
    }
    // ...
}
```

**所感**: 10+ の解決ストラテジーが imperative に列挙されてて、「どの順序でどの前提条件で試すか」が暗黙的。resolver strategy enum を作って、各 selection ごとに resolver の list を iterate して「最初に success した」を選ぶ方が declarative だし，order 変更や新規 strategy 追加が楽になるかもね。

---

## 9. lower/role_finalize/mod.rs: strip_compact_type_vars の recursive duplication

- **場所**: `crates/yulang-infer/src/lower/role_finalize/mod.rs:58-149`
- **匂い**: 構造を保ったまま vars を削除する transform が 92行，`compact_type_var` → `strip_compact_type_vars` → `normalize_builtin_numeric_compact_type` と3段階

```rust
fn strip_compact_type_vars(ty: &CompactType) -> CompactType {
    CompactType {
        vars: Default::default(),
        prims: ty.prims.clone(),
        cons: ty.cons.iter().map(|con| crate::simplify::compact::CompactCon {
            path: con.path.clone(),
            args: con.args.iter().map(|arg| CompactBounds {
                self_var: None,
                lower: strip_compact_type_vars(&arg.lower),
                upper: strip_compact_type_vars(&arg.upper),
            }).collect(),
        }).collect(),
        funs: ty.funs.iter().map(|fun| crate::simplify::compact::CompactFun {
            arg: strip_compact_type_vars(&fun.arg),
            arg_eff: strip_compact_type_vars(&fun.arg_eff),
            ret_eff: strip_compact_type_vars(&fun.ret_eff),
            ret: strip_compact_type_vars(&fun.ret),
        }).collect(),
        records: ty.records.iter().map(|record| crate::simplify::compact::CompactRecord {
            fields: record.fields.iter().map(|field| crate::types::RecordField {
                name: field.name.clone(),
                value: strip_compact_type_vars(&field.value),
                optional: field.optional,
            }).collect(),
        }).collect(),
        record_spreads: ty.record_spreads.iter().map(|spread| crate::simplify::compact::CompactRecordSpread {
            fields: spread.fields.iter().map(|field| crate::types::RecordField {
                name: field.name.clone(),
                value: strip_compact_type_vars(&field.value),
                optional: field.optional,
            }).collect(),
            tail: Box::new(strip_compact_type_vars(&spread.tail)),
            tail_wins: spread.tail_wins,
        }).collect(),
        // ... variants, tuples, rows も同じパターン ...
    }
}
```

**所感**: 構造를 보존하면서 vars를 제거하는 transformation이 명시적으로 풀려있다. Visitor pattern か fold combinator で「vars를 drop 하되 나머지는 유지」를 polymorphic하게 표현하면，코드 줄이나 재사용성이 올라갈 거 같다. normalize 단계도 이 안에 merge할 수 있을지도.

---

## 10. solve/mod.rs: Infer의 RefCell 밀집도

- **場所**: `crates/yulang-infer/src/solve/mod.rs:138-160`
- **匂い**: 20+ の RefCell フィールド，mutable な側面が多くの場所から shared

```rust
pub struct Infer {
    pub arena: TypeArena,
    pub lower: RefCell<FxHashMap<TypeVar, SmallVec<[PosId; 2]>>>,
    pub upper: RefCell<FxHashMap<TypeVar, SmallVec<[NegId; 2]>>>,
    pub lower_members: RefCell<FxHashSet<(TypeVar, PosId)>>,
    pub upper_members: RefCell<FxHashSet<(TypeVar, NegId)>>,
    pub compact_lower_instances: RefCell<FxHashMap<TypeVar, SmallVec<[OwnedSchemeInstance; 2]>>>,
    pub through: RefCell<FxHashSet<TypeVar>>,
    pub handler_matches: RefCell<Vec<HandlerMatchEdge>>,
    pub handler_match_dependents: RefCell<FxHashMap<TypeVar, SmallVec<[usize; 2]>>>,
    pub effect_boundary_keeps: RefCell<FxHashMap<TypeVar, ShiftKeep>>,
    pub levels: RefCell<FxHashMap<TypeVar, u32>>,
    pub origins: RefCell<FxHashMap<TypeVar, TypeOrigin>>,
    // ... さらに多数 ...
}
```

**所感**: RefCell でほぼ全フィールドを wrap してるから，runtime error で panic する危険が高い（特に nested borrow_mut)。制約が generated される phase と resolve される phase を厳密に分けて，phase boundary で RefCell を drop して不変な snapshot に変える方が安全かもね。或いはtype-level state machine (phantom type で phase を track) でコンパイル時に borrow conflict を防ぐとか。

---

## 11. display/dump.rs: collect_*_binding_paths の相似コード

- **場所**: `crates/yulang-infer/src/display/dump.rs:81-127`
- **匂い**: `collect_user_observable_binding_paths` と `collect_non_std_exported_binding_paths` がほぼ同じ，フィルタ条件だけ異なる

```rust
fn collect_user_observable_binding_paths(state: &LowerState) -> Vec<(Path, crate::ids::DefId)> {
    let canonical = crate::export::paths::collect_canonical_binding_paths(state);
    state.ctx.collect_observable_binding_paths()
        .into_iter()
        .filter(|(_, def)| {
            canonical.get(def)
                .and_then(|path| path.segments.first().cloned())
                .or_else(|| {
                    state.ctx.collect_all_binding_paths()
                        .into_iter()
                        .find_map(|(path, current)| (current == *def).then_some(path))
                        .and_then(|path| path.segments.first().cloned())
                })
                .map(|name| name.0.as_str() != "std")
                .unwrap_or(true)
        })
        .collect()
}

fn collect_non_std_exported_binding_paths(state: &LowerState) -> Vec<(Path, crate::ids::DefId)> {
    let canonical = crate::export::paths::collect_canonical_binding_paths(state);
    state.ctx.collect_exported_binding_paths()  // <- 唯一の差
        .into_iter()
        .filter(|(_, def)| {
            canonical.get(def)
                .and_then(|path| path.segments.first().cloned())
                .or_else(|| {
                    state.ctx.collect_all_binding_paths()
                        .into_iter()
                        .find_map(|(path, current)| (current == *def).then_some(path))
                        .and_then(|path| path.segments.first().cloned())
                })
                .map(|name| name.0.as_str() != "std")
                .unwrap_or(true)
        })
        .collect()
}
```

**所感**: 計算ロジックの 95% が同じ。`collector_fn` を parameter として `collect_binding_paths_with_filter` を作って両者を統一した方が保守的かもね。

---

## 12. lower/ctx.rs のモジュール traversal ロジック: depth-first walk の重複

- **場所**: `crates/yulang-infer/src/lower/ctx.rs:147-170`
- **匂い**: `collect_all_binding_paths`, `collect_all_type_paths` がほぼ同じ recursive walk を繰り返す

```rust
pub fn collect_all_binding_paths(&self) -> Vec<(Path, DefId)> {
    let mut out = Vec::new();
    if let Some(root_locals) = self.locals.first() {
        for (name, &def) in root_locals {
            out.push((Path { segments: vec![name.clone()] }, def));
        }
    }
    for module_id in self.modules.module_ids() {
        if self.modules.node(module_id).parent.is_none() {
            self.collect_module_binding_paths(module_id, Vec::new(), &mut out);
        }
    }
    // ... sort/dedup ...
    out
}

pub fn collect_all_type_paths(&self) -> Vec<(Path, DefId)> {
    let mut out = Vec::new();
    for module_id in self.modules.module_ids() {
        if self.modules.node(module_id).parent.is_none() {
            self.collect_module_type_paths(module_id, Vec::new(), &mut out);
        }
    }
    out
}
```

**所感**: `collect_module_binding_paths` と `collect_module_type_paths` がほぼ同じ recursive descent を持ってるはず。generic な `collect_module_items_with<T>` を作ってキーの種別（value vs type）を parameter にした方がいいかもね。

---

## 総括

yulang-infer コア engine の懸念は **層の蓄積に伴う partial duplication と context-switching の多さ**。単一責務に向かって以下のリファクタが候補:

1. **LowerState を分割**: scope/level/owner, effect/act, type-var cache, synthetic rewrite で層別。
2. **polarity-generic helper**: `coalesce` の正負分岐を enum wrapper で統一。
3. **freeze.rs overload の collapse**: 最終形 `_owned_with_non_generic_and_extra_vars` 直呼出し + 型安全 builder。
4. **ctx resolution の parametrization**: local-module-use の3フェーズを generic fold に。
5. **Deferred 解決の declarative strategy list**: if-continue chain を strategy enum list に。
6. **RefCell の phase separation**: constraint generation / resolve の境界を明確化。

いずれも「ロジック自体は正しいが，表現が imperative で重複が多い」という感じなので，時間があれば清潔化するとバグの温床が減るかなぁ。
