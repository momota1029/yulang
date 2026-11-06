# M1 solver: 追加した公開定理の全型

Status: Verified declarations; M1 as a whole remains partial.

Date: 2026-11-07

`integration/types` の開始点 `52c3410c31e0bfe2d4a0f23e8a2394358d557211` に対して追加した、32 module・498 public theorem の全型を記録する。各型は `import Yulang` の下で `#check @完全修飾名` を `lake env lean --trust=0` で実行した出力である。暗黙の型引数・量化子・前提を含み、省略記号は出ていない。追加 module の全 public theorem が Audit とこの一覧の両方に含まれることも照合した。private な証明補助、定義、abbrev は件数に数えない。

日本語の概要は各節の先頭、主結果と未完部分は [作業報告](2026-11-07-m1-solver-results.md)、証明範囲は [Lean README](../../lean/README.md) を参照する。「前順序」は反射律・推移律、「反対称な行 join 代数」は `RowFlowSchemes.Algebra` の全法則と反対称律を指す。

| Module | 公開定理数 |
| --- | --- |
| [MethodResolutionLocality](../../lean/Yulang/MethodResolutionLocality.lean) | 14 |
| [ModuleIncremental](../../lean/Yulang/ModuleIncremental.lean) | 12 |
| [ProducerContextual](../../lean/Yulang/ProducerContextual.lean) | 57 |
| [ProducerContextualRegular](../../lean/Yulang/ProducerContextualRegular.lean) | 34 |
| [CoreProducerContextualInstances](../../lean/Yulang/CoreProducerContextualInstances.lean) | 9 |
| [PositiveEquationElimination](../../lean/Yulang/PositiveEquationElimination.lean) | 20 |
| [MethodResolutionCost](../../lean/Yulang/MethodResolutionCost.lean) | 19 |
| [MethodResolutionIndex](../../lean/Yulang/MethodResolutionIndex.lean) | 21 |
| [InferenceSubstitutionCost](../../lean/Yulang/InferenceSubstitutionCost.lean) | 15 |
| [ProducerContextualNormalForm](../../lean/Yulang/ProducerContextualNormalForm.lean) | 5 |
| [ModuleInterfaceCache](../../lean/Yulang/ModuleInterfaceCache.lean) | 9 |
| [TypeSimplificationSize](../../lean/Yulang/TypeSimplificationSize.lean) | 19 |
| [ProducerContextualRecord](../../lean/Yulang/ProducerContextualRecord.lean) | 15 |
| [PresenceTailElimination](../../lean/Yulang/PresenceTailElimination.lean) | 38 |
| [PresenceTailRegular](../../lean/Yulang/PresenceTailRegular.lean) | 10 |
| [ContextualConstructorInspection](../../lean/Yulang/ContextualConstructorInspection.lean) | 3 |
| [ContextualNestedModels](../../lean/Yulang/ContextualNestedModels.lean) | 14 |
| [ContextualBranchSolver](../../lean/Yulang/ContextualBranchSolver.lean) | 5 |
| [ContextualTypeConstraintGraph](../../lean/Yulang/ContextualTypeConstraintGraph.lean) | 12 |
| [TypeSimplificationCheckCost](../../lean/Yulang/TypeSimplificationCheckCost.lean) | 14 |
| [ContextualValueBounds](../../lean/Yulang/ContextualValueBounds.lean) | 12 |
| [ContextualCoalescing](../../lean/Yulang/ContextualCoalescing.lean) | 11 |
| [ContextualRegularInference](../../lean/Yulang/ContextualRegularInference.lean) | 6 |
| [ContextualBranchInstances](../../lean/Yulang/ContextualBranchInstances.lean) | 3 |
| [ContextualTypeConstraintInference](../../lean/Yulang/ContextualTypeConstraintInference.lean) | 12 |
| [ContextualJointConstraintInference](../../lean/Yulang/ContextualJointConstraintInference.lean) | 14 |
| [TypeSimplificationCost](../../lean/Yulang/TypeSimplificationCost.lean) | 35 |
| [ContextualSourcePrincipalInference](../../lean/Yulang/ContextualSourcePrincipalInference.lean) | 18 |
| [CoreContextualSourceInference](../../lean/Yulang/CoreContextualSourceInference.lean) | 15 |
| [ContextualBranchCost](../../lean/Yulang/ContextualBranchCost.lean) | 9 |
| [ModuleScheduling](../../lean/Yulang/ModuleScheduling.lean) | 12 |
| [MethodResolutionScheduling](../../lean/Yulang/MethodResolutionScheduling.lean) | 6 |

## MethodResolutionLocality

任意の確定済み site の局所的な観測の一致から、実 resolve/freeze/finalize の一致を得る。同じ SCC 集合の任意の処理順序と重複に対して回答表が変わらない。

<details>
<summary>14 個の公開定理の完全な型</summary>

```lean
@Yulang.MethodResolutionLocality.resolve_local : ∀ {Row : Type} (left right : Yulang.MethodResolution.Site Row),
  Yulang.MethodResolutionLocality.SameFacts left right →
    Yulang.MethodResolution.resolve left = Yulang.MethodResolution.resolve right
```

```lean
@Yulang.MethodResolutionLocality.freeze_local : ∀ {Row : Type} (left right : Yulang.MethodResolution.Site Row),
  Yulang.MethodResolutionLocality.SameFacts left right →
    Yulang.MethodResolution.freeze left = Yulang.MethodResolution.freeze right
```

```lean
@Yulang.MethodResolutionLocality.finalize_local : ∀ {Row : Type} (left right : Yulang.MethodResolution.Site Row),
  Yulang.MethodResolutionLocality.SameFacts left right →
    ∀ (receiver : Yulang.FrozenMethods.CoreExpr),
      Yulang.FrozenMethods.finalize left receiver = Yulang.FrozenMethods.finalize right receiver
```

```lean
@Yulang.MethodResolutionLocality.run_apply : ∀ {Row : Type} {SiteId : Type u_1} [inst : DecidableEq SiteId]
  (sites : SiteId → Yulang.MethodResolution.Site Row) (order : List SiteId)
  (answers : Yulang.MethodResolutionLocality.Answers SiteId) (site : SiteId),
  Yulang.MethodResolutionLocality.run sites order answers site =
    if site ∈ order then some (Yulang.MethodResolution.resolve (sites site)) else answers site
```

```lean
@Yulang.MethodResolutionLocality.run_same_sites : ∀ {Row : Type} {SiteId : Type u_1} [inst : DecidableEq SiteId]
  (sites : SiteId → Yulang.MethodResolution.Site Row) (left right : List SiteId),
  (∀ (site : SiteId), site ∈ left ↔ site ∈ right) →
    ∀ (answers : Yulang.MethodResolutionLocality.Answers SiteId),
      Yulang.MethodResolutionLocality.run sites left answers = Yulang.MethodResolutionLocality.run sites right answers
```

```lean
@Yulang.MethodResolutionLocality.run_permutation : ∀ {Row : Type} {SiteId : Type u_1} [inst : DecidableEq SiteId]
  (sites : SiteId → Yulang.MethodResolution.Site Row) (left right : List SiteId),
  left.Perm right →
    ∀ (answers : Yulang.MethodResolutionLocality.Answers SiteId),
      Yulang.MethodResolutionLocality.run sites left answers = Yulang.MethodResolutionLocality.run sites right answers
```

```lean
@Yulang.MethodResolutionLocality.run_append : ∀ {Row : Type} {SiteId : Type u_1} [inst : DecidableEq SiteId]
  (sites : SiteId → Yulang.MethodResolution.Site Row) (first last : List SiteId)
  (answers : Yulang.MethodResolutionLocality.Answers SiteId),
  Yulang.MethodResolutionLocality.run sites (first ++ last) answers =
    Yulang.MethodResolutionLocality.run sites last (Yulang.MethodResolutionLocality.run sites first answers)
```

```lean
@Yulang.MethodResolutionLocality.runSCCs_flatMap : ∀ {Row : Type} {SiteId : Type u_1} {SCC : Type u_2}
  [inst : DecidableEq SiteId] (sites : SiteId → Yulang.MethodResolution.Site Row) (owned : SCC → List SiteId)
  (order : List SCC) (answers : Yulang.MethodResolutionLocality.Answers SiteId),
  Yulang.MethodResolutionLocality.runSCCs sites owned order answers =
    Yulang.MethodResolutionLocality.run sites (List.flatMap owned order) answers
```

```lean
@Yulang.MethodResolutionLocality.runSCCs_apply : ∀ {Row : Type} {SiteId : Type u_1} {SCC : Type u_2}
  [inst : DecidableEq SiteId] (sites : SiteId → Yulang.MethodResolution.Site Row) (owned : SCC → List SiteId)
  (order : List SCC) (answers : Yulang.MethodResolutionLocality.Answers SiteId) (site : SiteId),
  Yulang.MethodResolutionLocality.runSCCs sites owned order answers site =
    if ∃ component, component ∈ order ∧ site ∈ owned component then some (Yulang.MethodResolution.resolve (sites site))
    else answers site
```

```lean
@Yulang.MethodResolutionLocality.scc_order_independent : ∀ {Row : Type} {SiteId : Type u_1} {SCC : Type u_2}
  [inst : DecidableEq SiteId] (sites : SiteId → Yulang.MethodResolution.Site Row) (owned : SCC → List SiteId)
  (left right : List SCC),
  (∀ (component : SCC), component ∈ left ↔ component ∈ right) →
    ∀ (answers : Yulang.MethodResolutionLocality.Answers SiteId),
      Yulang.MethodResolutionLocality.runSCCs sites owned left answers =
        Yulang.MethodResolutionLocality.runSCCs sites owned right answers
```

```lean
@Yulang.MethodResolutionLocality.scc_permutation : ∀ {Row : Type} {SiteId : Type u_1} {SCC : Type u_2}
  [inst : DecidableEq SiteId] (sites : SiteId → Yulang.MethodResolution.Site Row) (owned : SCC → List SiteId)
  (left right : List SCC),
  left.Perm right →
    ∀ (answers : Yulang.MethodResolutionLocality.Answers SiteId),
      Yulang.MethodResolutionLocality.runSCCs sites owned left answers =
        Yulang.MethodResolutionLocality.runSCCs sites owned right answers
```

```lean
@Yulang.MethodResolutionLocality.resolved_site_exact : ∀ {Row : Type} {SiteId : Type u_1} {SCC : Type u_2}
  [inst : DecidableEq SiteId] (sites : SiteId → Yulang.MethodResolution.Site Row) (owned : SCC → List SiteId)
  (order : List SCC) (answers : Yulang.MethodResolutionLocality.Answers SiteId) (site : SiteId),
  (∃ component, component ∈ order ∧ site ∈ owned component) →
    ∀ (reference : Yulang.MethodResolution.Reference),
      Yulang.MethodResolutionLocality.runSCCs sites owned order answers site =
          some (Yulang.Methods.Selection.unique reference) ↔
        Yulang.MethodResolution.Selects (sites site) reference
```

```lean
@Yulang.MethodResolutionLocality.unprocessed_site_unchanged : ∀ {Row : Type} {SiteId : Type u_1} {SCC : Type u_2}
  [inst : DecidableEq SiteId] (sites : SiteId → Yulang.MethodResolution.Site Row) (owned : SCC → List SiteId)
  (order : List SCC) (answers : Yulang.MethodResolutionLocality.Answers SiteId) (site : SiteId),
  (¬∃ component, component ∈ order ∧ site ∈ owned component) →
    Yulang.MethodResolutionLocality.runSCCs sites owned order answers site = answers site
```

```lean
@Yulang.MethodResolutionLocality.scc_input_locality : ∀ {Row : Type} {SiteId : Type u_1} {SCC : Type u_2}
  [inst : DecidableEq SiteId] (left right : SiteId → Yulang.MethodResolution.Site Row) (owned : SCC → List SiteId)
  (order : List SCC) (answers : Yulang.MethodResolutionLocality.Answers SiteId),
  (∀ (component : SCC),
      component ∈ order →
        ∀ (site : SiteId),
          site ∈ owned component → Yulang.MethodResolutionLocality.SameFacts (left site) (right site)) →
    Yulang.MethodResolutionLocality.runSCCs left owned order answers =
      Yulang.MethodResolutionLocality.runSCCs right owned order answers
```

</details>

## ModuleIncremental

任意の局所純粋 compiler と完全な source/key・依存 artifact について、実 dirty 計算と逆依存経路、増分 build と全体 build、実 compile 呼出範囲を一致させる。clean node の入力不変性と正しい旧 cache を前提に明記する。

<details>
<summary>12 個の公開定理の完全な型</summary>

```lean
Yulang.ModuleIncremental.affected_iff : ∀ (changed : Nat → Bool) (dependencies : Yulang.ModuleIncremental.Dependencies)
  (node : Nat),
  Yulang.ModuleIncremental.Affected changed dependencies node ↔
    changed node = true ∨
      ∃ dependency, dependency ∈ dependencies node ∧ Yulang.ModuleIncremental.Affected changed dependencies ↑dependency
```

```lean
Yulang.ModuleIncremental.dirty_exact : ∀ (changed : Nat → Bool) (dependencies : Yulang.ModuleIncremental.Dependencies)
  (n : Nat) (node : Fin n),
  Yulang.ModuleIncremental.dirty changed dependencies n node = true ↔
    Yulang.ModuleIncremental.Affected changed dependencies ↑node
```

```lean
@Yulang.ModuleIncremental.clean_build_equal : ∀ {Source : Type u_1} {Interface : Type u_2}
  (compile : Source → List Interface → Interface) (before after : Nat → Source)
  (dependencies : Yulang.ModuleIncremental.Dependencies) (changed : Nat → Bool),
  (∀ (node : Nat), changed node = false → before node = after node) →
    ∀ (n : Nat) (node : Fin n),
      Yulang.ModuleIncremental.dirty changed dependencies n node = false →
        Yulang.ModuleIncremental.build compile before dependencies n node =
          Yulang.ModuleIncremental.build compile after dependencies n node
```

```lean
@Yulang.ModuleIncremental.rebuild_exact : ∀ {Source : Type u_1} {Interface : Type u_2}
  (compile : Source → List Interface → Interface) (before after : Nat → Source)
  (dependencies : Yulang.ModuleIncremental.Dependencies) (changed : Nat → Bool),
  (∀ (node : Nat), changed node = false → before node = after node) →
    ∀ (n : Nat),
      (Yulang.ModuleIncremental.rebuild compile after dependencies changed n
            (Yulang.ModuleIncremental.build compile before dependencies n)).fst =
        Yulang.ModuleIncremental.build compile after dependencies n
```

```lean
@Yulang.ModuleIncremental.rebuild_valid_cache : ∀ {Source : Type u_1} {Interface : Type u_2}
  (compile : Source → List Interface → Interface) (before after : Nat → Source)
  (dependencies : Yulang.ModuleIncremental.Dependencies) (changed : Nat → Bool),
  (∀ (node : Nat), changed node = false → before node = after node) →
    ∀ (n : Nat) (cached : Fin n → Interface),
      (∀ (node : Fin n), cached node = Yulang.ModuleIncremental.build compile before dependencies n node) →
        (Yulang.ModuleIncremental.rebuild compile after dependencies changed n cached).fst =
          Yulang.ModuleIncremental.build compile after dependencies n
```

```lean
@Yulang.ModuleIncremental.rebuild_trace : ∀ {Source : Type u_1} {Interface : Type u_2}
  (compile : Source → List Interface → Interface) (source : Nat → Source)
  (dependencies : Yulang.ModuleIncremental.Dependencies) (changed : Nat → Bool) (n : Nat) (cached : Fin n → Interface),
  (Yulang.ModuleIncremental.rebuild compile source dependencies changed n cached).snd =
    List.map Fin.val (List.filter (Yulang.ModuleIncremental.dirty changed dependencies n) (List.finRange n))
```

```lean
@Yulang.ModuleIncremental.rebuild_calls_le : ∀ {Source : Type u_1} {Interface : Type u_2}
  (compile : Source → List Interface → Interface) (source : Nat → Source)
  (dependencies : Yulang.ModuleIncremental.Dependencies) (changed : Nat → Bool) (n : Nat) (cached : Fin n → Interface),
  (Yulang.ModuleIncremental.rebuild compile source dependencies changed n cached).snd.length ≤ n
```

```lean
@Yulang.ModuleIncremental.rebuild_called_iff : ∀ {Source : Type u_1} {Interface : Type u_2}
  (compile : Source → List Interface → Interface) (source : Nat → Source)
  (dependencies : Yulang.ModuleIncremental.Dependencies) (changed : Nat → Bool) (n : Nat) (cached : Fin n → Interface)
  (node : Nat),
  node ∈ (Yulang.ModuleIncremental.rebuild compile source dependencies changed n cached).snd ↔
    node < n ∧ Yulang.ModuleIncremental.Affected changed dependencies node
```

```lean
@Yulang.ModuleIncremental.clean_build_changed_graph : ∀ {Source : Type u_1} {Interface : Type u_2}
  (compile : Source → List Interface → Interface) (before after : Nat → Source)
  (oldDependencies newDependencies : Yulang.ModuleIncremental.Dependencies) (changed : Nat → Bool),
  (∀ (node : Nat), changed node = false → before node = after node ∧ oldDependencies node = newDependencies node) →
    ∀ (n : Nat) (node : Fin n),
      Yulang.ModuleIncremental.dirty changed newDependencies n node = false →
        Yulang.ModuleIncremental.build compile before oldDependencies n node =
          Yulang.ModuleIncremental.build compile after newDependencies n node
```

```lean
@Yulang.ModuleIncremental.rebuild_changed_graph_exact : ∀ {Source : Type u_1} {Interface : Type u_2}
  (compile : Source → List Interface → Interface) (before after : Nat → Source)
  (oldDependencies newDependencies : Yulang.ModuleIncremental.Dependencies) (changed : Nat → Bool),
  (∀ (node : Nat), changed node = false → before node = after node ∧ oldDependencies node = newDependencies node) →
    ∀ (n : Nat),
      (Yulang.ModuleIncremental.rebuild compile after newDependencies changed n
            (Yulang.ModuleIncremental.build compile before oldDependencies n)).fst =
        Yulang.ModuleIncremental.build compile after newDependencies n
```

```lean
@Yulang.ModuleIncremental.rebuild_normal_forms : ∀ {Source : Type u_1} {Interface : Type u_2} {Normal : Type}
  (normalize : Interface → Normal) (compile : Source → List Interface → Interface) (before after : Nat → Source)
  (oldDependencies newDependencies : Yulang.ModuleIncremental.Dependencies) (changed : Nat → Bool),
  (∀ (node : Nat), changed node = false → before node = after node ∧ oldDependencies node = newDependencies node) →
    ∀ (n : Nat) (node : Fin n),
      normalize
          ((Yulang.ModuleIncremental.rebuild compile after newDependencies changed n
                (Yulang.ModuleIncremental.build compile before oldDependencies n)).fst
            node) =
        normalize (Yulang.ModuleIncremental.build compile after newDependencies n node)
```

```lean
@Yulang.ModuleIncremental.module_cache_sound : ∀ {Source : Type u_1} {Interface : Type u_2}
  (compile : Source → List Interface → Interface) (before after : Source)
  (oldDependencies newDependencies : List Interface),
  before = after → oldDependencies = newDependencies → compile before oldDependencies = compile after newDependencies
```

</details>

## ProducerContextual

union を含まない要求に任意型を表す変数と role-head 観測を加える。任意行関係で前順序と constructor grouping、行前順序で全 arrow 分解を示し、混合 union と top を分離する。

<details>
<summary>57 個の公開定理の完全な型</summary>

```lean
@Yulang.ProducerContextual.probeStep_union : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {env : Yulang.ProducerContextual.Environment Row}
  {argumentOrder : Yulang.StructuralBase.Ty Row → Yulang.StructuralBase.Ty Row → Prop}
  (first last : Yulang.StructuralBase.Ty Row) (obs : Yulang.ProducerContextual.Observation Row),
  Yulang.ProducerContextual.ProbeStep leRow env argumentOrder (first.union last) obs ↔
    Yulang.ProducerContextual.ProbeStep leRow env argumentOrder first obs ∧
      Yulang.ProducerContextual.ProbeStep leRow env argumentOrder last obs
```

```lean
@Yulang.ProducerContextual.probeStep_inter : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {env : Yulang.ProducerContextual.Environment Row}
  {argumentOrder : Yulang.StructuralBase.Ty Row → Yulang.StructuralBase.Ty Row → Prop}
  (first last : Yulang.StructuralBase.Ty Row) (obs : Yulang.ProducerContextual.Observation Row),
  Yulang.ProducerContextual.ProbeStep leRow env argumentOrder (first.inter last) obs ↔
    Yulang.ProducerContextual.ProbeStep leRow env argumentOrder first obs ∨
      Yulang.ProducerContextual.ProbeStep leRow env argumentOrder last obs
```

```lean
@Yulang.ProducerContextual.probeStep_bottom : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {env : Yulang.ProducerContextual.Environment Row}
  {argumentOrder : Yulang.StructuralBase.Ty Row → Yulang.StructuralBase.Ty Row → Prop}
  (obs : Yulang.ProducerContextual.Observation Row),
  Yulang.ProducerContextual.ProbeStep leRow env argumentOrder Yulang.StructuralBase.Ty.bottom obs
```

```lean
@Yulang.ProducerContextual.probeStep_trivial : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {env : Yulang.ProducerContextual.Environment Row}
  {argumentOrder : Yulang.StructuralBase.Ty Row → Yulang.StructuralBase.Ty Row → Prop}
  (type : Yulang.StructuralBase.Ty Row),
  Yulang.ProducerContextual.ProbeStep leRow env argumentOrder type Yulang.ProducerContextual.Observation.trivial
```

```lean
@Yulang.ProducerContextual.probeAt_union : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {env : Yulang.ProducerContextual.Environment Row} (rank : Nat) (first last : Yulang.StructuralBase.Ty Row)
  (obs : Yulang.ProducerContextual.Observation Row),
  Yulang.ProducerContextual.ProbeAt leRow rank env (first.union last) obs ↔
    Yulang.ProducerContextual.ProbeAt leRow rank env first obs ∧
      Yulang.ProducerContextual.ProbeAt leRow rank env last obs
```

```lean
@Yulang.ProducerContextual.probeAt_inter : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {env : Yulang.ProducerContextual.Environment Row} (rank : Nat) (first last : Yulang.StructuralBase.Ty Row)
  (obs : Yulang.ProducerContextual.Observation Row),
  Yulang.ProducerContextual.ProbeAt leRow rank env (first.inter last) obs ↔
    Yulang.ProducerContextual.ProbeAt leRow rank env first obs ∨
      Yulang.ProducerContextual.ProbeAt leRow rank env last obs
```

```lean
@Yulang.ProducerContextual.probeAt_bottom : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {env : Yulang.ProducerContextual.Environment Row} (rank : Nat) (obs : Yulang.ProducerContextual.Observation Row),
  Yulang.ProducerContextual.ProbeAt leRow rank env Yulang.StructuralBase.Ty.bottom obs
```

```lean
@Yulang.ProducerContextual.probeAt_trivial : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {env : Yulang.ProducerContextual.Environment Row} (rank : Nat) (type : Yulang.StructuralBase.Ty Row),
  Yulang.ProducerContextual.ProbeAt leRow rank env type Yulang.ProducerContextual.Observation.trivial
```

```lean
@Yulang.ProducerContextual.acceptAt_atom : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (rank : Nat)
  (env : Yulang.ProducerContextual.Environment Row) (type : Yulang.StructuralBase.Ty Row)
  (obs : Yulang.ProducerContextual.Observation Row),
  Yulang.ProducerContextual.AcceptAt leRow rank env type (Yulang.ProducerContextual.Demand.atom obs) ↔
    Yulang.ProducerContextual.ProbeAt leRow rank env type obs
```

```lean
@Yulang.ProducerContextual.acceptAt_var : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (rank : Nat)
  (env : Yulang.ProducerContextual.Environment Row) (type : Yulang.StructuralBase.Ty Row) (name : Nat),
  Yulang.ProducerContextual.AcceptAt leRow rank env type (Yulang.ProducerContextual.Demand.var name) ↔
    ∀ (obs : Yulang.ProducerContextual.Observation Row),
      Yulang.ProducerContextual.ProbeAt leRow rank env (env.types name) obs →
        Yulang.ProducerContextual.ProbeAt leRow rank env type obs
```

```lean
@Yulang.ProducerContextual.acceptAt_role : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (rank : Nat)
  (env : Yulang.ProducerContextual.Environment Row) (type : Yulang.StructuralBase.Ty Row) (name : Nat),
  Yulang.ProducerContextual.AcceptAt leRow rank env type (Yulang.ProducerContextual.Demand.role name) ↔
    Yulang.ProducerContextual.ProbeAt leRow rank env type (Yulang.ProducerContextual.Observation.role name)
```

```lean
@Yulang.ProducerContextual.acceptAt_inter : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (rank : Nat)
  (env : Yulang.ProducerContextual.Environment Row) (type : Yulang.StructuralBase.Ty Row)
  (first last : Yulang.ProducerContextual.Demand Row),
  Yulang.ProducerContextual.AcceptAt leRow rank env type (first.inter last) ↔
    Yulang.ProducerContextual.AcceptAt leRow rank env type first ∧
      Yulang.ProducerContextual.AcceptAt leRow rank env type last
```

```lean
@Yulang.ProducerContextual.acceptAt_mask : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (rank : Nat)
  (env : Yulang.ProducerContextual.Environment Row) (type : Yulang.StructuralBase.Ty Row) (hidden : List Nat)
  (demand : Yulang.ProducerContextual.Demand Row),
  Yulang.ProducerContextual.AcceptAt leRow rank env type (Yulang.ProducerContextual.Demand.mask hidden demand) ↔
    ∀ (obs : Yulang.ProducerContextual.Observation Row),
      Yulang.ProducerContextual.Demand.tests leRow rank env demand obs →
        Yulang.ProducerContextual.ProbeAt leRow rank env type (Yulang.ProducerContextual.Observation.mask hidden obs)
```

```lean
@Yulang.ProducerContextual.producerLeAt_iff_probe : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (rank : Nat)
  (source target : Yulang.StructuralBase.Ty Row),
  Yulang.ProducerContextual.ProducerLeAt leRow rank source target ↔
    ∀ (env : Yulang.ProducerContextual.Environment Row) (obs : Yulang.ProducerContextual.Observation Row),
      Yulang.ProducerContextual.ProbeAt leRow rank env target obs →
        Yulang.ProducerContextual.ProbeAt leRow rank env source obs
```

```lean
@Yulang.ProducerContextual.producerLe_iff_probe : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  (source target : Yulang.StructuralBase.Ty Row),
  Yulang.ProducerContextual.ProducerLe leRow source target ↔
    ∀ (rank : Nat) (env : Yulang.ProducerContextual.Environment Row) (obs : Yulang.ProducerContextual.Observation Row),
      Yulang.ProducerContextual.ProbeAt leRow rank env target obs →
        Yulang.ProducerContextual.ProbeAt leRow rank env source obs
```

```lean
@Yulang.ProducerContextual.producerEq_iff_probe : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  (source target : Yulang.StructuralBase.Ty Row),
  Yulang.ProducerContextual.ProducerEq leRow source target ↔
    ∀ (rank : Nat) (env : Yulang.ProducerContextual.Environment Row) (obs : Yulang.ProducerContextual.Observation Row),
      Yulang.ProducerContextual.ProbeAt leRow rank env source obs ↔
        Yulang.ProducerContextual.ProbeAt leRow rank env target obs
```

```lean
@Yulang.ProducerContextual.producerLe_refl : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  (type : Yulang.StructuralBase.Ty Row), Yulang.ProducerContextual.ProducerLe leRow type type
```

```lean
@Yulang.ProducerContextual.producerLe_trans : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {first middle last : Yulang.StructuralBase.Ty Row},
  Yulang.ProducerContextual.ProducerLe leRow first middle →
    Yulang.ProducerContextual.ProducerLe leRow middle last → Yulang.ProducerContextual.ProducerLe leRow first last
```

```lean
@Yulang.ProducerContextual.producerEq_refl : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  (type : Yulang.StructuralBase.Ty Row), Yulang.ProducerContextual.ProducerEq leRow type type
```

```lean
@Yulang.ProducerContextual.producerEq_symm : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {first last : Yulang.StructuralBase.Ty Row},
  Yulang.ProducerContextual.ProducerEq leRow first last → Yulang.ProducerContextual.ProducerEq leRow last first
```

```lean
@Yulang.ProducerContextual.producerEq_trans : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {first middle last : Yulang.StructuralBase.Ty Row},
  Yulang.ProducerContextual.ProducerEq leRow first middle →
    Yulang.ProducerContextual.ProducerEq leRow middle last → Yulang.ProducerContextual.ProducerEq leRow first last
```

```lean
@Yulang.ProducerContextual.structural_subtype_preserved : ∀ {Row : Type u_1} {leRow : Row → Row → Prop},
  (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
    ∀ {source target : Yulang.StructuralBase.Ty Row},
      Yulang.StructuralBase.Subtype leRow source target → Yulang.ProducerContextual.ProducerLe leRow source target
```

```lean
@Yulang.ProducerContextual.pair_union_group : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  (a b c d : Yulang.StructuralBase.Ty Row),
  Yulang.ProducerContextual.ProducerEq leRow ((a.pair b).union (c.pair d)) ((a.union c).pair (b.union d))
```

```lean
@Yulang.ProducerContextual.record_union_group : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (label : Nat)
  (a rest b tail : Yulang.StructuralBase.Ty Row),
  Yulang.ProducerContextual.ProducerEq leRow
    ((Yulang.StructuralBase.Ty.record label a rest).union (Yulang.StructuralBase.Ty.record label b tail))
    (Yulang.StructuralBase.Ty.record label (a.union b) (rest.union tail))
```

```lean
@Yulang.ProducerContextual.pair_union_first : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  (a b c : Yulang.StructuralBase.Ty Row),
  Yulang.ProducerContextual.ProducerEq leRow ((a.union b).pair c) ((a.pair c).union (b.pair c))
```

```lean
@Yulang.ProducerContextual.pair_union_last : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  (a b c : Yulang.StructuralBase.Ty Row),
  Yulang.ProducerContextual.ProducerEq leRow (a.pair (b.union c)) ((a.pair b).union (a.pair c))
```

```lean
@Yulang.ProducerContextual.record_union_payload : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (label : Nat)
  (a b rest : Yulang.StructuralBase.Ty Row),
  Yulang.ProducerContextual.ProducerEq leRow (Yulang.StructuralBase.Ty.record label (a.union b) rest)
    ((Yulang.StructuralBase.Ty.record label a rest).union (Yulang.StructuralBase.Ty.record label b rest))
```

```lean
@Yulang.ProducerContextual.variant_union : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (label : Nat)
  (a b : Yulang.StructuralBase.Ty Row),
  Yulang.ProducerContextual.ProducerEq leRow (Yulang.StructuralBase.Ty.variant label (a.union b))
    ((Yulang.StructuralBase.Ty.variant label a).union (Yulang.StructuralBase.Ty.variant label b))
```

```lean
@Yulang.ProducerContextual.probeAt_pairFirst : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {env : Yulang.ProducerContextual.Environment Row} (rank : Nat) (a b : Yulang.StructuralBase.Ty Row)
  (obs : Yulang.ProducerContextual.Observation Row),
  Yulang.ProducerContextual.ProbeAt leRow rank env (a.pair b) obs.pairFirst ↔
    Yulang.ProducerContextual.ProbeAt leRow rank env a obs
```

```lean
@Yulang.ProducerContextual.probeAt_pairLast : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {env : Yulang.ProducerContextual.Environment Row} (rank : Nat) (a b : Yulang.StructuralBase.Ty Row)
  (obs : Yulang.ProducerContextual.Observation Row),
  Yulang.ProducerContextual.ProbeAt leRow rank env (a.pair b) obs.pairLast ↔
    Yulang.ProducerContextual.ProbeAt leRow rank env b obs
```

```lean
@Yulang.ProducerContextual.probeAt_variant : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {env : Yulang.ProducerContextual.Environment Row} (rank actual expected : Nat)
  (payload : Yulang.StructuralBase.Ty Row) (obs : Yulang.ProducerContextual.Observation Row),
  Yulang.ProducerContextual.ProbeAt leRow rank env (Yulang.StructuralBase.Ty.variant actual payload)
      (Yulang.ProducerContextual.Observation.variant expected obs) ↔
    actual = expected ∧ Yulang.ProducerContextual.ProbeAt leRow rank env payload obs
```

```lean
@Yulang.ProducerContextual.producerLe_pair_iff : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  (a b c d : Yulang.StructuralBase.Ty Row),
  Yulang.ProducerContextual.ProducerLe leRow (a.pair b) (c.pair d) ↔
    Yulang.ProducerContextual.ProducerLe leRow a c ∧ Yulang.ProducerContextual.ProducerLe leRow b d
```

```lean
@Yulang.ProducerContextual.producerLe_variant_iff : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (label : Nat)
  (a b : Yulang.StructuralBase.Ty Row),
  Yulang.ProducerContextual.ProducerLe leRow (Yulang.StructuralBase.Ty.variant label a)
      (Yulang.StructuralBase.Ty.variant label b) ↔
    Yulang.ProducerContextual.ProducerLe leRow a b
```

```lean
@Yulang.ProducerContextual.producerLe_record_mono : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (label : Nat)
  {a b rest tail : Yulang.StructuralBase.Ty Row},
  Yulang.ProducerContextual.ProducerLe leRow a b →
    Yulang.ProducerContextual.ProducerLe leRow rest tail →
      Yulang.ProducerContextual.ProducerLe leRow (Yulang.StructuralBase.Ty.record label a rest)
        (Yulang.StructuralBase.Ty.record label b tail)
```

```lean
@Yulang.ProducerContextual.producerLe_union_mono : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {a b c d : Yulang.StructuralBase.Ty Row},
  Yulang.ProducerContextual.ProducerLe leRow a b →
    Yulang.ProducerContextual.ProducerLe leRow c d → Yulang.ProducerContextual.ProducerLe leRow (a.union c) (b.union d)
```

```lean
@Yulang.ProducerContextual.producerLe_inter_mono : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {a b c d : Yulang.StructuralBase.Ty Row},
  Yulang.ProducerContextual.ProducerLe leRow a b →
    Yulang.ProducerContextual.ProducerLe leRow c d → Yulang.ProducerContextual.ProducerLe leRow (a.inter c) (b.inter d)
```

```lean
@Yulang.ProducerContextual.producerLe_union_iff : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  (a b c : Yulang.StructuralBase.Ty Row),
  Yulang.ProducerContextual.ProducerLe leRow (a.union b) c ↔
    Yulang.ProducerContextual.ProducerLe leRow a c ∧ Yulang.ProducerContextual.ProducerLe leRow b c
```

```lean
@Yulang.ProducerContextual.producerLe_inter_iff : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  (a b c : Yulang.StructuralBase.Ty Row),
  Yulang.ProducerContextual.ProducerLe leRow a (b.inter c) ↔
    Yulang.ProducerContextual.ProducerLe leRow a b ∧ Yulang.ProducerContextual.ProducerLe leRow a c
```

```lean
@Yulang.ProducerContextual.producerLe_union_left : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  (a b : Yulang.StructuralBase.Ty Row), Yulang.ProducerContextual.ProducerLe leRow a (a.union b)
```

```lean
@Yulang.ProducerContextual.producerLe_union_right : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  (a b : Yulang.StructuralBase.Ty Row), Yulang.ProducerContextual.ProducerLe leRow b (a.union b)
```

```lean
@Yulang.ProducerContextual.producerEq_union_absorb : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {a b : Yulang.StructuralBase.Ty Row},
  Yulang.ProducerContextual.ProducerLe leRow a b → Yulang.ProducerContextual.ProducerEq leRow (a.union b) b
```

```lean
@Yulang.ProducerContextual.producerEq_union : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {a b c d : Yulang.StructuralBase.Ty Row},
  Yulang.ProducerContextual.ProducerEq leRow a b →
    Yulang.ProducerContextual.ProducerEq leRow c d → Yulang.ProducerContextual.ProducerEq leRow (a.union c) (b.union d)
```

```lean
@Yulang.ProducerContextual.producerEq_inter : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {a b c d : Yulang.StructuralBase.Ty Row},
  Yulang.ProducerContextual.ProducerEq leRow a b →
    Yulang.ProducerContextual.ProducerEq leRow c d → Yulang.ProducerContextual.ProducerEq leRow (a.inter c) (b.inter d)
```

```lean
@Yulang.ProducerContextual.producerEq_pair : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {a b c d : Yulang.StructuralBase.Ty Row},
  Yulang.ProducerContextual.ProducerEq leRow a b →
    Yulang.ProducerContextual.ProducerEq leRow c d → Yulang.ProducerContextual.ProducerEq leRow (a.pair c) (b.pair d)
```

```lean
@Yulang.ProducerContextual.producerEq_record : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (label : Nat)
  {a b rest tail : Yulang.StructuralBase.Ty Row},
  Yulang.ProducerContextual.ProducerEq leRow a b →
    Yulang.ProducerContextual.ProducerEq leRow rest tail →
      Yulang.ProducerContextual.ProducerEq leRow (Yulang.StructuralBase.Ty.record label a rest)
        (Yulang.StructuralBase.Ty.record label b tail)
```

```lean
@Yulang.ProducerContextual.producerEq_variant : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (label : Nat)
  {a b : Yulang.StructuralBase.Ty Row},
  Yulang.ProducerContextual.ProducerEq leRow a b →
    Yulang.ProducerContextual.ProducerEq leRow (Yulang.StructuralBase.Ty.variant label a)
      (Yulang.StructuralBase.Ty.variant label b)
```

```lean
@Yulang.ProducerContextual.arrow_argument_inversion : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {input input' output output' : Yulang.StructuralBase.Ty Row} {inputRow inputRow' outputRow outputRow' : Row},
  Yulang.ProducerContextual.ProducerLe leRow (input.arrow inputRow output outputRow)
      (input'.arrow inputRow' output' outputRow') →
    Yulang.ProducerContextual.ProducerLe leRow input' input
```

```lean
@Yulang.ProducerContextual.arrow_result_inversion : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {input input' output output' : Yulang.StructuralBase.Ty Row} {inputRow inputRow' outputRow outputRow' : Row},
  Yulang.ProducerContextual.ProducerLe leRow (input.arrow inputRow output outputRow)
      (input'.arrow inputRow' output' outputRow') →
    Yulang.ProducerContextual.ProducerLe leRow output output'
```

```lean
@Yulang.ProducerContextual.arrow_input_row_inversion : ∀ {Row : Type u_1} {leRow : Row → Row → Prop},
  (∀ (row : Row), leRow row row) →
    ∀ {input input' output output' : Yulang.StructuralBase.Ty Row} {inputRow inputRow' outputRow outputRow' : Row},
      Yulang.ProducerContextual.ProducerLe leRow (input.arrow inputRow output outputRow)
          (input'.arrow inputRow' output' outputRow') →
        leRow inputRow' inputRow
```

```lean
@Yulang.ProducerContextual.arrow_output_row_inversion : ∀ {Row : Type u_1} {leRow : Row → Row → Prop},
  (∀ (row : Row), leRow row row) →
    ∀ {input input' output output' : Yulang.StructuralBase.Ty Row} {inputRow inputRow' outputRow outputRow' : Row},
      Yulang.ProducerContextual.ProducerLe leRow (input.arrow inputRow output outputRow)
          (input'.arrow inputRow' output' outputRow') →
        leRow outputRow outputRow'
```

```lean
@Yulang.ProducerContextual.producerLe_arrow : ∀ {Row : Type u_1} {leRow : Row → Row → Prop},
  (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
    ∀ {input input' output output' : Yulang.StructuralBase.Ty Row} {inputRow inputRow' outputRow outputRow' : Row},
      Yulang.ProducerContextual.ProducerLe leRow input' input →
        leRow inputRow' inputRow →
          Yulang.ProducerContextual.ProducerLe leRow output output' →
            leRow outputRow outputRow' →
              Yulang.ProducerContextual.ProducerLe leRow (input.arrow inputRow output outputRow)
                (input'.arrow inputRow' output' outputRow')
```

```lean
@Yulang.ProducerContextual.producerLe_arrow_iff : ∀ {Row : Type u_1} {leRow : Row → Row → Prop},
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      ∀ (input input' output output' : Yulang.StructuralBase.Ty Row) (inputRow inputRow' outputRow outputRow' : Row),
        Yulang.ProducerContextual.ProducerLe leRow (input.arrow inputRow output outputRow)
            (input'.arrow inputRow' output' outputRow') ↔
          Yulang.ProducerContextual.ProducerLe leRow input' input ∧
            leRow inputRow' inputRow ∧
              Yulang.ProducerContextual.ProducerLe leRow output output' ∧ leRow outputRow outputRow'
```

```lean
@Yulang.ProducerContextual.producerEq_arrow : ∀ {Row : Type u_1} {leRow : Row → Row → Prop},
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      ∀ {input input' output output' : Yulang.StructuralBase.Ty Row} (inputRow outputRow : Row),
        Yulang.ProducerContextual.ProducerEq leRow input input' →
          Yulang.ProducerContextual.ProducerEq leRow output output' →
            Yulang.ProducerContextual.ProducerEq leRow (input.arrow inputRow output outputRow)
              (input'.arrow inputRow output' outputRow)
```

```lean
@Yulang.ProducerContextual.Examples.mixed_union_has_role : ∀ {Row : Type u_1} (leRow : Row → Row → Prop) (rank : Nat),
  Yulang.ProducerContextual.AcceptAt leRow rank (Yulang.ProducerContextual.Examples.mixedRole Row)
    ((Yulang.StructuralBase.Ty.base Yulang.Inference.Base.int).union
      (Yulang.StructuralBase.Ty.base Yulang.Inference.Base.str))
    (Yulang.ProducerContextual.Demand.role 0)
```

```lean
@Yulang.ProducerContextual.Examples.top_lacks_role : ∀ {Row : Type u_1} (leRow : Row → Row → Prop) (rank : Nat),
  ¬Yulang.ProducerContextual.AcceptAt leRow rank (Yulang.ProducerContextual.Examples.mixedRole Row)
      Yulang.StructuralBase.Ty.top (Yulang.ProducerContextual.Demand.role 0)
```

```lean
@Yulang.ProducerContextual.Examples.mixed_union_not_equivalent_top : ∀ {Row : Type u_1} (leRow : Row → Row → Prop),
  ¬Yulang.ProducerContextual.ProducerEq leRow
      ((Yulang.StructuralBase.Ty.base Yulang.Inference.Base.int).union
        (Yulang.StructuralBase.Ty.base Yulang.Inference.Base.str))
      Yulang.StructuralBase.Ty.top
```

```lean
@Yulang.ProducerContextual.Examples.mixed_arrow_not_equivalent_top_arrow : ∀ {Row : Type u_1} (leRow : Row → Row → Prop)
  (row : Row),
  ¬Yulang.ProducerContextual.ProducerEq leRow
      (((Yulang.StructuralBase.Ty.base Yulang.Inference.Base.int).union
            (Yulang.StructuralBase.Ty.base Yulang.Inference.Base.str)).arrow
        row (Yulang.StructuralBase.Ty.base Yulang.Inference.Base.int) row)
      (Yulang.StructuralBase.Ty.top.arrow row (Yulang.StructuralBase.Ty.base Yulang.Inference.Base.int) row)
```

</details>

## ProducerContextualRegular

任意の regular graph の全深さで、新しい要求順序の全 arrow 分解・constructor 合同性・旧構造部分型の保存を証明する。exact/default/mask の producer constructor は含めない。

<details>
<summary>34 個の公開定理の完全な型</summary>

```lean
@Yulang.ProducerContextualRegular.referenceLe_refl : ∀ {Row : Type u_1} {State : Type u_2}
  {graph : Yulang.RegularValueTypes.Graph Row State} {leRow : Row → Row → Prop} (state : State),
  Yulang.ProducerContextualRegular.ReferenceLe graph leRow state state
```

```lean
@Yulang.ProducerContextualRegular.referenceLe_trans : ∀ {Row : Type u_1} {State : Type u_2}
  {graph : Yulang.RegularValueTypes.Graph Row State} {leRow : Row → Row → Prop} {a b c : State},
  Yulang.ProducerContextualRegular.ReferenceLe graph leRow a b →
    Yulang.ProducerContextualRegular.ReferenceLe graph leRow b c →
      Yulang.ProducerContextualRegular.ReferenceLe graph leRow a c
```

```lean
@Yulang.ProducerContextualRegular.producerLe_arrow_reference_iff : ∀ {Row : Type u_1} {State : Type u_2}
  {graph : Yulang.RegularValueTypes.Graph Row State} {leRow : Row → Row → Prop},
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      ∀ (input input' output output' : State) (inputRow inputRow' outputRow outputRow' : Row),
        Yulang.ProducerContextualRegular.ProducerLe graph leRow
            (Yulang.RegularValueTypes.Layer.arrow input inputRow output outputRow)
            (Yulang.RegularValueTypes.Layer.arrow input' inputRow' output' outputRow') ↔
          Yulang.ProducerContextualRegular.ReferenceLe graph leRow input' input ∧
            leRow inputRow' inputRow ∧
              Yulang.ProducerContextualRegular.ReferenceLe graph leRow output output' ∧ leRow outputRow outputRow'
```

```lean
@Yulang.ProducerContextualRegular.producerLe_pair_reference_iff : ∀ {Row : Type u_1} {State : Type u_2}
  {graph : Yulang.RegularValueTypes.Graph Row State} {leRow : Row → Row → Prop} (a b c d : State),
  Yulang.ProducerContextualRegular.ProducerLe graph leRow (Yulang.RegularValueTypes.Layer.pair a b)
      (Yulang.RegularValueTypes.Layer.pair c d) ↔
    Yulang.ProducerContextualRegular.ReferenceLe graph leRow a c ∧
      Yulang.ProducerContextualRegular.ReferenceLe graph leRow b d
```

```lean
@Yulang.ProducerContextualRegular.producerLe_variant_reference_iff : ∀ {Row : Type u_1} {State : Type u_2}
  {graph : Yulang.RegularValueTypes.Graph Row State} {leRow : Row → Row → Prop} (label : Nat) (a b : State),
  Yulang.ProducerContextualRegular.ProducerLe graph leRow (Yulang.RegularValueTypes.Layer.variant label a)
      (Yulang.RegularValueTypes.Layer.variant label b) ↔
    Yulang.ProducerContextualRegular.ReferenceLe graph leRow a b
```

```lean
@Yulang.ProducerContextualRegular.producerLe_refl : ∀ {Row : Type u_1} {State : Type u_2}
  {graph : Yulang.RegularValueTypes.Graph Row State} {leRow : Row → Row → Prop}
  (type : Yulang.RegularValueTypes.Layer Row State), Yulang.ProducerContextualRegular.ProducerLe graph leRow type type
```

```lean
@Yulang.ProducerContextualRegular.producerLe_trans : ∀ {Row : Type u_1} {State : Type u_2}
  {graph : Yulang.RegularValueTypes.Graph Row State} {leRow : Row → Row → Prop}
  {a b c : Yulang.RegularValueTypes.Layer Row State},
  Yulang.ProducerContextualRegular.ProducerLe graph leRow a b →
    Yulang.ProducerContextualRegular.ProducerLe graph leRow b c →
      Yulang.ProducerContextualRegular.ProducerLe graph leRow a c
```

```lean
@Yulang.ProducerContextualRegular.producerEq_refl : ∀ {Row : Type u_1} {State : Type u_2}
  {graph : Yulang.RegularValueTypes.Graph Row State} {leRow : Row → Row → Prop}
  (type : Yulang.RegularValueTypes.Layer Row State), Yulang.ProducerContextualRegular.ProducerEq graph leRow type type
```

```lean
@Yulang.ProducerContextualRegular.producerEq_symm : ∀ {Row : Type u_1} {State : Type u_2}
  {graph : Yulang.RegularValueTypes.Graph Row State} {leRow : Row → Row → Prop}
  {a b : Yulang.RegularValueTypes.Layer Row State},
  Yulang.ProducerContextualRegular.ProducerEq graph leRow a b →
    Yulang.ProducerContextualRegular.ProducerEq graph leRow b a
```

```lean
@Yulang.ProducerContextualRegular.producerEq_trans : ∀ {Row : Type u_1} {State : Type u_2}
  {graph : Yulang.RegularValueTypes.Graph Row State} {leRow : Row → Row → Prop}
  {a b c : Yulang.RegularValueTypes.Layer Row State},
  Yulang.ProducerContextualRegular.ProducerEq graph leRow a b →
    Yulang.ProducerContextualRegular.ProducerEq graph leRow b c →
      Yulang.ProducerContextualRegular.ProducerEq graph leRow a c
```

```lean
@Yulang.ProducerContextualRegular.structural_subtype_preserved : ∀ {Row : Type u_1} {State : Type u_2}
  {graph : Yulang.RegularValueTypes.Graph Row State} {leRow : Row → Row → Prop},
  (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
    ∀ {source target : Yulang.RegularValueTypes.Layer Row State},
      Yulang.RegularValueTypes.Subtype graph leRow source target →
        Yulang.ProducerContextualRegular.ProducerLe graph leRow source target
```

```lean
@Yulang.ProducerContextualRegular.producerLe_union_iff : ∀ {Row : Type u_1} {State : Type u_2}
  {graph : Yulang.RegularValueTypes.Graph Row State} {leRow : Row → Row → Prop}
  (a b c : Yulang.RegularValueTypes.Layer Row State),
  Yulang.ProducerContextualRegular.ProducerLe graph leRow (a.union b) c ↔
    Yulang.ProducerContextualRegular.ProducerLe graph leRow a c ∧
      Yulang.ProducerContextualRegular.ProducerLe graph leRow b c
```

```lean
@Yulang.ProducerContextualRegular.producerLe_union_left : ∀ {Row : Type u_1} {State : Type u_2}
  {graph : Yulang.RegularValueTypes.Graph Row State} {leRow : Row → Row → Prop}
  (a b : Yulang.RegularValueTypes.Layer Row State),
  Yulang.ProducerContextualRegular.ProducerLe graph leRow a (a.union b)
```

```lean
@Yulang.ProducerContextualRegular.producerLe_union_right : ∀ {Row : Type u_1} {State : Type u_2}
  {graph : Yulang.RegularValueTypes.Graph Row State} {leRow : Row → Row → Prop}
  (a b : Yulang.RegularValueTypes.Layer Row State),
  Yulang.ProducerContextualRegular.ProducerLe graph leRow b (a.union b)
```

```lean
@Yulang.ProducerContextualRegular.producerEq_union_absorb : ∀ {Row : Type u_1} {State : Type u_2}
  {graph : Yulang.RegularValueTypes.Graph Row State} {leRow : Row → Row → Prop}
  {a b : Yulang.RegularValueTypes.Layer Row State},
  Yulang.ProducerContextualRegular.ProducerLe graph leRow a b →
    Yulang.ProducerContextualRegular.ProducerEq graph leRow (a.union b) b
```

```lean
@Yulang.ProducerContextualRegular.producerLe_inter_iff : ∀ {Row : Type u_1} {State : Type u_2}
  {graph : Yulang.RegularValueTypes.Graph Row State} {leRow : Row → Row → Prop}
  (a b c : Yulang.RegularValueTypes.Layer Row State),
  Yulang.ProducerContextualRegular.ProducerLe graph leRow a (b.inter c) ↔
    Yulang.ProducerContextualRegular.ProducerLe graph leRow a b ∧
      Yulang.ProducerContextualRegular.ProducerLe graph leRow a c
```

```lean
@Yulang.ProducerContextualRegular.producerLe_union_mono : ∀ {Row : Type u_1} {State : Type u_2}
  {graph : Yulang.RegularValueTypes.Graph Row State} {leRow : Row → Row → Prop}
  {a b c d : Yulang.RegularValueTypes.Layer Row State},
  Yulang.ProducerContextualRegular.ProducerLe graph leRow a c →
    Yulang.ProducerContextualRegular.ProducerLe graph leRow b d →
      Yulang.ProducerContextualRegular.ProducerLe graph leRow (a.union b) (c.union d)
```

```lean
@Yulang.ProducerContextualRegular.producerLe_inter_mono : ∀ {Row : Type u_1} {State : Type u_2}
  {graph : Yulang.RegularValueTypes.Graph Row State} {leRow : Row → Row → Prop}
  {a b c d : Yulang.RegularValueTypes.Layer Row State},
  Yulang.ProducerContextualRegular.ProducerLe graph leRow a c →
    Yulang.ProducerContextualRegular.ProducerLe graph leRow b d →
      Yulang.ProducerContextualRegular.ProducerLe graph leRow (a.inter b) (c.inter d)
```

```lean
@Yulang.ProducerContextualRegular.quote_observe_le : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {a b : Yulang.RegularInferenceModel.Ty Row},
  Yulang.ProducerContextualRegular.ProducerLe (Yulang.RegularInferenceModel.graph Row) leRow a b →
    ∀ (depth : Nat),
      Yulang.ProducerContextual.ProducerLe leRow
        (Yulang.RegularValueTypes.observe (Yulang.RegularInferenceModel.graph Row) depth
          (Yulang.RegularInferenceModel.State.node a))
        (Yulang.RegularValueTypes.observe (Yulang.RegularInferenceModel.graph Row) depth
          (Yulang.RegularInferenceModel.State.node b))
```

```lean
@Yulang.ProducerContextualRegular.producerLe_pair_iff : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  (a b c d : Yulang.RegularInferenceModel.Ty Row),
  Yulang.ProducerContextualRegular.ProducerLe (Yulang.RegularInferenceModel.graph Row) leRow
      (Yulang.RegularValueTypes.Layer.pair (Yulang.RegularInferenceModel.State.node a)
        (Yulang.RegularInferenceModel.State.node b))
      (Yulang.RegularValueTypes.Layer.pair (Yulang.RegularInferenceModel.State.node c)
        (Yulang.RegularInferenceModel.State.node d)) ↔
    Yulang.ProducerContextualRegular.ProducerLe (Yulang.RegularInferenceModel.graph Row) leRow a c ∧
      Yulang.ProducerContextualRegular.ProducerLe (Yulang.RegularInferenceModel.graph Row) leRow b d
```

```lean
@Yulang.ProducerContextualRegular.producerLe_variant_iff : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (label : Nat)
  (a b : Yulang.RegularInferenceModel.Ty Row),
  Yulang.ProducerContextualRegular.ProducerLe (Yulang.RegularInferenceModel.graph Row) leRow
      (Yulang.RegularValueTypes.Layer.variant label (Yulang.RegularInferenceModel.State.node a))
      (Yulang.RegularValueTypes.Layer.variant label (Yulang.RegularInferenceModel.State.node b)) ↔
    Yulang.ProducerContextualRegular.ProducerLe (Yulang.RegularInferenceModel.graph Row) leRow a b
```

```lean
@Yulang.ProducerContextualRegular.producerLe_record_mono : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (label : Nat)
  {a b rest tail : Yulang.RegularInferenceModel.Ty Row},
  Yulang.ProducerContextualRegular.ProducerLe (Yulang.RegularInferenceModel.graph Row) leRow a b →
    Yulang.ProducerContextualRegular.ProducerLe (Yulang.RegularInferenceModel.graph Row) leRow rest tail →
      Yulang.ProducerContextualRegular.ProducerLe (Yulang.RegularInferenceModel.graph Row) leRow
        (Yulang.RegularValueTypes.Layer.record label (Yulang.RegularInferenceModel.State.node a) rest)
        (Yulang.RegularValueTypes.Layer.record label (Yulang.RegularInferenceModel.State.node b) tail)
```

```lean
@Yulang.ProducerContextualRegular.producerLe_arrow : ∀ {Row : Type u_1} {leRow : Row → Row → Prop},
  (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
    ∀ {input input' output output' : Yulang.RegularInferenceModel.Ty Row}
      {inputRow inputRow' outputRow outputRow' : Row},
      Yulang.ProducerContextualRegular.ProducerLe (Yulang.RegularInferenceModel.graph Row) leRow input' input →
        leRow inputRow' inputRow →
          Yulang.ProducerContextualRegular.ProducerLe (Yulang.RegularInferenceModel.graph Row) leRow output output' →
            leRow outputRow outputRow' →
              Yulang.ProducerContextualRegular.ProducerLe (Yulang.RegularInferenceModel.graph Row) leRow
                (Yulang.RegularValueTypes.Layer.arrow (Yulang.RegularInferenceModel.State.node input) inputRow
                  (Yulang.RegularInferenceModel.State.node output) outputRow)
                (Yulang.RegularValueTypes.Layer.arrow (Yulang.RegularInferenceModel.State.node input') inputRow'
                  (Yulang.RegularInferenceModel.State.node output') outputRow')
```

```lean
@Yulang.ProducerContextualRegular.producerLe_arrow_iff : ∀ {Row : Type u_1} {leRow : Row → Row → Prop},
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      ∀ (input input' output output' : Yulang.RegularInferenceModel.Ty Row)
        (inputRow inputRow' outputRow outputRow' : Row),
        Yulang.ProducerContextualRegular.ProducerLe (Yulang.RegularInferenceModel.graph Row) leRow
            (Yulang.RegularValueTypes.Layer.arrow (Yulang.RegularInferenceModel.State.node input) inputRow
              (Yulang.RegularInferenceModel.State.node output) outputRow)
            (Yulang.RegularValueTypes.Layer.arrow (Yulang.RegularInferenceModel.State.node input') inputRow'
              (Yulang.RegularInferenceModel.State.node output') outputRow') ↔
          Yulang.ProducerContextualRegular.ProducerLe (Yulang.RegularInferenceModel.graph Row) leRow input' input ∧
            leRow inputRow' inputRow ∧
              Yulang.ProducerContextualRegular.ProducerLe (Yulang.RegularInferenceModel.graph Row) leRow output
                  output' ∧
                leRow outputRow outputRow'
```

```lean
@Yulang.ProducerContextualRegular.producerEq_pair : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {a b c d : Yulang.RegularInferenceModel.Ty Row},
  Yulang.ProducerContextualRegular.ProducerEq (Yulang.RegularInferenceModel.graph Row) leRow a c →
    Yulang.ProducerContextualRegular.ProducerEq (Yulang.RegularInferenceModel.graph Row) leRow b d →
      Yulang.ProducerContextualRegular.ProducerEq (Yulang.RegularInferenceModel.graph Row) leRow
        (Yulang.RegularValueTypes.Layer.pair (Yulang.RegularInferenceModel.State.node a)
          (Yulang.RegularInferenceModel.State.node b))
        (Yulang.RegularValueTypes.Layer.pair (Yulang.RegularInferenceModel.State.node c)
          (Yulang.RegularInferenceModel.State.node d))
```

```lean
@Yulang.ProducerContextualRegular.producerEq_variant : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (label : Nat)
  {a b : Yulang.RegularInferenceModel.Ty Row},
  Yulang.ProducerContextualRegular.ProducerEq (Yulang.RegularInferenceModel.graph Row) leRow a b →
    Yulang.ProducerContextualRegular.ProducerEq (Yulang.RegularInferenceModel.graph Row) leRow
      (Yulang.RegularValueTypes.Layer.variant label (Yulang.RegularInferenceModel.State.node a))
      (Yulang.RegularValueTypes.Layer.variant label (Yulang.RegularInferenceModel.State.node b))
```

```lean
@Yulang.ProducerContextualRegular.producerEq_record : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (label : Nat)
  {a b rest tail : Yulang.RegularInferenceModel.Ty Row},
  Yulang.ProducerContextualRegular.ProducerEq (Yulang.RegularInferenceModel.graph Row) leRow a b →
    Yulang.ProducerContextualRegular.ProducerEq (Yulang.RegularInferenceModel.graph Row) leRow rest tail →
      Yulang.ProducerContextualRegular.ProducerEq (Yulang.RegularInferenceModel.graph Row) leRow
        (Yulang.RegularValueTypes.Layer.record label (Yulang.RegularInferenceModel.State.node a) rest)
        (Yulang.RegularValueTypes.Layer.record label (Yulang.RegularInferenceModel.State.node b) tail)
```

```lean
@Yulang.ProducerContextualRegular.producerEq_arrow : ∀ {Row : Type u_1} {leRow : Row → Row → Prop},
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      ∀ {input input' output output' : Yulang.RegularInferenceModel.Ty Row} (inputRow outputRow : Row),
        Yulang.ProducerContextualRegular.ProducerEq (Yulang.RegularInferenceModel.graph Row) leRow input input' →
          Yulang.ProducerContextualRegular.ProducerEq (Yulang.RegularInferenceModel.graph Row) leRow output output' →
            Yulang.ProducerContextualRegular.ProducerEq (Yulang.RegularInferenceModel.graph Row) leRow
              (Yulang.RegularValueTypes.Layer.arrow (Yulang.RegularInferenceModel.State.node input) inputRow
                (Yulang.RegularInferenceModel.State.node output) outputRow)
              (Yulang.RegularValueTypes.Layer.arrow (Yulang.RegularInferenceModel.State.node input') inputRow
                (Yulang.RegularInferenceModel.State.node output') outputRow)
```

```lean
@Yulang.ProducerContextualRegular.quote_observe_union : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  (a b : Yulang.RegularInferenceModel.Ty Row) (depth : Nat),
  Yulang.ProducerContextual.ProducerEq leRow
    (Yulang.RegularValueTypes.observe (Yulang.RegularInferenceModel.graph Row) depth
      (Yulang.RegularInferenceModel.State.node (Yulang.RegularValueTypes.Layer.union a b)))
    ((Yulang.RegularValueTypes.observe (Yulang.RegularInferenceModel.graph Row) depth
          (Yulang.RegularInferenceModel.State.node a)).union
      (Yulang.RegularValueTypes.observe (Yulang.RegularInferenceModel.graph Row) depth
        (Yulang.RegularInferenceModel.State.node b)))
```

```lean
@Yulang.ProducerContextualRegular.pair_union_group : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  (a b c d : Yulang.RegularInferenceModel.Ty Row),
  Yulang.ProducerContextualRegular.ProducerEq (Yulang.RegularInferenceModel.graph Row) leRow
    ((Yulang.RegularValueTypes.Layer.pair (Yulang.RegularInferenceModel.State.node a)
          (Yulang.RegularInferenceModel.State.node b)).union
      (Yulang.RegularValueTypes.Layer.pair (Yulang.RegularInferenceModel.State.node c)
        (Yulang.RegularInferenceModel.State.node d)))
    (Yulang.RegularValueTypes.Layer.pair
      (Yulang.RegularInferenceModel.State.node (Yulang.RegularValueTypes.Layer.union a c))
      (Yulang.RegularInferenceModel.State.node (Yulang.RegularValueTypes.Layer.union b d)))
```

```lean
@Yulang.ProducerContextualRegular.record_union_group : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (label : Nat)
  (a rest b tail : Yulang.RegularInferenceModel.Ty Row),
  Yulang.ProducerContextualRegular.ProducerEq (Yulang.RegularInferenceModel.graph Row) leRow
    ((Yulang.RegularValueTypes.Layer.record label (Yulang.RegularInferenceModel.State.node a) rest).union
      (Yulang.RegularValueTypes.Layer.record label (Yulang.RegularInferenceModel.State.node b) tail))
    (Yulang.RegularValueTypes.Layer.record label
      (Yulang.RegularInferenceModel.State.node (Yulang.RegularValueTypes.Layer.union a b))
      (Yulang.RegularValueTypes.Layer.union rest tail))
```

```lean
@Yulang.ProducerContextualRegular.variant_union : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (label : Nat)
  (a b : Yulang.RegularInferenceModel.Ty Row),
  Yulang.ProducerContextualRegular.ProducerEq (Yulang.RegularInferenceModel.graph Row) leRow
    (Yulang.RegularValueTypes.Layer.variant label
      (Yulang.RegularInferenceModel.State.node (Yulang.RegularValueTypes.Layer.union a b)))
    ((Yulang.RegularValueTypes.Layer.variant label (Yulang.RegularInferenceModel.State.node a)).union
      (Yulang.RegularValueTypes.Layer.variant label (Yulang.RegularInferenceModel.State.node b)))
```

```lean
@Yulang.ProducerContextualRegular.legacy_instances_preserved : ∀ {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {a b : Row}, algebra.le a b → algebra.le b a → a = b) →
    ∀ (expression : Yulang.Inference.Expr),
      Yulang.SourcePrincipalInference.supported expression = true →
        ∀ (result : Yulang.Inference.Comp (Yulang.SourcePrincipalInference.model algebra)),
          Yulang.SourcePrincipalInference.Result.Instance algebra result
              (Yulang.SourcePrincipalInference.infer expression) →
            Yulang.Inference.Typing (Yulang.ProducerContextualRegular.model Row algebra.empty algebra.join algebra.le)
              [] expression result
```

```lean
@Yulang.ProducerContextualRegular.Examples.mixed_union_not_equivalent_top : ∀ {Row : Type u_1} {State : Type u_2}
  (graph : Yulang.RegularValueTypes.Graph Row State) (leRow : Row → Row → Prop),
  ¬Yulang.ProducerContextualRegular.ProducerEq graph leRow
      ((Yulang.RegularValueTypes.Layer.base Yulang.Inference.Base.int).union
        (Yulang.RegularValueTypes.Layer.base Yulang.Inference.Base.str))
      Yulang.RegularValueTypes.Layer.top
```

</details>

## CoreProducerContextualInstances

任意の旧結果と全自由 parameter を同じ evaluator で評価し、旧 instance を保存し、新 instance を同じ行の要求同値な旧 instance へ反映する。独立 Typing の逆向きは後の source 接続を参照。

<details>
<summary>9 個の公開定理の完全な型</summary>

```lean
@Yulang.Core.ProducerContextualInstances.legacy_instances_preserved : ∀ {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row) (result : Yulang.SourcePrincipalInference.Result)
  (target : Yulang.Core.ProducerLegacyInstances.Computation Row),
  Yulang.SourcePrincipalInference.Result.Instance algebra target result →
    Yulang.Core.ProducerContextualInstances.Instance algebra result target
```

```lean
@Yulang.Core.ProducerContextualInstances.legacy_instances_reflected : ∀ {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row) (result : Yulang.SourcePrincipalInference.Result)
  (target : Yulang.Core.ProducerLegacyInstances.Computation Row),
  Yulang.Core.ProducerContextualInstances.Instance algebra result target →
    ∃ oldValue,
      Yulang.SourcePrincipalInference.Result.Instance algebra (oldValue, target.snd) result ∧
        Yulang.Core.ProducerContextualInstances.Equivalent algebra oldValue target.fst
```

```lean
@Yulang.Core.ProducerContextualInstances.legacy_instances_exact_modulo : ∀ {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row) (result : Yulang.SourcePrincipalInference.Result)
  (target : Yulang.Core.ProducerLegacyInstances.Computation Row),
  Yulang.Core.ProducerContextualInstances.Instance algebra result target ↔
    ∃ oldValue,
      Yulang.SourcePrincipalInference.Result.Instance algebra (oldValue, target.snd) result ∧
        Yulang.Core.ProducerContextualInstances.Equivalent algebra oldValue target.fst
```

```lean
@Yulang.Core.ProducerContextualInstances.source_instances_exact_modulo : ∀ {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {a b : Row}, algebra.le a b → algebra.le b a → a = b) →
    ∀ (expression : Yulang.Inference.Expr),
      Yulang.SourcePrincipalInference.supported expression = true →
        ∀ (target : Yulang.Core.ProducerLegacyInstances.Computation Row),
          Yulang.Core.ProducerContextualInstances.Instance algebra (Yulang.SourcePrincipalInference.infer expression)
              target ↔
            ∃ oldValue,
              Yulang.Inference.Typing (Yulang.SourcePrincipalInference.model algebra) [] expression
                  (oldValue, target.snd) ∧
                Yulang.Core.ProducerContextualInstances.Equivalent algebra oldValue target.fst
```

```lean
@Yulang.Core.ProducerContextualInstances.source_instances_sound : ∀ {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {a b : Row}, algebra.le a b → algebra.le b a → a = b) →
    ∀ (expression : Yulang.Inference.Expr),
      Yulang.SourcePrincipalInference.supported expression = true →
        ∀ (target : Yulang.Core.ProducerLegacyInstances.Computation Row),
          Yulang.Core.ProducerContextualInstances.Instance algebra (Yulang.SourcePrincipalInference.infer expression)
              target →
            Yulang.Inference.Typing (Yulang.ProducerContextualRegular.model Row algebra.empty algebra.join algebra.le)
              [] expression target
```

```lean
@Yulang.Core.ProducerContextualInstances.unsupported_has_no_instance : ∀ {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row) (target : Yulang.Core.ProducerLegacyInstances.Computation Row),
  ¬Yulang.Core.ProducerContextualInstances.Instance algebra Yulang.SourcePrincipalInference.Result.unsupported target
```

```lean
@Yulang.Core.ProducerContextualInstances.rejected_has_no_instance : ∀ {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row) (target : Yulang.Core.ProducerLegacyInstances.Computation Row),
  ¬Yulang.Core.ProducerContextualInstances.Instance algebra Yulang.SourcePrincipalInference.Result.rejected target
```

```lean
@Yulang.Core.ProducerContextualInstances.DistributionExample.factorised_equivalent_distributed : ∀ {Row : Type u_1}
  (leRow : Row → Row → Prop),
  Yulang.ProducerContextualRegular.ProducerEq (Yulang.RegularInferenceModel.graph Row) leRow
    Yulang.Core.PresenceLegacyObstructions.factorised Yulang.Core.PresenceLegacyObstructions.distributed
```

```lean
@Yulang.Core.ProducerContextualInstances.DistributionExample.distributed_instance : ∀ {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {a b : Row}, algebra.le a b → algebra.le b a → a = b) →
    Yulang.Core.ProducerContextualInstances.Instance algebra
        (Yulang.SourcePrincipalInference.infer Yulang.Core.PresenceLegacyObstructions.source)
        (Yulang.Core.PresenceLegacyObstructions.distributed, algebra.empty) ∧
      ¬Yulang.SourcePrincipalInference.Result.Instance algebra
          (Yulang.Core.PresenceLegacyObstructions.distributed, algebra.empty)
          (Yulang.SourcePrincipalInference.infer Yulang.Core.PresenceLegacyObstructions.source)
```

</details>

## PositiveEquationElimination

全座標を含む有限列、任意の正方程式・atom 命題割当てで、全自由 parameter から不動点を構成し、任意独立不動点を回収する。反復数は容量から決まり、成功・fuel を前提にしない。

<details>
<summary>20 個の公開定理の完全な型</summary>

```lean
@Yulang.PositiveEquationElimination.iterate_zero : ∀ {Value : Type} (step : Value → Value) (value : Value),
  Yulang.PositiveEquationElimination.iterate step 0 value = value
```

```lean
@Yulang.PositiveEquationElimination.iterate_succ : ∀ {Value : Type} (step : Value → Value) (capacity : Nat)
  (value : Value),
  Yulang.PositiveEquationElimination.iterate step (capacity + 1) value =
    Yulang.PositiveEquationElimination.iterate step capacity (step value)
```

```lean
@Yulang.PositiveEquationElimination.iterate_fixed : ∀ {Value : Type} (step : Value → Value) (value : Value),
  step value = value → ∀ (capacity : Nat), Yulang.PositiveEquationElimination.iterate step capacity value = value
```

```lean
@Yulang.PositiveEquationElimination.inflationary_stabilizes : ∀ {Index : Type} (coordinates : List Index),
  (∀ (index : Index), index ∈ coordinates) →
    ∀ (step : Yulang.PositiveEquationElimination.Valuation Index → Yulang.PositiveEquationElimination.Valuation Index),
      (∀ (value : Yulang.PositiveEquationElimination.Valuation Index),
          Yulang.PositiveEquationElimination.Below value (step value)) →
        ∀ (initial : Yulang.PositiveEquationElimination.Valuation Index),
          step (Yulang.PositiveEquationElimination.iterate step coordinates.length initial) =
            Yulang.PositiveEquationElimination.iterate step coordinates.length initial
```

```lean
@Yulang.PositiveEquationElimination.deflationary_stabilizes : ∀ {Index : Type} (coordinates : List Index),
  (∀ (index : Index), index ∈ coordinates) →
    ∀ (step : Yulang.PositiveEquationElimination.Valuation Index → Yulang.PositiveEquationElimination.Valuation Index),
      (∀ (value : Yulang.PositiveEquationElimination.Valuation Index),
          Yulang.PositiveEquationElimination.Below (step value) value) →
        ∀ (initial : Yulang.PositiveEquationElimination.Valuation Index),
          step (Yulang.PositiveEquationElimination.iterate step coordinates.length initial) =
            Yulang.PositiveEquationElimination.iterate step coordinates.length initial
```

```lean
@Yulang.PositiveEquationElimination.descend_prefixpoint : ∀ {Index : Type}
  (step : Yulang.PositiveEquationElimination.Valuation Index → Yulang.PositiveEquationElimination.Valuation Index),
  Yulang.PositiveEquationElimination.Monotone step →
    ∀ (value : Yulang.PositiveEquationElimination.Valuation Index),
      Yulang.PositiveEquationElimination.Below (step value) value →
        Yulang.PositiveEquationElimination.Below (step (Yulang.PositiveEquationElimination.descend step value))
          (Yulang.PositiveEquationElimination.descend step value)
```

```lean
@Yulang.PositiveEquationElimination.descend_iterate_prefixpoint : ∀ {Index : Type}
  (step : Yulang.PositiveEquationElimination.Valuation Index → Yulang.PositiveEquationElimination.Valuation Index),
  Yulang.PositiveEquationElimination.Monotone step →
    ∀ (capacity : Nat) (value : Yulang.PositiveEquationElimination.Valuation Index),
      Yulang.PositiveEquationElimination.Below (step value) value →
        Yulang.PositiveEquationElimination.Below
          (step
            (Yulang.PositiveEquationElimination.iterate (Yulang.PositiveEquationElimination.descend step) capacity
              value))
          (Yulang.PositiveEquationElimination.iterate (Yulang.PositiveEquationElimination.descend step) capacity value)
```

```lean
@Yulang.PositiveEquationElimination.project_sound : ∀ {Index : Type} (coordinates : List Index),
  (∀ (index : Index), index ∈ coordinates) →
    ∀ (step : Yulang.PositiveEquationElimination.Valuation Index → Yulang.PositiveEquationElimination.Valuation Index),
      Yulang.PositiveEquationElimination.Monotone step →
        ∀ (parameter : Yulang.PositiveEquationElimination.Valuation Index),
          step (Yulang.PositiveEquationElimination.project coordinates step parameter) =
            Yulang.PositiveEquationElimination.project coordinates step parameter
```

```lean
@Yulang.PositiveEquationElimination.project_retract : ∀ {Index : Type} (coordinates : List Index)
  (step : Yulang.PositiveEquationElimination.Valuation Index → Yulang.PositiveEquationElimination.Valuation Index)
  (solution : Yulang.PositiveEquationElimination.Valuation Index),
  step solution = solution → Yulang.PositiveEquationElimination.project coordinates step solution = solution
```

```lean
@Yulang.PositiveEquationElimination.Formula.eval_bind : ∀ {Index Atom Target : Type}
  (formula : Yulang.PositiveEquationElimination.Formula Index Atom)
  (variables : Index → Yulang.PositiveEquationElimination.Formula Target Atom)
  (atoms : Yulang.PositiveEquationElimination.Valuation Atom)
  (parameters : Yulang.PositiveEquationElimination.Valuation Target),
  Yulang.PositiveEquationElimination.Formula.eval atoms parameters
      (Yulang.PositiveEquationElimination.Formula.bind variables formula) =
    Yulang.PositiveEquationElimination.Formula.eval atoms
      (fun index => Yulang.PositiveEquationElimination.Formula.eval atoms parameters (variables index)) formula
```

```lean
@Yulang.PositiveEquationElimination.Formula.eval_monotone : ∀ {Index Atom : Type}
  (formula : Yulang.PositiveEquationElimination.Formula Index Atom)
  (atoms : Yulang.PositiveEquationElimination.Valuation Atom)
  (left right : Yulang.PositiveEquationElimination.Valuation Index),
  Yulang.PositiveEquationElimination.Below left right →
    Yulang.PositiveEquationElimination.Formula.eval atoms left formula →
      Yulang.PositiveEquationElimination.Formula.eval atoms right formula
```

```lean
@Yulang.PositiveEquationElimination.evaluate_monotone : ∀ {Index Atom : Type}
  (system : Yulang.PositiveEquationElimination.System Index Atom)
  (atoms : Yulang.PositiveEquationElimination.Valuation Atom),
  Yulang.PositiveEquationElimination.Monotone (Yulang.PositiveEquationElimination.evaluate system atoms)
```

```lean
@Yulang.PositiveEquationElimination.evaluate_ascend : ∀ {Index Atom : Type}
  (system value : Yulang.PositiveEquationElimination.System Index Atom)
  (atoms : Yulang.PositiveEquationElimination.Valuation Atom)
  (parameters : Yulang.PositiveEquationElimination.Valuation Index),
  Yulang.PositiveEquationElimination.evaluate (Yulang.PositiveEquationElimination.ascendFormula system value) atoms
      parameters =
    Yulang.PositiveEquationElimination.ascend (Yulang.PositiveEquationElimination.evaluate system atoms)
      (Yulang.PositiveEquationElimination.evaluate value atoms parameters)
```

```lean
@Yulang.PositiveEquationElimination.evaluate_descend : ∀ {Index Atom : Type}
  (system value : Yulang.PositiveEquationElimination.System Index Atom)
  (atoms : Yulang.PositiveEquationElimination.Valuation Atom)
  (parameters : Yulang.PositiveEquationElimination.Valuation Index),
  Yulang.PositiveEquationElimination.evaluate (Yulang.PositiveEquationElimination.descendFormula system value) atoms
      parameters =
    Yulang.PositiveEquationElimination.descend (Yulang.PositiveEquationElimination.evaluate system atoms)
      (Yulang.PositiveEquationElimination.evaluate value atoms parameters)
```

```lean
@Yulang.PositiveEquationElimination.iterate_commute : ∀ {Left Right : Type} (leftStep : Left → Left)
  (rightStep : Right → Right) (map : Left → Right),
  (∀ (value : Left), map (leftStep value) = rightStep (map value)) →
    ∀ (capacity : Nat) (value : Left),
      map (Yulang.PositiveEquationElimination.iterate leftStep capacity value) =
        Yulang.PositiveEquationElimination.iterate rightStep capacity (map value)
```

```lean
@Yulang.PositiveEquationElimination.project_natural : ∀ {Index : Type} (coordinates : List Index)
  (indexMap : Index → Index)
  (leftStep rightStep :
    Yulang.PositiveEquationElimination.Valuation Index → Yulang.PositiveEquationElimination.Valuation Index),
  (∀ (value : Yulang.PositiveEquationElimination.Valuation Index),
      Yulang.PositiveEquationElimination.pullback indexMap (leftStep value) =
        rightStep (Yulang.PositiveEquationElimination.pullback indexMap value)) →
    ∀ (parameters : Yulang.PositiveEquationElimination.Valuation Index),
      Yulang.PositiveEquationElimination.pullback indexMap
          (Yulang.PositiveEquationElimination.project coordinates leftStep parameters) =
        Yulang.PositiveEquationElimination.project coordinates rightStep
          (Yulang.PositiveEquationElimination.pullback indexMap parameters)
```

```lean
@Yulang.PositiveEquationElimination.evaluate_solve : ∀ {Index Atom : Type} (coordinates : List Index)
  (system : Yulang.PositiveEquationElimination.System Index Atom)
  (atoms : Yulang.PositiveEquationElimination.Valuation Atom)
  (parameters : Yulang.PositiveEquationElimination.Valuation Index),
  Yulang.PositiveEquationElimination.evaluate (Yulang.PositiveEquationElimination.solve coordinates system) atoms
      parameters =
    Yulang.PositiveEquationElimination.project coordinates (Yulang.PositiveEquationElimination.evaluate system atoms)
      parameters
```

```lean
@Yulang.PositiveEquationElimination.solve_sound : ∀ {Index Atom : Type} (coordinates : List Index),
  (∀ (index : Index), index ∈ coordinates) →
    ∀ (system : Yulang.PositiveEquationElimination.System Index Atom)
      (atoms : Yulang.PositiveEquationElimination.Valuation Atom)
      (parameters : Yulang.PositiveEquationElimination.Valuation Index),
      Yulang.PositiveEquationElimination.evaluate system atoms
          (Yulang.PositiveEquationElimination.evaluate (Yulang.PositiveEquationElimination.solve coordinates system)
            atoms parameters) =
        Yulang.PositiveEquationElimination.evaluate (Yulang.PositiveEquationElimination.solve coordinates system) atoms
          parameters
```

```lean
@Yulang.PositiveEquationElimination.solve_retract : ∀ {Index Atom : Type} (coordinates : List Index)
  (system : Yulang.PositiveEquationElimination.System Index Atom)
  (atoms : Yulang.PositiveEquationElimination.Valuation Atom)
  (solution : Yulang.PositiveEquationElimination.Valuation Index),
  Yulang.PositiveEquationElimination.evaluate system atoms solution = solution →
    Yulang.PositiveEquationElimination.evaluate (Yulang.PositiveEquationElimination.solve coordinates system) atoms
        solution =
      solution
```

```lean
@Yulang.PositiveEquationElimination.solved_instances_exact : ∀ {Index Atom : Type} (coordinates : List Index),
  (∀ (index : Index), index ∈ coordinates) →
    ∀ (system : Yulang.PositiveEquationElimination.System Index Atom)
      (atoms : Yulang.PositiveEquationElimination.Valuation Atom)
      (value : Yulang.PositiveEquationElimination.Valuation Index),
      Yulang.PositiveEquationElimination.evaluate system atoms value = value ↔
        ∃ parameters,
          Yulang.PositiveEquationElimination.evaluate (Yulang.PositiveEquationElimination.solve coordinates system)
              atoms parameters =
            value
```

</details>

## MethodResolutionCost

任意の既存 selection 入力で同じ三状態結果を返す計数付き実装と、候補数・型 node 数による費用上界。費用単位は元 module 冒頭に記す。

<details>
<summary>19 個の公開定理の完全な型</summary>

```lean
@Yulang.MethodResolutionCost.allEqualCount_value : ∀ {α : Type u_1} [inst : DecidableEq α] (expected : α)
  (members : List α),
  (Yulang.MethodResolutionCost.allEqualCount expected members).fst = Yulang.Methods.AllEqual members expected
```

```lean
@Yulang.MethodResolutionCost.allEqualCount_bound : ∀ {α : Type u_1} [inst : DecidableEq α] (expected : α)
  (members : List α), (Yulang.MethodResolutionCost.allEqualCount expected members).snd ≤ members.length
```

```lean
@Yulang.MethodResolutionCost.selectCount_value : ∀ {α : Type u_1} [inst : DecidableEq α] (members : List α),
  (Yulang.MethodResolutionCost.selectCount members).fst = Yulang.Methods.select members
```

```lean
@Yulang.MethodResolutionCost.selectCount_bound : ∀ {α : Type u_1} [inst : DecidableEq α] (members : List α),
  (Yulang.MethodResolutionCost.selectCount members).snd ≤ members.length
```

```lean
Yulang.MethodResolutionCost.candidatesCount_value : ∀ (scope : Yulang.MethodResolution.Scope) (name : Nat)
  (roles : List Nat),
  (Yulang.MethodResolutionCost.candidatesCount scope name roles).fst =
    List.filterMap (fun role => Option.map (fun x => (role, x)) (scope.methodRef role name)) roles
```

```lean
Yulang.MethodResolutionCost.candidatesCount_steps : ∀ (scope : Yulang.MethodResolution.Scope) (name : Nat)
  (roles : List Nat), (Yulang.MethodResolutionCost.candidatesCount scope name roles).snd = roles.length
```

```lean
Yulang.MethodResolutionCost.candidatesCount_length : ∀ (scope : Yulang.MethodResolution.Scope) (name : Nat)
  (roles : List Nat), (Yulang.MethodResolutionCost.candidatesCount scope name roles).fst.length ≤ roles.length
```

```lean
Yulang.MethodResolutionCost.unknownCount_value : ∀ (scope : Yulang.MethodResolution.Scope) (name : Nat),
  (Yulang.MethodResolutionCost.unknownCount scope name).fst = Yulang.MethodResolution.unknown scope name
```

```lean
Yulang.MethodResolutionCost.unknownCount_bound : ∀ (scope : Yulang.MethodResolution.Scope) (name : Nat),
  (Yulang.MethodResolutionCost.unknownCount scope name).snd ≤ 1 + 2 * scope.visibleRoles.length
```

```lean
@Yulang.MethodResolutionCost.lookupCount_value : ∀ {Row : Type} (name : Nat) (type : Yulang.StructuralBase.Ty Row),
  (Yulang.MethodResolutionCost.lookupCount name type).fst = Yulang.StructuralBase.Ty.lookup name type
```

```lean
@Yulang.MethodResolutionCost.lookupCount_bound : ∀ {Row : Type} (name : Nat) (type : Yulang.StructuralBase.Ty Row),
  (Yulang.MethodResolutionCost.lookupCount name type).snd ≤ Yulang.MethodResolutionCost.typeNodes type
```

```lean
@Yulang.MethodResolutionCost.knownCount_value : ∀ {Row : Type} (receiver : Yulang.StructuralBase.Ty Row) (name : Nat)
  (fallback : Yulang.Methods.Selection Nat),
  (Yulang.MethodResolutionCost.knownCount receiver name fallback).fst =
    Yulang.MethodResolution.known receiver name fallback
```

```lean
@Yulang.MethodResolutionCost.knownCount_bound : ∀ {Row : Type} (receiver : Yulang.StructuralBase.Ty Row) (name : Nat)
  (fallback : Yulang.Methods.Selection Nat),
  (Yulang.MethodResolutionCost.knownCount receiver name fallback).snd ≤
    1 + Yulang.MethodResolutionCost.typeNodes receiver
```

```lean
@Yulang.MethodResolutionCost.resolveCount_value : ∀ {Row : Type} (site : Yulang.MethodResolution.Site Row),
  (Yulang.MethodResolutionCost.resolveCount site).fst = Yulang.MethodResolution.resolve site
```

```lean
@Yulang.MethodResolutionCost.resolveCount_bound : ∀ {Row : Type} (site : Yulang.MethodResolution.Site Row),
  (Yulang.MethodResolutionCost.resolveCount site).snd ≤ Yulang.MethodResolutionCost.siteBound site
```

```lean
@Yulang.MethodResolutionCost.runCount_value : ∀ {Row : Type} {SiteId : Type u_1} [inst : DecidableEq SiteId]
  (sites : SiteId → Yulang.MethodResolution.Site Row) (order : List SiteId)
  (answers : Yulang.MethodResolutionLocality.Answers SiteId),
  (Yulang.MethodResolutionCost.runCount sites order answers).fst =
    Yulang.MethodResolutionLocality.run sites order answers
```

```lean
@Yulang.MethodResolutionCost.runCount_steps : ∀ {Row : Type} {SiteId : Type u_1} [inst : DecidableEq SiteId]
  (sites : SiteId → Yulang.MethodResolution.Site Row) (order : List SiteId)
  (answers : Yulang.MethodResolutionLocality.Answers SiteId),
  (Yulang.MethodResolutionCost.runCount sites order answers).snd =
    (List.map (fun site => (Yulang.MethodResolutionCost.resolveCount (sites site)).snd) order).sum
```

```lean
@Yulang.MethodResolutionCost.runCount_bound : ∀ {Row : Type} {SiteId : Type u_1} [inst : DecidableEq SiteId]
  (sites : SiteId → Yulang.MethodResolution.Site Row) (order : List SiteId)
  (answers : Yulang.MethodResolutionLocality.Answers SiteId),
  (Yulang.MethodResolutionCost.runCount sites order answers).snd ≤
    (List.map (fun site => Yulang.MethodResolutionCost.siteBound (sites site)) order).sum
```

```lean
@Yulang.MethodResolutionCost.runCount_uniform_bound : ∀ {Row : Type} {SiteId : Type u_1} [inst : DecidableEq SiteId]
  (sites : SiteId → Yulang.MethodResolution.Site Row) (order : List SiteId)
  (answers : Yulang.MethodResolutionLocality.Answers SiteId) (bound : Nat),
  (∀ (site : SiteId), site ∈ order → Yulang.MethodResolutionCost.siteBound (sites site) ≤ bound) →
    (Yulang.MethodResolutionCost.runCount sites order answers).snd ≤ order.length * bound
```

</details>

## MethodResolutionIndex

有限 catalog の同じ role/name が同じ declaration を表す関数性の下で、実 index は既存 resolver と一致する。重複と順序を扱い、上界自体には関数性も成功も仮定しない。

<details>
<summary>21 個の公開定理の完全な型</summary>

```lean
@Yulang.MethodResolutionIndex.insertCount_bound : ∀ {α : Type u_1} [inst : DecidableEq α] (candidate : α)
  (summary : Yulang.Methods.Selection α), (Yulang.MethodResolutionIndex.insertCount candidate summary).snd ≤ 1
```

```lean
@Yulang.MethodResolutionIndex.insert_select : ∀ {α : Type u_1} [inst : DecidableEq α] (candidate : α)
  (members : List α),
  Yulang.MethodResolutionIndex.insert candidate (Yulang.Methods.select members) =
    Yulang.Methods.select (candidate :: members)
```

```lean
Yulang.MethodResolutionIndex.mem_namedCandidates : ∀ (entries : List Yulang.MethodResolutionIndex.Entry) (name : Nat)
  (candidate : Nat × Nat),
  candidate ∈ Yulang.MethodResolutionIndex.namedCandidates entries name ↔
    ∃ entry, entry ∈ entries ∧ entry.name = name ∧ (entry.role, entry.declaration) = candidate
```

```lean
Yulang.MethodResolutionIndex.buildIndex_exact : ∀ (entries : List Yulang.MethodResolutionIndex.Entry) (name : Nat),
  Yulang.MethodResolutionIndex.buildIndex entries name =
    Yulang.Methods.select (Yulang.MethodResolutionIndex.namedCandidates entries name)
```

```lean
Yulang.MethodResolutionIndex.buildIndex_ext : ∀ (left right : List Yulang.MethodResolutionIndex.Entry),
  (∀ (entry : Yulang.MethodResolutionIndex.Entry), entry ∈ left ↔ entry ∈ right) →
    Yulang.MethodResolutionIndex.buildIndex left = Yulang.MethodResolutionIndex.buildIndex right
```

```lean
Yulang.MethodResolutionIndex.buildIndex_perm : ∀ (left right : List Yulang.MethodResolutionIndex.Entry),
  left.Perm right → Yulang.MethodResolutionIndex.buildIndex left = Yulang.MethodResolutionIndex.buildIndex right
```

```lean
Yulang.MethodResolutionIndex.lookupRef_sound : ∀ (entries : List Yulang.MethodResolutionIndex.Entry)
  (role name declaration : Nat),
  Yulang.MethodResolutionIndex.lookupRef entries role name = some declaration →
    ∃ entry, entry ∈ entries ∧ entry.role = role ∧ entry.name = name ∧ entry.declaration = declaration
```

```lean
Yulang.MethodResolutionIndex.lookupRef_complete : ∀ (entries : List Yulang.MethodResolutionIndex.Entry),
  Yulang.MethodResolutionIndex.Functional entries →
    ∀ (entry : Yulang.MethodResolutionIndex.Entry),
      entry ∈ entries → Yulang.MethodResolutionIndex.lookupRef entries entry.role entry.name = some entry.declaration
```

```lean
Yulang.MethodResolutionIndex.catalog_candidates_exact : ∀ (entries : List Yulang.MethodResolutionIndex.Entry)
  (visible : List Nat),
  Yulang.MethodResolutionIndex.Functional entries →
    ∀ (name role declaration : Nat),
      (role, declaration) ∈
          Yulang.MethodResolutionIndex.namedCandidates (Yulang.MethodResolutionIndex.visibleEntries entries visible)
            name ↔
        Yulang.MethodResolution.Candidate (Yulang.MethodResolutionIndex.catalogScope entries visible) name role
          declaration
```

```lean
Yulang.MethodResolutionIndex.indexedUnknown_exact : ∀ (entries : List Yulang.MethodResolutionIndex.Entry)
  (visible : List Nat),
  Yulang.MethodResolutionIndex.Functional entries →
    ∀ (name : Nat),
      Yulang.MethodResolutionIndex.indexedUnknown
          (Yulang.MethodResolutionIndex.buildIndex (Yulang.MethodResolutionIndex.visibleEntries entries visible)) name =
        Yulang.MethodResolution.unknown (Yulang.MethodResolutionIndex.catalogScope entries visible) name
```

```lean
@Yulang.MethodResolutionIndex.indexedResolve_exact : ∀ {Row : Type} (entries : List Yulang.MethodResolutionIndex.Entry)
  (visible : List Nat),
  Yulang.MethodResolutionIndex.Functional entries →
    ∀ (name : Nat) (receiver : Option (Yulang.StructuralBase.Ty Row)) (fallback : Yulang.Methods.Selection Nat),
      Yulang.MethodResolutionIndex.indexedResolve
          (Yulang.MethodResolutionIndex.buildIndex (Yulang.MethodResolutionIndex.visibleEntries entries visible))
          { name := name, scope := Yulang.MethodResolutionIndex.catalogScope entries visible, receiver := receiver,
            typedFallback := fallback } =
        Yulang.MethodResolution.resolve
          { name := name, scope := Yulang.MethodResolutionIndex.catalogScope entries visible, receiver := receiver,
            typedFallback := fallback }
```

```lean
Yulang.MethodResolutionIndex.addEntryCount_value : ∀ (entry : Yulang.MethodResolutionIndex.Entry)
  (index : Yulang.MethodResolutionIndex.Index),
  (Yulang.MethodResolutionIndex.addEntryCount entry index).fst = Yulang.MethodResolutionIndex.addEntry entry index
```

```lean
Yulang.MethodResolutionIndex.addEntryCount_bound : ∀ (entry : Yulang.MethodResolutionIndex.Entry)
  (index : Yulang.MethodResolutionIndex.Index), (Yulang.MethodResolutionIndex.addEntryCount entry index).snd ≤ 3
```

```lean
Yulang.MethodResolutionIndex.buildIndexCount_value : ∀ (entries : List Yulang.MethodResolutionIndex.Entry),
  (Yulang.MethodResolutionIndex.buildIndexCount entries).fst = Yulang.MethodResolutionIndex.buildIndex entries
```

```lean
Yulang.MethodResolutionIndex.buildIndexCount_bound : ∀ (entries : List Yulang.MethodResolutionIndex.Entry),
  (Yulang.MethodResolutionIndex.buildIndexCount entries).snd ≤ 3 * entries.length
```

```lean
Yulang.MethodResolutionIndex.indexedUnknownCount_value : ∀ (index : Yulang.MethodResolutionIndex.Index) (name : Nat),
  (Yulang.MethodResolutionIndex.indexedUnknownCount index name).fst =
    Yulang.MethodResolutionIndex.indexedUnknown index name
```

```lean
Yulang.MethodResolutionIndex.indexedUnknownCount_steps : ∀ (index : Yulang.MethodResolutionIndex.Index) (name : Nat),
  (Yulang.MethodResolutionIndex.indexedUnknownCount index name).snd = 2
```

```lean
Yulang.MethodResolutionIndex.queryNamesCount_value : ∀ (index : Yulang.MethodResolutionIndex.Index) (names : List Nat),
  (Yulang.MethodResolutionIndex.queryNamesCount index names).fst =
    List.map (Yulang.MethodResolutionIndex.indexedUnknown index) names
```

```lean
Yulang.MethodResolutionIndex.queryNamesCount_steps : ∀ (index : Yulang.MethodResolutionIndex.Index) (names : List Nat),
  (Yulang.MethodResolutionIndex.queryNamesCount index names).snd = 2 * names.length
```

```lean
Yulang.MethodResolutionIndex.resolveNamesCount_exact : ∀ (entries : List Yulang.MethodResolutionIndex.Entry)
  (visible : List Nat),
  Yulang.MethodResolutionIndex.Functional entries →
    ∀ (names : List Nat),
      (Yulang.MethodResolutionIndex.resolveNamesCount (Yulang.MethodResolutionIndex.visibleEntries entries visible)
            names).fst =
        List.map (Yulang.MethodResolution.unknown (Yulang.MethodResolutionIndex.catalogScope entries visible)) names
```

```lean
Yulang.MethodResolutionIndex.resolveNamesCount_bound : ∀ (entries : List Yulang.MethodResolutionIndex.Entry)
  (names : List Nat),
  (Yulang.MethodResolutionIndex.resolveNamesCount entries names).snd ≤ 3 * entries.length + 2 * names.length
```

</details>

## InferenceSubstitutionCost

任意の型項・行項・formula substitution を実計数し、既存関数と値を一致させる。具体化の上界は全 node 数、binder 深さ、置換先の両成分サイズによる。

<details>
<summary>15 個の公開定理の完全な型</summary>

```lean
@Yulang.InferenceSubstitutionCost.rowNodes_rename : ∀ {α β : Type} (term : Yulang.Inference.RowTerm α) (rename : α → β),
  Yulang.InferenceSubstitutionCost.rowNodes (Yulang.Inference.RowTerm.rename rename term) =
    Yulang.InferenceSubstitutionCost.rowNodes term
```

```lean
@Yulang.InferenceSubstitutionCost.tyNodes_rename : ∀ {α β : Type} (term : Yulang.Inference.TyTerm α) (rename : α → β),
  Yulang.InferenceSubstitutionCost.tyNodes (Yulang.Inference.TyTerm.rename rename term) =
    Yulang.InferenceSubstitutionCost.tyNodes term
```

```lean
@Yulang.InferenceSubstitutionCost.compNodes_rename : ∀ {α β : Type} (term : Yulang.Inference.CompTerm α)
  (rename : α → β),
  Yulang.InferenceSubstitutionCost.compNodes (Yulang.Inference.CompTerm.rename rename term) =
    Yulang.InferenceSubstitutionCost.compNodes term
```

```lean
@Yulang.InferenceSubstitutionCost.rowSubst_value : ∀ {α β : Type} (replacement : α → Yulang.Inference.CompTerm β × Nat)
  (term : Yulang.Inference.RowTerm α),
  (Yulang.InferenceSubstitutionCost.rowSubst replacement term).fst =
    Yulang.Inference.RowTerm.subst (fun index => (replacement index).fst) term
```

```lean
@Yulang.InferenceSubstitutionCost.tySubst_value : ∀ {α β : Type} (replacement : α → Yulang.Inference.CompTerm β × Nat)
  (term : Yulang.Inference.TyTerm α),
  (Yulang.InferenceSubstitutionCost.tySubst replacement term).fst =
    Yulang.Inference.TyTerm.subst (fun index => (replacement index).fst) term
```

```lean
@Yulang.InferenceSubstitutionCost.rowSubst_bound : ∀ {α β : Type} (replacement : α → Yulang.Inference.CompTerm β × Nat)
  (cost : Nat),
  (∀ (index : α), (replacement index).snd ≤ cost) →
    ∀ (term : Yulang.Inference.RowTerm α),
      (Yulang.InferenceSubstitutionCost.rowSubst replacement term).snd ≤
        Yulang.InferenceSubstitutionCost.rowNodes term * (cost + 1)
```

```lean
@Yulang.InferenceSubstitutionCost.tySubst_bound : ∀ {α β : Type} (replacement : α → Yulang.Inference.CompTerm β × Nat)
  (cost : Nat),
  (∀ (index : α), (replacement index).snd ≤ cost) →
    ∀ (term : Yulang.Inference.TyTerm α),
      (Yulang.InferenceSubstitutionCost.tySubst replacement term).snd ≤
        Yulang.InferenceSubstitutionCost.tyNodes term * (cost + 1)
```

```lean
@Yulang.InferenceSubstitutionCost.lift_value : ∀ {α : Type u_1} {β : Type}
  (replacement : α → Yulang.Inference.CompTerm β × Nat),
  (fun index => (Yulang.InferenceSubstitutionCost.lift replacement index).fst) =
    Yulang.Inference.liftSubst fun index => (replacement index).fst
```

```lean
@Yulang.InferenceSubstitutionCost.lift_bounds : ∀ {α : Type u_1} {β : Type}
  (replacement : α → Yulang.Inference.CompTerm β × Nat) (size cost : Nat),
  2 ≤ size →
    (∀ (index : α), Yulang.InferenceSubstitutionCost.compNodes (replacement index).fst ≤ size) →
      (∀ (index : α), (replacement index).snd ≤ cost) →
        (∀ (index : Option α),
            Yulang.InferenceSubstitutionCost.compNodes (Yulang.InferenceSubstitutionCost.lift replacement index).fst ≤
              size) ∧
          ∀ (index : Option α), (Yulang.InferenceSubstitutionCost.lift replacement index).snd ≤ cost + size
```

```lean
@Yulang.InferenceSubstitutionCost.formulaSubst_value : ∀ {α β : Type}
  (replacement : α → Yulang.Inference.CompTerm β × Nat) (formula : Yulang.Inference.Formula α),
  (Yulang.InferenceSubstitutionCost.formulaSubst replacement formula).fst =
    Yulang.Inference.Formula.subst (fun index => (replacement index).fst) formula
```

```lean
@Yulang.InferenceSubstitutionCost.formulaSubst_bound : ∀ {α β : Type}
  (replacement : α → Yulang.Inference.CompTerm β × Nat) (size cost : Nat),
  2 ≤ size →
    (∀ (index : α), Yulang.InferenceSubstitutionCost.compNodes (replacement index).fst ≤ size) →
      (∀ (index : α), (replacement index).snd ≤ cost) →
        ∀ (formula : Yulang.Inference.Formula α),
          (Yulang.InferenceSubstitutionCost.formulaSubst replacement formula).snd ≤
            Yulang.InferenceSubstitutionCost.formulaNodes formula *
              (cost + size * Yulang.InferenceSubstitutionCost.binderDepth formula + 1)
```

```lean
@Yulang.InferenceSubstitutionCost.instantiate_value : ∀ {α : Type} (scheme : Yulang.Inference.Scheme α)
  (target : Yulang.Inference.CompTerm α),
  (Yulang.InferenceSubstitutionCost.instantiate scheme target).fst = scheme.instantiate target
```

```lean
@Yulang.InferenceSubstitutionCost.instantiate_bound : ∀ {α : Type} (scheme : Yulang.Inference.Scheme α)
  (target : Yulang.Inference.CompTerm α),
  (Yulang.InferenceSubstitutionCost.instantiate scheme target).snd ≤
    Yulang.InferenceSubstitutionCost.formulaNodes scheme *
      (max 2 (Yulang.InferenceSubstitutionCost.compNodes target) * Yulang.InferenceSubstitutionCost.binderDepth scheme +
        1)
```

```lean
@Yulang.InferenceSubstitutionCost.binderDepth_le_nodes : ∀ {α : Type} (formula : Yulang.Inference.Formula α),
  Yulang.InferenceSubstitutionCost.binderDepth formula ≤ Yulang.InferenceSubstitutionCost.formulaNodes formula
```

```lean
@Yulang.InferenceSubstitutionCost.instantiate_size_bound : ∀ {α : Type} (scheme : Yulang.Inference.Scheme α)
  (target : Yulang.Inference.CompTerm α),
  (Yulang.InferenceSubstitutionCost.instantiate scheme target).snd ≤
    Yulang.InferenceSubstitutionCost.formulaNodes scheme *
      (max 2 (Yulang.InferenceSubstitutionCost.compNodes target) *
          Yulang.InferenceSubstitutionCost.formulaNodes scheme +
        1)
```

</details>

## ProducerContextualNormalForm

既存 grouping と normalize が新要求同値を保存する。全 normalize は行前順序を前提とし、同値な union の順序違いで結果が異なるため完全な標準形ではない。

<details>
<summary>5 個の公開定理の完全な型</summary>

```lean
@Yulang.ProducerContextualNormalForm.union_idempotent : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  (type : Yulang.StructuralBase.Ty Row), Yulang.ProducerContextual.ProducerEq leRow (type.union type) type
```

```lean
@Yulang.ProducerContextualNormalForm.merge_equivalent : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  (left right : Yulang.StructuralBase.Ty Row),
  Yulang.ProducerContextual.ProducerEq leRow (Yulang.ProducerNormalForm.merge left right) (left.union right)
```

```lean
@Yulang.ProducerContextualNormalForm.normalize_equivalent : ∀ {Row : Type u_1} {leRow : Row → Row → Prop},
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      ∀ (type : Yulang.StructuralBase.Ty Row),
        Yulang.ProducerContextual.ProducerEq leRow (Yulang.ProducerNormalForm.normalize type) type
```

```lean
@Yulang.ProducerContextualNormalForm.normalize_accept_iff : ∀ {Row : Type u_1} {leRow : Row → Row → Prop},
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      ∀ (type : Yulang.StructuralBase.Ty Row) (rank : Nat) (environment : Yulang.ProducerContextual.Environment Row)
        (demand : Yulang.ProducerContextual.Demand Row),
        Yulang.ProducerContextual.AcceptAt leRow rank environment (Yulang.ProducerNormalForm.normalize type) demand ↔
          Yulang.ProducerContextual.AcceptAt leRow rank environment type demand
```

```lean
@Yulang.ProducerContextualNormalForm.normalize_not_complete : ∀ {Row : Type u_1} (leRow : Row → Row → Prop),
  ∃ first last,
    Yulang.ProducerContextual.ProducerEq leRow first last ∧
      Yulang.ProducerNormalForm.normalize first ≠ Yulang.ProducerNormalForm.normalize last
```

</details>

## ModuleInterfaceCache

任意の新入力と正しい旧 build で、source/key と実依存 artifact の等号を検査する cache 再利用が全体再計算と一致する。呼出列は実入力が異なる node のみで、重複せず node 数以下。

<details>
<summary>9 個の公開定理の完全な型</summary>

```lean
@Yulang.ModuleInterfaceCache.rebuild_exact : ∀ {Source : Type u_1} {Interface : Type u_2} [inst : DecidableEq Source]
  [inst_1 : DecidableEq Interface] (compile : Source → List Interface → Interface) (before after : Nat → Source)
  (oldDependencies newDependencies : Yulang.ModuleIncremental.Dependencies) (n : Nat),
  (Yulang.ModuleInterfaceCache.rebuild compile before after oldDependencies newDependencies n
        (Yulang.ModuleIncremental.build compile before oldDependencies n)).fst =
    Yulang.ModuleIncremental.build compile after newDependencies n
```

```lean
@Yulang.ModuleInterfaceCache.rebuild_valid_cache : ∀ {Source : Type u_1} {Interface : Type u_2}
  [inst : DecidableEq Source] [inst_1 : DecidableEq Interface] (compile : Source → List Interface → Interface)
  (before after : Nat → Source) (oldDependencies newDependencies : Yulang.ModuleIncremental.Dependencies) (n : Nat)
  (cached : Fin n → Interface),
  (∀ (node : Fin n), cached node = Yulang.ModuleIncremental.build compile before oldDependencies n node) →
    (Yulang.ModuleInterfaceCache.rebuild compile before after oldDependencies newDependencies n cached).fst =
      Yulang.ModuleIncremental.build compile after newDependencies n
```

```lean
@Yulang.ModuleInterfaceCache.rebuild_trace : ∀ {Source : Type u_1} {Interface : Type u_2} [inst : DecidableEq Source]
  [inst_1 : DecidableEq Interface] (compile : Source → List Interface → Interface) (before after : Nat → Source)
  (oldDependencies newDependencies : Yulang.ModuleIncremental.Dependencies) (n : Nat),
  (Yulang.ModuleInterfaceCache.rebuild compile before after oldDependencies newDependencies n
        (Yulang.ModuleIncremental.build compile before oldDependencies n)).snd =
    List.filter
      (fun node => !Yulang.ModuleInterfaceCache.sameInput compile before after oldDependencies newDependencies node)
      (List.range n)
```

```lean
@Yulang.ModuleInterfaceCache.rebuild_called_iff : ∀ {Source : Type u_1} {Interface : Type u_2}
  [inst : DecidableEq Source] [inst_1 : DecidableEq Interface] (compile : Source → List Interface → Interface)
  (before after : Nat → Source) (oldDependencies newDependencies : Yulang.ModuleIncremental.Dependencies)
  (n node : Nat),
  node ∈
      (Yulang.ModuleInterfaceCache.rebuild compile before after oldDependencies newDependencies n
          (Yulang.ModuleIncremental.build compile before oldDependencies n)).snd ↔
    node < n ∧ Yulang.ModuleInterfaceCache.sameInput compile before after oldDependencies newDependencies node = false
```

```lean
@Yulang.ModuleInterfaceCache.rebuild_calls_le : ∀ {Source : Type u_1} {Interface : Type u_2} [inst : DecidableEq Source]
  [inst_1 : DecidableEq Interface] (compile : Source → List Interface → Interface) (before after : Nat → Source)
  (oldDependencies newDependencies : Yulang.ModuleIncremental.Dependencies) (n : Nat),
  (Yulang.ModuleInterfaceCache.rebuild compile before after oldDependencies newDependencies n
          (Yulang.ModuleIncremental.build compile before oldDependencies n)).snd.length ≤
    n
```

```lean
@Yulang.ModuleInterfaceCache.rebuild_calls_nodup : ∀ {Source : Type u_1} {Interface : Type u_2}
  [inst : DecidableEq Source] [inst_1 : DecidableEq Interface] (compile : Source → List Interface → Interface)
  (before after : Nat → Source) (oldDependencies newDependencies : Yulang.ModuleIncremental.Dependencies) (n : Nat),
  (Yulang.ModuleInterfaceCache.rebuild compile before after oldDependencies newDependencies n
        (Yulang.ModuleIncremental.build compile before oldDependencies n)).snd.Nodup
```

```lean
@Yulang.ModuleInterfaceCache.clean_same_input : ∀ {Source : Type u_1} {Interface : Type u_2} [inst : DecidableEq Source]
  [inst_1 : DecidableEq Interface] (compile : Source → List Interface → Interface) (before after : Nat → Source)
  (oldDependencies newDependencies : Yulang.ModuleIncremental.Dependencies) (changed : Nat → Bool),
  (∀ (node : Nat), changed node = false → before node = after node ∧ oldDependencies node = newDependencies node) →
    ∀ (node : Nat),
      Yulang.ModuleIncremental.dirty changed newDependencies (node + 1) (Fin.last node) = false →
        Yulang.ModuleInterfaceCache.sameInput compile before after oldDependencies newDependencies node = true
```

```lean
@Yulang.ModuleInterfaceCache.called_implies_affected : ∀ {Source : Type u_1} {Interface : Type u_2}
  [inst : DecidableEq Source] [inst_1 : DecidableEq Interface] (compile : Source → List Interface → Interface)
  (before after : Nat → Source) (oldDependencies newDependencies : Yulang.ModuleIncremental.Dependencies)
  (changed : Nat → Bool),
  (∀ (node : Nat), changed node = false → before node = after node ∧ oldDependencies node = newDependencies node) →
    ∀ (n node : Nat),
      node ∈
          (Yulang.ModuleInterfaceCache.rebuild compile before after oldDependencies newDependencies n
              (Yulang.ModuleIncremental.build compile before oldDependencies n)).snd →
        Yulang.ModuleIncremental.Affected changed newDependencies node
```

```lean
Yulang.ModuleInterfaceCache.Examples.unchanged_interface_stops_recompilation : have compile :=
  fun source dependencies => (source + dependencies.sum) % 2;
have before := fun x => 0;
have after := fun node => if node = 0 then 2 else 0;
(Yulang.ModuleInterfaceCache.rebuild compile before after Yulang.ModuleInterfaceCache.Examples.chainDependencies
      Yulang.ModuleInterfaceCache.Examples.chainDependencies 3
      (Yulang.ModuleIncremental.build compile before Yulang.ModuleInterfaceCache.Examples.chainDependencies 3)).snd =
  [0]
```

</details>

## TypeSimplificationSize

任意の型項で実簡約が値 node 数と行込み node 数を増やさず、一時置換のサイズと実候補数を入力サイズから抑える。簡約成功を前提にしない。

<details>
<summary>19 個の公開定理の完全な型</summary>

```lean
@Yulang.TypeSimplificationSize.row_substitution_identity : ∀ {n : Nat}
  (replacement : Fin n → Yulang.Inference.TyTerm (Fin n)) (row : Yulang.Inference.RowTerm (Fin n)),
  Yulang.Inference.RowTerm.subst (fun index => { ty := replacement index, row := Yulang.Inference.RowTerm.var index })
      row =
    row
```

```lean
@Yulang.TypeSimplificationSize.substitute_nodes_bound : ∀ {n : Nat}
  (replacement : Fin n → Yulang.Inference.TyTerm (Fin n)) (factor : Nat),
  1 ≤ factor →
    (∀ (index : Fin n), Yulang.TypeSimplification.nodes (replacement index) ≤ factor) →
      ∀ (term : Yulang.Inference.TyTerm (Fin n)),
        Yulang.TypeSimplification.nodes (Yulang.TypeSimplification.substituteValues term replacement) ≤
          factor * Yulang.TypeSimplification.nodes term
```

```lean
@Yulang.TypeSimplificationSize.substitute_total_nodes_bound : ∀ {n : Nat}
  (replacement : Fin n → Yulang.Inference.TyTerm (Fin n)) (factor : Nat),
  1 ≤ factor →
    (∀ (index : Fin n), Yulang.InferenceSubstitutionCost.tyNodes (replacement index) ≤ factor) →
      ∀ (term : Yulang.Inference.TyTerm (Fin n)),
        Yulang.InferenceSubstitutionCost.tyNodes (Yulang.TypeSimplification.substituteValues term replacement) ≤
          factor * Yulang.InferenceSubstitutionCost.tyNodes term
```

```lean
@Yulang.TypeSimplificationSize.replacement_sizes : ∀ {n : Nat} (term : Yulang.Inference.TyTerm (Fin n)) (index : Fin n),
  Yulang.TypeSimplification.nodes (Yulang.TypeSimplification.replacement term index) = 1 ∧
    Yulang.InferenceSubstitutionCost.tyNodes (Yulang.TypeSimplification.replacement term index) = 1
```

```lean
@Yulang.TypeSimplificationSize.simplify_sizes : ∀ {n : Nat} (term : Yulang.Inference.TyTerm (Fin n)),
  Yulang.TypeSimplification.nodes (Yulang.TypeSimplification.simplify term) ≤ Yulang.TypeSimplification.nodes term ∧
    Yulang.InferenceSubstitutionCost.tyNodes (Yulang.TypeSimplification.simplify term) ≤
      Yulang.InferenceSubstitutionCost.tyNodes term
```

```lean
@Yulang.TypeSimplificationSize.simplifySafe_sizes : ∀ {n : Nat} (term : Yulang.Inference.TyTerm (Fin n)),
  Yulang.TypeSimplification.nodes (Yulang.TypeSimplification.simplifySafe term) ≤ Yulang.TypeSimplification.nodes term ∧
    Yulang.InferenceSubstitutionCost.tyNodes (Yulang.TypeSimplification.simplifySafe term) ≤
      Yulang.InferenceSubstitutionCost.tyNodes term
```

```lean
@Yulang.TypeSimplificationSize.merge_sizes : ∀ {n : Nat} (first second : Fin n)
  (term : Yulang.Inference.TyTerm (Fin n)),
  Yulang.TypeSimplification.nodes (Yulang.TypeSimplification.merge first second term) ≤
      Yulang.TypeSimplification.nodes term ∧
    Yulang.InferenceSubstitutionCost.tyNodes (Yulang.TypeSimplification.merge first second term) ≤
      Yulang.InferenceSubstitutionCost.tyNodes term
```

```lean
@Yulang.TypeSimplificationSize.applyMerge_sizes : ∀ {n : Nat} (first second : Fin n)
  (term : Yulang.Inference.TyTerm (Fin n)),
  Yulang.TypeSimplification.nodes (Yulang.TypeSimplification.applyMerge first second term) ≤
      Yulang.TypeSimplification.nodes term ∧
    Yulang.InferenceSubstitutionCost.tyNodes (Yulang.TypeSimplification.applyMerge first second term) ≤
      Yulang.InferenceSubstitutionCost.tyNodes term
```

```lean
@Yulang.TypeSimplificationSize.mergeCandidates_sizes : ∀ {n : Nat} (candidates : List (Fin n × Fin n))
  (term : Yulang.Inference.TyTerm (Fin n)),
  Yulang.TypeSimplification.nodes (Yulang.TypeSimplification.mergeCandidates candidates term) ≤
      Yulang.TypeSimplification.nodes term ∧
    Yulang.InferenceSubstitutionCost.tyNodes (Yulang.TypeSimplification.mergeCandidates candidates term) ≤
      Yulang.InferenceSubstitutionCost.tyNodes term
```

```lean
@Yulang.TypeSimplificationSize.mergeAll_sizes : ∀ {n : Nat} (term : Yulang.Inference.TyTerm (Fin n)),
  Yulang.TypeSimplification.nodes (Yulang.TypeSimplification.mergeAll term) ≤ Yulang.TypeSimplification.nodes term ∧
    Yulang.InferenceSubstitutionCost.tyNodes (Yulang.TypeSimplification.mergeAll term) ≤
      Yulang.InferenceSubstitutionCost.tyNodes term
```

```lean
@Yulang.TypeSimplificationSize.sandwich_sizes : ∀ {n : Nat} (index : Fin n)
  (fixed term : Yulang.Inference.TyTerm (Fin n)),
  Yulang.TypeSimplification.nodes fixed ≤ 1 →
    Yulang.InferenceSubstitutionCost.tyNodes fixed ≤ 1 →
      Yulang.TypeSimplification.nodes (Yulang.TypeSimplification.sandwich index fixed term) ≤
          Yulang.TypeSimplification.nodes term ∧
        Yulang.InferenceSubstitutionCost.tyNodes (Yulang.TypeSimplification.sandwich index fixed term) ≤
          Yulang.InferenceSubstitutionCost.tyNodes term
```

```lean
@Yulang.TypeSimplificationSize.applySandwich_sizes : ∀ {n : Nat} (index : Fin n)
  (fixed term : Yulang.Inference.TyTerm (Fin n)),
  Yulang.TypeSimplification.nodes fixed ≤ 1 →
    Yulang.InferenceSubstitutionCost.tyNodes fixed ≤ 1 →
      Yulang.TypeSimplification.nodes (Yulang.TypeSimplification.applySandwich index fixed term) ≤
          Yulang.TypeSimplification.nodes term ∧
        Yulang.InferenceSubstitutionCost.tyNodes (Yulang.TypeSimplification.applySandwich index fixed term) ≤
          Yulang.InferenceSubstitutionCost.tyNodes term
```

```lean
@Yulang.TypeSimplificationSize.sandwichCandidates_sizes : ∀ {n : Nat}
  (candidates : List (Fin n × Yulang.Inference.TyTerm (Fin n))),
  (∀ (pair : Fin n × Yulang.Inference.TyTerm (Fin n)),
      pair ∈ candidates →
        Yulang.TypeSimplification.nodes pair.snd ≤ 1 ∧ Yulang.InferenceSubstitutionCost.tyNodes pair.snd ≤ 1) →
    ∀ (term : Yulang.Inference.TyTerm (Fin n)),
      Yulang.TypeSimplification.nodes (Yulang.TypeSimplification.sandwichCandidates candidates term) ≤
          Yulang.TypeSimplification.nodes term ∧
        Yulang.InferenceSubstitutionCost.tyNodes (Yulang.TypeSimplification.sandwichCandidates candidates term) ≤
          Yulang.InferenceSubstitutionCost.tyNodes term
```

```lean
@Yulang.TypeSimplificationSize.sandwichAll_sizes : ∀ {n : Nat} (term : Yulang.Inference.TyTerm (Fin n)),
  Yulang.TypeSimplification.nodes (Yulang.TypeSimplification.sandwichAll term) ≤ Yulang.TypeSimplification.nodes term ∧
    Yulang.InferenceSubstitutionCost.tyNodes (Yulang.TypeSimplification.sandwichAll term) ≤
      Yulang.InferenceSubstitutionCost.tyNodes term
```

```lean
@Yulang.TypeSimplificationSize.simplifyAll_sizes : ∀ {n : Nat} (term : Yulang.Inference.TyTerm (Fin n)),
  Yulang.TypeSimplification.nodes (Yulang.TypeSimplification.simplifyAll term) ≤ Yulang.TypeSimplification.nodes term ∧
    Yulang.InferenceSubstitutionCost.tyNodes (Yulang.TypeSimplification.simplifyAll term) ≤
      Yulang.InferenceSubstitutionCost.tyNodes term
```

```lean
@Yulang.TypeSimplificationSize.jointReplacement_sizes : ∀ {n : Nat} (positive : Bool) (first second index : Fin n),
  Yulang.TypeSimplification.nodes (Yulang.TypeSimplification.jointReplacement positive first second index) ≤ 3 ∧
    Yulang.InferenceSubstitutionCost.tyNodes (Yulang.TypeSimplification.jointReplacement positive first second index) ≤
      3
```

```lean
@Yulang.TypeSimplificationSize.jointSubstitution_sizes : ∀ {n : Nat} (positive : Bool) (first second : Fin n)
  (term : Yulang.Inference.TyTerm (Fin n)),
  Yulang.TypeSimplification.nodes
        (Yulang.TypeSimplification.substituteValues term
          (Yulang.TypeSimplification.jointReplacement positive first second)) ≤
      3 * Yulang.TypeSimplification.nodes term ∧
    Yulang.InferenceSubstitutionCost.tyNodes
        (Yulang.TypeSimplification.substituteValues term
          (Yulang.TypeSimplification.jointReplacement positive first second)) ≤
      3 * Yulang.InferenceSubstitutionCost.tyNodes term
```

```lean
Yulang.TypeSimplificationSize.merge_candidate_count : ∀ (n : Nat),
  (List.flatMap (fun first => List.map (fun second => (first, second)) (List.finRange n)) (List.finRange n)).length =
    n * n
```

```lean
Yulang.TypeSimplificationSize.sandwich_candidate_count : ∀ (n : Nat),
  (List.flatMap
        (fun index =>
          List.map (fun base => (index, Yulang.Inference.TyTerm.base base))
            [Yulang.Inference.Base.int, Yulang.Inference.Base.str, Yulang.Inference.Base.bool,
              Yulang.Inference.Base.unit])
        (List.finRange n)).length =
    4 * n
```

</details>

## ProducerContextualRecord

任意行関係の同名 record 比較を、payload 比較と head label を除去した tail の field 比較に分解する。任意 regular graph の全深さで tail の深さを保つ。

<details>
<summary>15 個の公開定理の完全な型</summary>

```lean
@Yulang.ProducerContextualRecord.fieldLe_refl : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (hidden : List Nat)
  (type : Yulang.StructuralBase.Ty Row), Yulang.ProducerContextualRecord.FieldLe leRow hidden type type
```

```lean
@Yulang.ProducerContextualRecord.fieldLe_trans : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (hidden : List Nat)
  {first middle last : Yulang.StructuralBase.Ty Row},
  Yulang.ProducerContextualRecord.FieldLe leRow hidden first middle →
    Yulang.ProducerContextualRecord.FieldLe leRow hidden middle last →
      Yulang.ProducerContextualRecord.FieldLe leRow hidden first last
```

```lean
@Yulang.ProducerContextualRecord.fieldLe_hide_more : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {first last : List Nat},
  (∀ (label : Nat), label ∈ first → label ∈ last) →
    ∀ {source target : Yulang.StructuralBase.Ty Row},
      Yulang.ProducerContextualRecord.FieldLe leRow first source target →
        Yulang.ProducerContextualRecord.FieldLe leRow last source target
```

```lean
@Yulang.ProducerContextualRecord.probeAt_record_field : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (rank : Nat)
  (env : Yulang.ProducerContextual.Environment Row) (current label : Nat) (payload rest : Yulang.StructuralBase.Ty Row)
  (observation : Yulang.ProducerContextual.Observation Row),
  Yulang.ProducerContextual.ProbeAt leRow rank env (Yulang.StructuralBase.Ty.record current payload rest)
      (Yulang.ProducerContextual.Observation.field label observation) ↔
    if label = current then Yulang.ProducerContextual.ProbeAt leRow rank env payload observation
    else
      Yulang.ProducerContextual.ProbeAt leRow rank env rest
        (Yulang.ProducerContextual.Observation.field label observation)
```

```lean
@Yulang.ProducerContextualRecord.fieldLe_record_iff : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (hidden : List Nat)
  (label : Nat) (a b rest tail : Yulang.StructuralBase.Ty Row),
  Yulang.ProducerContextualRecord.FieldLe leRow hidden (Yulang.StructuralBase.Ty.record label a rest)
      (Yulang.StructuralBase.Ty.record label b tail) ↔
    (¬label ∈ hidden → Yulang.ProducerContextual.ProducerLe leRow a b) ∧
      Yulang.ProducerContextualRecord.FieldLe leRow (label :: hidden) rest tail
```

```lean
@Yulang.ProducerContextualRecord.producerLe_records_iff_fields : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  (first last : Nat) (a b rest tail : Yulang.StructuralBase.Ty Row),
  Yulang.ProducerContextual.ProducerLe leRow (Yulang.StructuralBase.Ty.record first a rest)
      (Yulang.StructuralBase.Ty.record last b tail) ↔
    Yulang.ProducerContextualRecord.FieldLe leRow [] (Yulang.StructuralBase.Ty.record first a rest)
      (Yulang.StructuralBase.Ty.record last b tail)
```

```lean
@Yulang.ProducerContextualRecord.producerLe_record_iff : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (label : Nat)
  (a b rest tail : Yulang.StructuralBase.Ty Row),
  Yulang.ProducerContextual.ProducerLe leRow (Yulang.StructuralBase.Ty.record label a rest)
      (Yulang.StructuralBase.Ty.record label b tail) ↔
    Yulang.ProducerContextual.ProducerLe leRow a b ∧ Yulang.ProducerContextualRecord.FieldLe leRow [label] rest tail
```

```lean
@Yulang.ProducerContextualRecord.fieldLe_emptyRecord : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (hidden : List Nat)
  (source : Yulang.StructuralBase.Ty Row),
  Yulang.ProducerContextualRecord.FieldLe leRow hidden source Yulang.StructuralBase.Ty.emptyRecord
```

```lean
@Yulang.ProducerContextualRecord.singleton_requirement_iff : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (label : Nat)
  (a b rest : Yulang.StructuralBase.Ty Row),
  Yulang.ProducerContextual.ProducerLe leRow (Yulang.StructuralBase.Ty.record label a rest)
      (Yulang.StructuralBase.Ty.record label b Yulang.StructuralBase.Ty.emptyRecord) ↔
    Yulang.ProducerContextual.ProducerLe leRow a b
```

```lean
@Yulang.ProducerContextualRecord.hidden_head_iff : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (hidden : List Nat)
  (label : Nat) (payload rest target : Yulang.StructuralBase.Ty Row),
  Yulang.ProducerContextualRecord.FieldLe leRow (label :: hidden) (Yulang.StructuralBase.Ty.record label payload rest)
      target ↔
    Yulang.ProducerContextualRecord.FieldLe leRow (label :: hidden) rest target
```

```lean
@Yulang.ProducerContextualRecord.shadowed_head_equivalent : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (label : Nat)
  (payload hidden rest : Yulang.StructuralBase.Ty Row),
  Yulang.ProducerContextual.ProducerEq leRow
    (Yulang.StructuralBase.Ty.record label payload (Yulang.StructuralBase.Ty.record label hidden rest))
    (Yulang.StructuralBase.Ty.record label payload rest)
```

```lean
@Yulang.ProducerContextualRecord.Regular.record_reference_iff : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {State : Type u_2} (graph : Yulang.RegularValueTypes.Graph Row State) (label : Nat) (a b : State)
  (rest tail : Yulang.RegularValueTypes.Layer Row State),
  Yulang.ProducerContextualRegular.ProducerLe graph leRow (Yulang.RegularValueTypes.Layer.record label a rest)
      (Yulang.RegularValueTypes.Layer.record label b tail) ↔
    Yulang.ProducerContextualRegular.ReferenceLe graph leRow a b ∧
      Yulang.ProducerContextualRecord.Regular.FieldLe graph leRow [label] rest tail
```

```lean
@Yulang.ProducerContextualRecord.Regular.record_iff : ∀ {Row : Type u_1} {leRow : Row → Row → Prop} (label : Nat)
  (a b rest tail : Yulang.RegularInferenceModel.Ty Row),
  Yulang.ProducerContextualRegular.ProducerLe (Yulang.RegularInferenceModel.graph Row) leRow
      (Yulang.RegularValueTypes.Layer.record label (Yulang.RegularInferenceModel.State.node a) rest)
      (Yulang.RegularValueTypes.Layer.record label (Yulang.RegularInferenceModel.State.node b) tail) ↔
    Yulang.ProducerContextualRegular.ProducerLe (Yulang.RegularInferenceModel.graph Row) leRow a b ∧
      Yulang.ProducerContextualRecord.Regular.FieldLe (Yulang.RegularInferenceModel.graph Row) leRow [label] rest tail
```

```lean
@Yulang.ProducerContextualRecord.Regular.singleton_requirement_iff : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  (label : Nat) (a b rest : Yulang.RegularInferenceModel.Ty Row),
  Yulang.ProducerContextualRegular.ProducerLe (Yulang.RegularInferenceModel.graph Row) leRow
      (Yulang.RegularValueTypes.Layer.record label (Yulang.RegularInferenceModel.State.node a) rest)
      (Yulang.RegularValueTypes.Layer.record label (Yulang.RegularInferenceModel.State.node b)
        Yulang.RegularValueTypes.Layer.emptyRecord) ↔
    Yulang.ProducerContextualRegular.ProducerLe (Yulang.RegularInferenceModel.graph Row) leRow a b
```

```lean
@Yulang.ProducerContextualRecord.Regular.shadowed_head_equivalent : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  {State : Type u_2} (graph : Yulang.RegularValueTypes.Graph Row State) (label : Nat) (payload hidden : State)
  (rest : Yulang.RegularValueTypes.Layer Row State),
  Yulang.ProducerContextualRegular.ProducerEq graph leRow
    (Yulang.RegularValueTypes.Layer.record label payload (Yulang.RegularValueTypes.Layer.record label hidden rest))
    (Yulang.RegularValueTypes.Layer.record label payload rest)
```

</details>

## PresenceTailElimination

任意の有限 positive tail 方程式と全自由 concrete layer parameter で同深さ循環を消去し、単一 layer 由来の mask family を構文等号で構成する。全 payload 述語・外側 mask・data 値で独立解を回収する。

<details>
<summary>38 個の公開定理の完全な型</summary>

```lean
@Yulang.PresenceTailElimination.sum_map_constant : ∀ {α : Type u_1} (items : List α) (constant : Nat),
  (List.map (fun x => constant) items).sum = items.length * constant
```

```lean
@Yulang.PresenceTailElimination.Mask.all_complete : ∀ {labels : Nat}
  (hidden : Yulang.PresenceTailElimination.Mask labels), hidden ∈ Yulang.PresenceTailElimination.Mask.all labels
```

```lean
Yulang.PresenceTailElimination.Mask.all_length : ∀ (labels : Nat),
  (Yulang.PresenceTailElimination.Mask.all labels).length = 2 ^ labels
```

```lean
@Yulang.PresenceTailElimination.Mask.join_empty : ∀ {labels : Nat}
  (hidden : Yulang.PresenceTailElimination.Mask labels), hidden.join Yulang.PresenceTailElimination.Mask.empty = hidden
```

```lean
@Yulang.PresenceTailElimination.Mask.empty_join : ∀ {labels : Nat}
  (hidden : Yulang.PresenceTailElimination.Mask labels), Yulang.PresenceTailElimination.Mask.empty.join hidden = hidden
```

```lean
@Yulang.PresenceTailElimination.Mask.join_comm : ∀ {labels : Nat}
  (left right : Yulang.PresenceTailElimination.Mask labels), left.join right = right.join left
```

```lean
@Yulang.PresenceTailElimination.Mask.join_assoc : ∀ {labels : Nat}
  (first middle last : Yulang.PresenceTailElimination.Mask labels),
  (first.join middle).join last = first.join (middle.join last)
```

```lean
@Yulang.PresenceTailElimination.Mask.join_right_comm : ∀ {labels : Nat}
  (first middle last : Yulang.PresenceTailElimination.Mask labels),
  (first.join middle).join last = (first.join last).join middle
```

```lean
@Yulang.PresenceTailElimination.Mask.names_empty : ∀ {labels : Nat},
  Yulang.PresenceTailElimination.Mask.empty.names = []
```

```lean
@Yulang.PresenceTailElimination.Mask.mem_names : ∀ {labels : Nat} (hidden : Yulang.PresenceTailElimination.Mask labels)
  (label : Nat), label ∈ hidden.names ↔ ∃ bound, hidden ⟨label, bound⟩ = true
```

```lean
@Yulang.PresenceTailElimination.Mask.mem_names_join : ∀ {labels : Nat}
  (left right : Yulang.PresenceTailElimination.Mask labels) (label : Nat),
  label ∈ (left.join right).names ↔ label ∈ left.names ∨ label ∈ right.names
```

```lean
@Yulang.PresenceTailElimination.Mask.mask_join : ∀ {labels : Nat} {Payload : Type u_1}
  (left right : Yulang.PresenceTailElimination.Mask labels) (layer : Yulang.PresenceLayers.Layer Payload),
  Yulang.PresenceLayers.Layer.mask right.names (Yulang.PresenceLayers.Layer.mask left.names layer) =
    Yulang.PresenceLayers.Layer.mask (left.join right).names layer
```

```lean
@Yulang.PresenceTailElimination.Mask.mask_only : ∀ {labels : Nat} {Payload : Type u_1} (label : Fin labels)
  (layer : Yulang.PresenceLayers.Layer Payload),
  Yulang.PresenceLayers.Layer.mask (Yulang.PresenceTailElimination.Mask.only label).names layer =
    Yulang.PresenceLayers.Layer.mask [↑label] layer
```

```lean
@Yulang.PresenceTailElimination.Body.eval_monotone : ∀ {labels : Nat} {Payload Tail : Type}
  (body : Yulang.PresenceTailElimination.Body labels Payload Tail)
  (atoms : Yulang.PresenceLayers.Layer Payload → Yulang.PresenceTailElimination.Mask labels → Prop)
  (left right : Yulang.PositiveEquationElimination.Valuation (Tail × Yulang.PresenceTailElimination.Mask labels)),
  Yulang.PositiveEquationElimination.Below left right →
    ∀ (hidden : Yulang.PresenceTailElimination.Mask labels),
      Yulang.PresenceTailElimination.Body.eval atoms left hidden body →
        Yulang.PresenceTailElimination.Body.eval atoms right hidden body
```

```lean
@Yulang.PresenceTailElimination.Body.expand_mask : ∀ {labels : Nat} {Payload Tail : Type}
  (body : Yulang.PresenceTailElimination.Body labels Payload Tail)
  (tails : Tail × Yulang.PresenceTailElimination.Mask labels → Yulang.PresenceLayers.Layer Payload),
  (∀ (tail : Tail) (first more : Yulang.PresenceTailElimination.Mask labels),
      Yulang.PresenceLayers.Layer.mask more.names (tails (tail, first)) = tails (tail, first.join more)) →
    ∀ (hidden more : Yulang.PresenceTailElimination.Mask labels),
      Yulang.PresenceLayers.Layer.mask more.names (Yulang.PresenceTailElimination.Body.expand tails hidden body) =
        Yulang.PresenceTailElimination.Body.expand tails (hidden.join more) body
```

```lean
@Yulang.PresenceTailElimination.Body.meaning_expand : ∀ {labels : Nat} {Payload Tail : Type}
  (body : Yulang.PresenceTailElimination.Body labels Payload Tail)
  (tails : Tail × Yulang.PresenceTailElimination.Mask labels → Yulang.PresenceLayers.Layer Payload)
  (assignment : Payload → Yulang.PresenceDataTypes.Ty) (outer : List Nat)
  (hidden : Yulang.PresenceTailElimination.Mask labels) (value : Yulang.SourceDataRuntime.Value),
  Yulang.PresenceLayers.Layer.meaning assignment outer (Yulang.PresenceTailElimination.Body.expand tails hidden body)
      value =
    Yulang.PresenceTailElimination.Body.eval
      (fun layer mask =>
        Yulang.PresenceLayers.Layer.meaning assignment outer (Yulang.PresenceLayers.Layer.mask mask.names layer) value)
      (fun coordinate => Yulang.PresenceLayers.Layer.meaning assignment outer (tails coordinate) value) hidden body
```

```lean
@Yulang.PresenceTailElimination.coordinates_complete : ∀ {slots labels : Nat}
  (coordinate : Yulang.PresenceTailElimination.Coordinate slots labels),
  coordinate ∈ Yulang.PresenceTailElimination.coordinates slots labels
```

```lean
Yulang.PresenceTailElimination.coordinates_length : ∀ (slots labels : Nat),
  (Yulang.PresenceTailElimination.coordinates slots labels).length = slots * 2 ^ labels
```

```lean
@Yulang.PresenceTailElimination.seed_coherent : ∀ {slots : Nat} {Payload : Type u_1} {labels : Nat}
  (parameters : Fin slots → Yulang.PresenceLayers.Layer Payload),
  Yulang.PresenceTailElimination.Coherent (Yulang.PresenceTailElimination.seed parameters)
```

```lean
@Yulang.PresenceTailElimination.step_coherent : ∀ {slots labels : Nat} {Payload : Type}
  (graph : Yulang.PresenceTailElimination.Graph slots labels Payload)
  (family : Yulang.PresenceTailElimination.Coordinate slots labels → Yulang.PresenceLayers.Layer Payload),
  Yulang.PresenceTailElimination.Coherent family →
    Yulang.PresenceTailElimination.Coherent (Yulang.PresenceTailElimination.step graph family)
```

```lean
@Yulang.PresenceTailElimination.ascend_coherent : ∀ {slots labels : Nat} {Payload : Type}
  (graph : Yulang.PresenceTailElimination.Graph slots labels Payload)
  (family : Yulang.PresenceTailElimination.Coordinate slots labels → Yulang.PresenceLayers.Layer Payload),
  Yulang.PresenceTailElimination.Coherent family →
    Yulang.PresenceTailElimination.Coherent (Yulang.PresenceTailElimination.ascend graph family)
```

```lean
@Yulang.PresenceTailElimination.descend_coherent : ∀ {slots labels : Nat} {Payload : Type}
  (graph : Yulang.PresenceTailElimination.Graph slots labels Payload)
  (family : Yulang.PresenceTailElimination.Coordinate slots labels → Yulang.PresenceLayers.Layer Payload),
  Yulang.PresenceTailElimination.Coherent family →
    Yulang.PresenceTailElimination.Coherent (Yulang.PresenceTailElimination.descend graph family)
```

```lean
@Yulang.PresenceTailElimination.iterate_invariant : ∀ {Value : Type} (update : Value → Value)
  (invariant : Value → Prop),
  (∀ (value : Value), invariant value → invariant (update value)) →
    ∀ (rounds : Nat) (initial : Value),
      invariant initial → invariant (Yulang.PositiveEquationElimination.iterate update rounds initial)
```

```lean
@Yulang.PresenceTailElimination.solveFamily_coherent : ∀ {slots labels : Nat} {Payload : Type}
  (graph : Yulang.PresenceTailElimination.Graph slots labels Payload)
  (parameters : Fin slots → Yulang.PresenceLayers.Layer Payload),
  Yulang.PresenceTailElimination.Coherent (Yulang.PresenceTailElimination.solveFamily graph parameters)
```

```lean
@Yulang.PresenceTailElimination.solve_mask : ∀ {slots labels : Nat} {Payload : Type}
  (graph : Yulang.PresenceTailElimination.Graph slots labels Payload)
  (parameters : Fin slots → Yulang.PresenceLayers.Layer Payload) (index : Fin slots)
  (hidden : Yulang.PresenceTailElimination.Mask labels),
  Yulang.PresenceLayers.Layer.mask hidden.names (Yulang.PresenceTailElimination.solve graph parameters index) =
    Yulang.PresenceTailElimination.solveFamily graph parameters (index, hidden)
```

```lean
@Yulang.PresenceTailElimination.semanticStep_monotone : ∀ {slots labels : Nat} {Payload : Type}
  (graph : Yulang.PresenceTailElimination.Graph slots labels Payload)
  (assignment : Payload → Yulang.PresenceDataTypes.Ty) (outer : List Nat) (value : Yulang.SourceDataRuntime.Value),
  Yulang.PositiveEquationElimination.Monotone (Yulang.PresenceTailElimination.semanticStep graph assignment outer value)
```

```lean
@Yulang.PresenceTailElimination.observe_step : ∀ {slots labels : Nat} {Payload : Type}
  (graph : Yulang.PresenceTailElimination.Graph slots labels Payload)
  (assignment : Payload → Yulang.PresenceDataTypes.Ty) (outer : List Nat) (value : Yulang.SourceDataRuntime.Value)
  (family : Yulang.PresenceTailElimination.Coordinate slots labels → Yulang.PresenceLayers.Layer Payload),
  Yulang.PresenceTailElimination.observeFamily assignment outer value
      (Yulang.PresenceTailElimination.step graph family) =
    Yulang.PresenceTailElimination.semanticStep graph assignment outer value
      (Yulang.PresenceTailElimination.observeFamily assignment outer value family)
```

```lean
@Yulang.PresenceTailElimination.observe_ascend : ∀ {slots labels : Nat} {Payload : Type}
  (graph : Yulang.PresenceTailElimination.Graph slots labels Payload)
  (assignment : Payload → Yulang.PresenceDataTypes.Ty) (outer : List Nat) (value : Yulang.SourceDataRuntime.Value)
  (family : Yulang.PresenceTailElimination.Coordinate slots labels → Yulang.PresenceLayers.Layer Payload),
  Yulang.PresenceTailElimination.observeFamily assignment outer value
      (Yulang.PresenceTailElimination.ascend graph family) =
    Yulang.PositiveEquationElimination.ascend (Yulang.PresenceTailElimination.semanticStep graph assignment outer value)
      (Yulang.PresenceTailElimination.observeFamily assignment outer value family)
```

```lean
@Yulang.PresenceTailElimination.observe_descend : ∀ {slots labels : Nat} {Payload : Type}
  (graph : Yulang.PresenceTailElimination.Graph slots labels Payload)
  (assignment : Payload → Yulang.PresenceDataTypes.Ty) (outer : List Nat) (value : Yulang.SourceDataRuntime.Value)
  (family : Yulang.PresenceTailElimination.Coordinate slots labels → Yulang.PresenceLayers.Layer Payload),
  Yulang.PresenceTailElimination.observeFamily assignment outer value
      (Yulang.PresenceTailElimination.descend graph family) =
    Yulang.PositiveEquationElimination.descend
      (Yulang.PresenceTailElimination.semanticStep graph assignment outer value)
      (Yulang.PresenceTailElimination.observeFamily assignment outer value family)
```

```lean
@Yulang.PresenceTailElimination.observe_solveFamily : ∀ {slots labels : Nat} {Payload : Type}
  (graph : Yulang.PresenceTailElimination.Graph slots labels Payload)
  (parameters : Fin slots → Yulang.PresenceLayers.Layer Payload) (assignment : Payload → Yulang.PresenceDataTypes.Ty)
  (outer : List Nat) (value : Yulang.SourceDataRuntime.Value),
  Yulang.PresenceTailElimination.observeFamily assignment outer value
      (Yulang.PresenceTailElimination.solveFamily graph parameters) =
    Yulang.PositiveEquationElimination.project (Yulang.PresenceTailElimination.coordinates slots labels)
      (Yulang.PresenceTailElimination.semanticStep graph assignment outer value)
      (Yulang.PresenceTailElimination.observeFamily assignment outer value
        (Yulang.PresenceTailElimination.seed parameters))
```

```lean
@Yulang.PresenceTailElimination.solveFamily_sound : ∀ {slots labels : Nat} {Payload : Type}
  (graph : Yulang.PresenceTailElimination.Graph slots labels Payload)
  (parameters : Fin slots → Yulang.PresenceLayers.Layer Payload) (assignment : Payload → Yulang.PresenceDataTypes.Ty)
  (outer : List Nat) (value : Yulang.SourceDataRuntime.Value),
  Yulang.PresenceTailElimination.semanticStep graph assignment outer value
      (Yulang.PresenceTailElimination.observeFamily assignment outer value
        (Yulang.PresenceTailElimination.solveFamily graph parameters)) =
    Yulang.PresenceTailElimination.observeFamily assignment outer value
      (Yulang.PresenceTailElimination.solveFamily graph parameters)
```

```lean
@Yulang.PresenceTailElimination.solveFamily_retract : ∀ {slots labels : Nat} {Payload : Type}
  (graph : Yulang.PresenceTailElimination.Graph slots labels Payload)
  (solution : Fin slots → Yulang.PresenceLayers.Layer Payload) (assignment : Payload → Yulang.PresenceDataTypes.Ty)
  (outer : List Nat) (value : Yulang.SourceDataRuntime.Value),
  Yulang.PresenceTailElimination.semanticStep graph assignment outer value
        (Yulang.PresenceTailElimination.observeFamily assignment outer value
          (Yulang.PresenceTailElimination.seed solution)) =
      Yulang.PresenceTailElimination.observeFamily assignment outer value
        (Yulang.PresenceTailElimination.seed solution) →
    Yulang.PresenceTailElimination.observeFamily assignment outer value
        (Yulang.PresenceTailElimination.solveFamily graph solution) =
      Yulang.PresenceTailElimination.observeFamily assignment outer value (Yulang.PresenceTailElimination.seed solution)
```

```lean
@Yulang.PresenceTailElimination.seed_solve : ∀ {slots labels : Nat} {Payload : Type}
  (graph : Yulang.PresenceTailElimination.Graph slots labels Payload)
  (parameters : Fin slots → Yulang.PresenceLayers.Layer Payload),
  Yulang.PresenceTailElimination.seed (Yulang.PresenceTailElimination.solve graph parameters) =
    Yulang.PresenceTailElimination.solveFamily graph parameters
```

```lean
@Yulang.PresenceTailElimination.solve_satisfies : ∀ {slots labels : Nat} {Payload : Type}
  (graph : Yulang.PresenceTailElimination.Graph slots labels Payload)
  (parameters : Fin slots → Yulang.PresenceLayers.Layer Payload),
  Yulang.PresenceTailElimination.Satisfies graph (Yulang.PresenceTailElimination.solve graph parameters)
```

```lean
@Yulang.PresenceTailElimination.seed_equivalent : ∀ {slots : Nat} {Payload : Type u_1} {labels : Nat}
  (left right : Fin slots → Yulang.PresenceLayers.Layer Payload),
  Yulang.PresenceTailElimination.Equivalent left right →
    ∀ (assignment : Payload → Yulang.PresenceDataTypes.Ty) (outer : List Nat) (value : Yulang.SourceDataRuntime.Value),
      Yulang.PresenceTailElimination.observeFamily assignment outer value (Yulang.PresenceTailElimination.seed left) =
        Yulang.PresenceTailElimination.observeFamily assignment outer value (Yulang.PresenceTailElimination.seed right)
```

```lean
@Yulang.PresenceTailElimination.satisfies_congr : ∀ {slots labels : Nat} {Payload : Type}
  (graph : Yulang.PresenceTailElimination.Graph slots labels Payload)
  (left right : Fin slots → Yulang.PresenceLayers.Layer Payload),
  Yulang.PresenceTailElimination.Equivalent left right →
    (Yulang.PresenceTailElimination.Satisfies graph left ↔ Yulang.PresenceTailElimination.Satisfies graph right)
```

```lean
@Yulang.PresenceTailElimination.solve_retract : ∀ {slots labels : Nat} {Payload : Type}
  (graph : Yulang.PresenceTailElimination.Graph slots labels Payload)
  (solution : Fin slots → Yulang.PresenceLayers.Layer Payload),
  Yulang.PresenceTailElimination.Satisfies graph solution →
    Yulang.PresenceTailElimination.Equivalent (Yulang.PresenceTailElimination.solve graph solution) solution
```

```lean
@Yulang.PresenceTailElimination.solved_instances_exact : ∀ {slots labels : Nat} {Payload : Type}
  (graph : Yulang.PresenceTailElimination.Graph slots labels Payload)
  (solution : Fin slots → Yulang.PresenceLayers.Layer Payload),
  Yulang.PresenceTailElimination.Satisfies graph solution ↔
    ∃ parameters,
      Yulang.PresenceTailElimination.Equivalent (Yulang.PresenceTailElimination.solve graph parameters) solution
```

</details>

## PresenceTailRegular

任意の finite tail/payload graph・外部 regular graph・全自由 parameter layers に対し、実構成は全深さで独立方程式を満たす。任意独立解を一つの共通 parameter family により全深さ・全外側 mask で回収する。

<details>
<summary>10 個の公開定理の完全な型</summary>

```lean
@Yulang.PresenceTailElimination.Body.eval_mapPayload : ∀ {labels : Nat} {Payload Target Tail : Type}
  (body : Yulang.PresenceTailElimination.Body labels Payload Tail) (rename : Payload → Target)
  (atoms : Yulang.PresenceLayers.Layer Target → Yulang.PresenceTailElimination.Mask labels → Prop)
  (tails : Yulang.PositiveEquationElimination.Valuation (Tail × Yulang.PresenceTailElimination.Mask labels))
  (hidden : Yulang.PresenceTailElimination.Mask labels),
  Yulang.PresenceTailElimination.Body.eval atoms tails hidden
      (Yulang.PresenceTailElimination.Body.mapPayload rename body) =
    Yulang.PresenceTailElimination.Body.eval
      (fun layer mask => atoms (Yulang.PresenceLayers.Layer.map rename layer) mask) tails hidden body
```

```lean
@Yulang.PresenceTailElimination.Body.eval_congr : ∀ {labels : Nat} {Payload Tail : Type}
  (body : Yulang.PresenceTailElimination.Body labels Payload Tail)
  (leftAtoms rightAtoms : Yulang.PresenceLayers.Layer Payload → Yulang.PresenceTailElimination.Mask labels → Prop)
  (leftTails rightTails :
    Yulang.PositiveEquationElimination.Valuation (Tail × Yulang.PresenceTailElimination.Mask labels)),
  (∀ (layer : Yulang.PresenceLayers.Layer Payload) (hidden : Yulang.PresenceTailElimination.Mask labels),
      leftAtoms layer hidden ↔ rightAtoms layer hidden) →
    (∀ (coordinate : Tail × Yulang.PresenceTailElimination.Mask labels), leftTails coordinate ↔ rightTails coordinate) →
      ∀ (hidden : Yulang.PresenceTailElimination.Mask labels),
        Yulang.PresenceTailElimination.Body.eval leftAtoms leftTails hidden body ↔
          Yulang.PresenceTailElimination.Body.eval rightAtoms rightTails hidden body
```

```lean
@Yulang.PresenceTailRegular.parameter_embedding : ∀ {slots labels : Nat} {Index : Type}
  (graph : Yulang.PresenceTailRegular.Graph slots labels) (external : Yulang.PresenceRegularObservations.Graph Index)
  (parameters : Fin slots → Yulang.PresenceLayers.Layer Index) (depth : Nat) (index : Index)
  (value : Yulang.SourceDataRuntime.Value),
  Yulang.PresenceRegularObservations.observe (Yulang.PresenceTailRegular.solveGraph graph external parameters) depth
      (Sum.inr index) value ↔
    Yulang.PresenceRegularObservations.observe external depth index value
```

```lean
@Yulang.PresenceTailRegular.parameter_mask_embedding : ∀ {slots labels : Nat} {Index : Type}
  (graph : Yulang.PresenceTailRegular.Graph slots labels) (external : Yulang.PresenceRegularObservations.Graph Index)
  (parameters : Fin slots → Yulang.PresenceLayers.Layer Index) (depth : Nat) (hidden : List Nat) (index : Index)
  (value : Yulang.SourceDataRuntime.Value),
  Yulang.PresenceMaskedCoalescing.observeMasked (Yulang.PresenceTailRegular.solveGraph graph external parameters) depth
      hidden (Sum.inr index) value ↔
    Yulang.PresenceMaskedCoalescing.observeMasked external depth hidden index value
```

```lean
@Yulang.PresenceTailRegular.observe_seed : ∀ {slots labels : Nat} {Payload : Type u_1}
  (family : Fin slots → Yulang.PresenceLayers.Layer Payload) (assignment : Payload → Yulang.PresenceDataTypes.Ty)
  (outer : List Nat) (value : Yulang.SourceDataRuntime.Value)
  (coordinate : Yulang.PresenceTailElimination.Coordinate slots labels),
  Yulang.PresenceTailElimination.observeFamily assignment outer value (Yulang.PresenceTailElimination.seed family)
      coordinate =
    Yulang.PresenceLayers.Layer.meaning assignment (coordinate.snd.names ++ outer) (family coordinate.fst) value
```

```lean
@Yulang.PresenceTailRegular.semanticStep_lift : ∀ {slots labels : Nat} {Index : Type}
  (graph : Yulang.PresenceTailRegular.Graph slots labels)
  (family : Fin slots → Yulang.PresenceLayers.Layer (Fin slots ⊕ Index))
  (assignment : Fin slots ⊕ Index → Yulang.PresenceDataTypes.Ty) (outer : List Nat)
  (value : Yulang.SourceDataRuntime.Value) (coordinate : Yulang.PresenceTailElimination.Coordinate slots labels),
  Yulang.PresenceTailElimination.semanticStep (Yulang.PresenceTailRegular.liftGraph graph) assignment outer value
      (Yulang.PresenceTailElimination.observeFamily assignment outer value (Yulang.PresenceTailElimination.seed family))
      coordinate =
    Yulang.PresenceTailElimination.Body.eval
      (fun layer hidden =>
        Yulang.PresenceLayers.Layer.meaning (fun child => assignment (Sum.inl child)) (hidden.names ++ outer) layer
          value)
      (fun child => Yulang.PresenceLayers.Layer.meaning assignment (child.snd.names ++ outer) (family child.fst) value)
      coordinate.snd (graph coordinate.fst)
```

```lean
@Yulang.PresenceTailRegular.solveGraph_realizes : ∀ {slots labels : Nat} {Index : Type}
  (graph : Yulang.PresenceTailRegular.Graph slots labels) (external : Yulang.PresenceRegularObservations.Graph Index)
  (parameters : Fin slots → Yulang.PresenceLayers.Layer Index),
  Yulang.PresenceTailRegular.Realizes graph (Yulang.PresenceTailRegular.solveGraph graph external parameters) Sum.inl
```

```lean
@Yulang.PresenceTailRegular.realizes_congr : ∀ {slots labels : Nat} {Index Other : Type}
  (graph : Yulang.PresenceTailRegular.Graph slots labels) (left : Yulang.PresenceRegularObservations.Graph Index)
  (leftRoots : Fin slots → Index) (right : Yulang.PresenceRegularObservations.Graph Other)
  (rightRoots : Fin slots → Other),
  (∀ (depth : Nat) (hidden : List Nat) (index : Fin slots) (value : Yulang.SourceDataRuntime.Value),
      Yulang.PresenceMaskedCoalescing.observeMasked left depth hidden (leftRoots index) value ↔
        Yulang.PresenceMaskedCoalescing.observeMasked right depth hidden (rightRoots index) value) →
    (Yulang.PresenceTailRegular.Realizes graph left leftRoots ↔
      Yulang.PresenceTailRegular.Realizes graph right rightRoots)
```

```lean
@Yulang.PresenceTailRegular.solveGraph_retract : ∀ {slots labels : Nat} {Index : Type}
  (graph : Yulang.PresenceTailRegular.Graph slots labels) (original : Yulang.PresenceRegularObservations.Graph Index)
  (roots : Fin slots → Index),
  Yulang.PresenceTailRegular.Realizes graph original roots →
    ∀ (depth : Nat) (outer : List Nat) (index : Fin slots) (value : Yulang.SourceDataRuntime.Value),
      Yulang.PresenceMaskedCoalescing.observeMasked
          (Yulang.PresenceTailRegular.solveGraph graph original fun index => original (roots index)) depth outer
          (Sum.inl index) value ↔
        Yulang.PresenceMaskedCoalescing.observeMasked original depth outer (roots index) value
```

```lean
@Yulang.PresenceTailRegular.solved_instances_exact : ∀ {slots labels : Nat} {Index : Type}
  (graph : Yulang.PresenceTailRegular.Graph slots labels) (original : Yulang.PresenceRegularObservations.Graph Index)
  (roots : Fin slots → Index),
  Yulang.PresenceTailRegular.Realizes graph original roots ↔
    ∃ parameters,
      ∀ (depth : Nat) (hidden : List Nat) (index : Fin slots) (value : Yulang.SourceDataRuntime.Value),
        Yulang.PresenceMaskedCoalescing.observeMasked (Yulang.PresenceTailRegular.solveGraph graph original parameters)
            depth hidden (Sum.inl index) value ↔
          Yulang.PresenceMaskedCoalescing.observeMasked original depth hidden (roots index) value
```

</details>

## ContextualConstructorInspection

任意の有限 rigid node と contextual 値割当てについて、行前順序の下で実 inspector の全 child/row obligation を導く。proper record spine、重複 label、arrow の任意引数を含む。

<details>
<summary>3 個の公開定理の完全な型</summary>

```lean
@Yulang.ContextualConstructorInspection.recordType_probe_field : ∀ {n : Nat} {Row : Type u_1} (leRow : Row → Row → Prop)
  (rank : Nat) (env : Yulang.ProducerContextual.Environment Row) (value : Yulang.NestedValueSolver.Valuation n Row)
  (fields : List (Nat × Fin n)) (label : Nat) (obs : Yulang.ProducerContextual.Observation Row),
  Yulang.ProducerContextual.ProbeAt leRow rank env (Yulang.NestedValueSolver.recordType value fields)
      (Yulang.ProducerContextual.Observation.field label obs) ↔
    ∃ node,
      Yulang.NestedValueSolver.lookupField label fields = some node ∧
        Yulang.ProducerContextual.ProbeAt leRow rank env (value node) obs
```

```lean
@Yulang.ContextualConstructorInspection.record_inspect_sound : ∀ {n : Nat} {Row : Type u_1} (leRow : Row → Row → Prop)
  (value : Yulang.NestedValueSolver.Valuation n Row) (source target : List (Nat × Fin n)),
  Yulang.ProducerContextual.ProducerLe leRow (Yulang.NestedValueSolver.recordType value source)
      (Yulang.NestedValueSolver.recordType value target) →
    Yulang.NestedValueSolver.recordCompatible source target = true ∧
      ∀ (edge : Yulang.NestedValueSolver.Edge n),
        edge ∈ Yulang.NestedValueSolver.recordEdges source target →
          Yulang.ProducerContextual.ProducerLe leRow (value edge.fst) (value edge.snd)
```

```lean
@Yulang.ContextualConstructorInspection.inspect_sound : ∀ {n : Nat} {Row : Type u_1} (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      ∀ (value : Yulang.NestedValueSolver.Valuation n Row) (source target : Yulang.NestedValueSolver.Node n Row)
        {actualSource actualTarget : Yulang.StructuralBase.Ty Row},
        Yulang.NestedValueSolver.Node.Holds value actualSource source →
          Yulang.NestedValueSolver.Node.Holds value actualTarget target →
            Yulang.ProducerContextual.ProducerLe leRow actualSource actualTarget →
              Yulang.ContextualConstructorInspection.InspectionHolds leRow value
                (Yulang.NestedValueSolver.inspect source target)
```

</details>

## ContextualNestedModels

任意の有限 rigid graph と入力辺を実飽和し、任意 regular contextual model を保存・反映する。行前順序と正確な行検査の下で拒否 iff モデル不存在、受理結果から Closed・整合性・二乗 cache 容量を得る。

<details>
<summary>14 個の公開定理の完全な型</summary>

```lean
@Yulang.ContextualNestedModels.nodeLe_trans : ∀ {Row : Type u_1} {State : Type u_2}
  {graph : Yulang.RegularValueTypes.Graph Row State} {leRow : Row → Row → Prop} {a b c : State},
  Yulang.ContextualNestedModels.NodeLe graph leRow a b →
    Yulang.ContextualNestedModels.NodeLe graph leRow b c → Yulang.ContextualNestedModels.NodeLe graph leRow a c
```

```lean
@Yulang.ContextualNestedModels.observe_subtype : ∀ {Row : Type u_1} {State : Type u_2}
  (modelGraph : Yulang.RegularValueTypes.Graph Row State) (leRow : Row → Row → Prop) {left right : State},
  Yulang.ContextualNestedModels.NodeLe modelGraph leRow left right →
    ∀ (depth : Nat),
      Yulang.ProducerContextual.ProducerLe leRow (Yulang.RegularValueTypes.observe modelGraph depth left)
        (Yulang.RegularValueTypes.observe modelGraph depth right)
```

```lean
@Yulang.ContextualNestedModels.inspect_sound : ∀ {n : Nat} {Row : Type u_1} {State : Type u_2}
  (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      ∀ (graph : Yulang.NestedValueSolver.Graph n Row) (modelGraph : Yulang.RegularValueTypes.Graph Row State)
        (valuation : Fin n → State),
        Yulang.ContextualNestedModels.Realizes graph modelGraph leRow valuation →
          ∀ (edge : Yulang.NestedValueSolver.Edge n),
            Yulang.ContextualNestedModels.NodeLe modelGraph leRow (valuation edge.fst) (valuation edge.snd) →
              Yulang.ContextualNestedModels.InspectionHolds modelGraph leRow valuation
                (Yulang.NestedValueSolver.inspect (graph edge.fst) (graph edge.snd))
```

```lean
@Yulang.ContextualNestedModels.rules_valid : ∀ {n : Nat} {Row : Type u_1} {State : Type u_2} (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      ∀ (graph : Yulang.NestedValueSolver.Graph n Row) (constraints : List (Yulang.NestedValueSolver.Edge n))
        (modelGraph : Yulang.RegularValueTypes.Graph Row State) (valuation : Fin n → State),
        Yulang.ContextualNestedModels.Models leRow graph constraints modelGraph valuation →
          ∀ (rule : Yulang.FiniteHorn.Rule (Yulang.NestedValueSolver.Edge n)),
            rule ∈ Yulang.NestedValueSolver.rules graph constraints →
              Yulang.FiniteHorn.Valid
                (fun edge =>
                  Yulang.ContextualNestedModels.NodeLe modelGraph leRow (valuation edge.fst) (valuation edge.snd))
                rule
```

```lean
@Yulang.ContextualNestedModels.saturate_preserves : ∀ {n : Nat} {Row : Type u_1} {State : Type u_2}
  (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      ∀ (graph : Yulang.NestedValueSolver.Graph n Row) (constraints : List (Yulang.NestedValueSolver.Edge n))
        (modelGraph : Yulang.RegularValueTypes.Graph Row State) (valuation : Fin n → State),
        Yulang.ContextualNestedModels.Models leRow graph constraints modelGraph valuation →
          Yulang.ContextualNestedModels.Models leRow graph (Yulang.NestedValueSolver.saturate graph constraints)
            modelGraph valuation
```

```lean
@Yulang.ContextualNestedModels.saturate_models_iff : ∀ {n : Nat} {Row : Type u_1} {State : Type u_2}
  (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      ∀ (graph : Yulang.NestedValueSolver.Graph n Row) (constraints : List (Yulang.NestedValueSolver.Edge n))
        (modelGraph : Yulang.RegularValueTypes.Graph Row State) (valuation : Fin n → State),
        Yulang.ContextualNestedModels.Models leRow graph (Yulang.NestedValueSolver.saturate graph constraints)
            modelGraph valuation ↔
          Yulang.ContextualNestedModels.Models leRow graph constraints modelGraph valuation
```

```lean
@Yulang.ContextualNestedModels.consistent_of_models : ∀ {n : Nat} {Row : Type u_1} {State : Type u_2}
  (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (graph : Yulang.NestedValueSolver.Graph n Row) (cache : List (Yulang.NestedValueSolver.Edge n))
          (modelGraph : Yulang.RegularValueTypes.Graph Row State) (valuation : Fin n → State),
          Yulang.ContextualNestedModels.Models leRow graph cache modelGraph valuation →
            Yulang.NestedValueSolver.consistent rowCheck graph cache = true
```

```lean
@Yulang.ContextualNestedModels.solve_rejects_model : ∀ {n : Nat} {Row : Type u_1} {State : Type u_2}
  (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (graph : Yulang.NestedValueSolver.Graph n Row) (constraints : List (Yulang.NestedValueSolver.Edge n)),
          Yulang.NestedValueSolver.solve rowCheck graph constraints = none →
            ∀ (modelGraph : Yulang.RegularValueTypes.Graph Row State) (valuation : Fin n → State),
              ¬Yulang.ContextualNestedModels.Models leRow graph constraints modelGraph valuation
```

```lean
@Yulang.ContextualNestedModels.solve_rejects : ∀ {n : Nat} {Row : Type u_1} {State : Type u_2}
  (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (graph : Yulang.NestedValueSolver.Graph n Row) (constraints : List (Yulang.NestedValueSolver.Edge n)),
          Yulang.NestedValueSolver.solve rowCheck graph constraints = none →
            ¬∃ modelGraph valuation, Yulang.ContextualNestedModels.Models leRow graph constraints modelGraph valuation
```

```lean
@Yulang.ContextualNestedModels.solve_rejects_finite : ∀ {n : Nat} {Row : Type u_1} (rowCheck : Row → Row → Bool)
  (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (graph : Yulang.NestedValueSolver.Graph n Row) (constraints : List (Yulang.NestedValueSolver.Edge n)),
          Yulang.NestedValueSolver.solve rowCheck graph constraints = none →
            ¬∃ size modelGraph valuation,
                Yulang.ContextualNestedModels.Models leRow graph constraints modelGraph valuation
```

```lean
@Yulang.ContextualNestedModels.old_models_preserved : ∀ {n : Nat} {Row : Type u_1} {State : Type u_2}
  (leRow : Row → Row → Prop),
  (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
    ∀ (graph : Yulang.NestedValueSolver.Graph n Row) (constraints : List (Yulang.NestedValueSolver.Edge n))
      (modelGraph : Yulang.RegularValueTypes.Graph Row State) (valuation : Fin n → State),
      Yulang.RegularNestedModels.Models leRow graph constraints modelGraph valuation →
        Yulang.ContextualNestedModels.Models leRow graph constraints modelGraph valuation
```

```lean
@Yulang.ContextualNestedModels.solve_instantiates_model : ∀ {n : Nat} {Row : Type u_1} {State : Type u_2}
  (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop),
  (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
    (∀ (left right : Row), rowCheck left right = true → leRow left right) →
      ∀ (graph : Yulang.NestedValueSolver.Graph n Row) (constraints cache : List (Yulang.NestedValueSolver.Edge n)),
        Yulang.NestedValueSolver.solve rowCheck graph constraints = some cache →
          ∀ (parameterGraph : Yulang.RegularValueTypes.Graph Row State)
            (parameter : Fin n → Yulang.RegularValueTypes.Layer Row State),
            Yulang.ContextualNestedModels.Models leRow graph constraints
              (Yulang.RegularValueCoalescing.coalesceGraph graph cache parameterGraph parameter) Sum.inl
```

```lean
@Yulang.ContextualNestedModels.solve_none_iff : ∀ {n : Nat} {Row : Type u_1} (rowCheck : Row → Row → Bool)
  (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (graph : Yulang.NestedValueSolver.Graph n Row) (constraints : List (Yulang.NestedValueSolver.Edge n)),
          Yulang.NestedValueSolver.solve rowCheck graph constraints = none ↔
            ¬∃ ModelState model value, Yulang.ContextualNestedModels.Models leRow graph constraints model value
```

```lean
@Yulang.ContextualNestedModels.solve_closed_capacity : ∀ {n : Nat} {Row : Type u_1} (rowCheck : Row → Row → Bool)
  (graph : Yulang.NestedValueSolver.Graph n Row) (constraints cache : List (Yulang.NestedValueSolver.Edge n)),
  Yulang.NestedValueSolver.solve rowCheck graph constraints = some cache →
    Yulang.NestedValueSolver.Closed graph constraints cache ∧
      Yulang.NestedValueSolver.consistent rowCheck graph cache = true ∧ cache.length ≤ n * n
```

</details>

## ContextualBranchSolver

任意の有限 truth/falsity/edge/and/or formula を実際に分岐列挙・飽和し、全独立モデルを実受理 cache へ保存・反映する。空結果 iff モデル不存在、各受理 cache の Closed と容量を証明する。

<details>
<summary>5 個の公開定理の完全な型</summary>

```lean
@Yulang.ContextualBranchSolver.branches_exact : ∀ {n : Nat} (holds : Yulang.NestedValueSolver.Edge n → Prop)
  (formula : Yulang.ContextualBranchSolver.Formula n),
  Yulang.ContextualBranchSolver.Formula.Holds holds formula ↔
    ∃ branch, branch ∈ formula.branches ∧ ∀ (edge : Yulang.NestedValueSolver.Edge n), edge ∈ branch → holds edge
```

```lean
@Yulang.ContextualBranchSolver.mem_solve : ∀ {n : Nat} {Row : Type u_1} (rowCheck : Row → Row → Bool)
  (graph : Yulang.NestedValueSolver.Graph n Row) (formula : Yulang.ContextualBranchSolver.Formula n)
  (branch : Yulang.ContextualBranchSolver.Branch n),
  branch ∈ Yulang.ContextualBranchSolver.solve rowCheck graph formula ↔
    branch.input ∈ formula.branches ∧ Yulang.NestedValueSolver.solve rowCheck graph branch.input = some branch.cache
```

```lean
@Yulang.ContextualBranchSolver.solve_models_exact : ∀ {n : Nat} {Row : Type u_1} {State : Type u_2}
  (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (graph : Yulang.NestedValueSolver.Graph n Row) (formula : Yulang.ContextualBranchSolver.Formula n)
          (modelGraph : Yulang.RegularValueTypes.Graph Row State) (value : Fin n → State),
          Yulang.ContextualBranchSolver.Models leRow graph formula modelGraph value ↔
            ∃ branch,
              branch ∈ Yulang.ContextualBranchSolver.solve rowCheck graph formula ∧
                Yulang.ContextualNestedModels.Models leRow graph branch.cache modelGraph value
```

```lean
@Yulang.ContextualBranchSolver.accepted_closed_capacity : ∀ {n : Nat} {Row : Type u_1} (rowCheck : Row → Row → Bool)
  (graph : Yulang.NestedValueSolver.Graph n Row) (formula : Yulang.ContextualBranchSolver.Formula n)
  (branch : Yulang.ContextualBranchSolver.Branch n),
  branch ∈ Yulang.ContextualBranchSolver.solve rowCheck graph formula →
    Yulang.NestedValueSolver.Closed graph branch.input branch.cache ∧
      Yulang.NestedValueSolver.consistent rowCheck graph branch.cache = true ∧ branch.cache.length ≤ n * n
```

```lean
@Yulang.ContextualBranchSolver.solve_nil_iff : ∀ {n : Nat} {Row : Type u_1} (rowCheck : Row → Row → Bool)
  (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (graph : Yulang.NestedValueSolver.Graph n Row) (formula : Yulang.ContextualBranchSolver.Formula n),
          Yulang.ContextualBranchSolver.solve rowCheck graph formula = [] ↔
            ¬∃ ModelState modelGraph value, Yulang.ContextualBranchSolver.Models leRow graph formula modelGraph value
```

</details>

## ContextualTypeConstraintGraph

行前順序の下で実 compiler は元共有変数の各割当てを保存・反映し、同じ regular carrier の contextual model へ接続する。正確な行検査の下で実入口の拒否 iff supported かつ充足不能。

<details>
<summary>12 個の公開定理の完全な型</summary>

```lean
@Yulang.ContextualTypeConstraintGraph.latticeRules : ∀ {Row : Type u_1} (empty : Row) (join : Row → Row → Row)
  (leRow : Row → Row → Prop),
  Yulang.TypeConstraintGraph.LatticeRules (Yulang.ContextualTypeConstraintGraph.model Row empty join leRow)
```

```lean
@Yulang.ContextualTypeConstraintGraph.recordMeaning_eq : ∀ {Row : Type u_1} {n : Nat} (empty : Row)
  (join : Row → Row → Row) (leRow : Row → Row → Prop) (value : Fin n → Yulang.ContextualTypeConstraintGraph.Value Row)
  (fields : List (Nat × Fin n)),
  Yulang.TypeConstraintGraph.recordMeaning (Yulang.ContextualTypeConstraintGraph.model Row empty join leRow) value
      fields =
    Yulang.RegularInferenceModel.recordMeaning value fields
```

```lean
@Yulang.ContextualTypeConstraintGraph.recordMeaning_equivalent : ∀ {Row : Type u_1} {n : Nat} (empty : Row)
  (join : Row → Row → Row) (leRow : Row → Row → Prop) (fields : List (Nat × Fin n))
  (left right : Fin n → Yulang.ContextualTypeConstraintGraph.Value Row),
  (∀ (field : Nat × Fin n),
      field ∈ fields →
        Yulang.TypeConstraintGraphEquivalence.Equivalent
          (Yulang.ContextualTypeConstraintGraph.model Row empty join leRow) (left field.snd) (right field.snd)) →
    Yulang.TypeConstraintGraphEquivalence.Equivalent (Yulang.ContextualTypeConstraintGraph.model Row empty join leRow)
      (Yulang.TypeConstraintGraph.recordMeaning (Yulang.ContextualTypeConstraintGraph.model Row empty join leRow) left
        fields)
      (Yulang.TypeConstraintGraph.recordMeaning (Yulang.ContextualTypeConstraintGraph.model Row empty join leRow) right
        fields)
```

```lean
@Yulang.ContextualTypeConstraintGraph.congruenceRules : ∀ {Row : Type u_1} (empty : Row) (join : Row → Row → Row)
  (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      Yulang.TypeConstraintGraphEquivalence.CongruenceRules
        (Yulang.ContextualTypeConstraintGraph.model Row empty join leRow)
```

```lean
@Yulang.ContextualTypeConstraintGraph.semanticNodeMeaning_iff : ∀ {Row : Type u_1} {n : Nat} (empty : Row)
  (join : Row → Row → Row) (leRow : Row → Row → Prop) (value : Fin n → Yulang.ContextualTypeConstraintGraph.Value Row)
  (actual : Yulang.ContextualTypeConstraintGraph.Value Row) (node : Yulang.NestedValueSolver.Node n Row),
  Yulang.TypeConstraintGraphEquivalence.SemanticNodeMeaning
      (Yulang.ContextualTypeConstraintGraph.model Row empty join leRow) value actual node ↔
    node ≠ Yulang.NestedValueSolver.Node.var →
      Yulang.ProducerContextualRegular.ProducerEq (Yulang.RegularInferenceModel.graph Row) leRow actual
        (Yulang.RegularValueTypes.Layer.map (fun index => Yulang.RegularInferenceModel.State.node (value index))
          (Yulang.RigidValueLayers.rigidLayer node))
```

```lean
@Yulang.ContextualTypeConstraintGraph.semanticGraphModels_iff : ∀ {Row : Type u_1} {n : Nat} (empty : Row)
  (join : Row → Row → Row) (leRow : Row → Row → Prop) (graph : Yulang.NestedValueSolver.Graph n Row)
  (constraints : List (Yulang.NestedValueSolver.Edge n))
  (value : Fin n → Yulang.ContextualTypeConstraintGraph.Value Row),
  Yulang.TypeConstraintGraphEquivalence.SemanticGraphModels
      (Yulang.ContextualTypeConstraintGraph.model Row empty join leRow) graph constraints value ↔
    Yulang.ContextualNestedModels.Models leRow graph constraints (Yulang.RegularInferenceModel.graph Row) fun index =>
      Yulang.RegularInferenceModel.State.node (value index)
```

```lean
@Yulang.ContextualTypeConstraintGraph.compile_assignment_exact : ∀ {Row : Type u_1} {m : Nat} (empty : Row)
  (join : Row → Row → Row) (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      ∀ (rows : Fin m → Row) (problem : Yulang.TypeConstraintGraph.Problem m)
        (compiled : Yulang.TypeConstraintGraph.Compiled m Row),
        Yulang.TypeConstraintGraph.compile empty join rows problem = some compiled →
          ∀ (input : Fin m → Yulang.ContextualTypeConstraintGraph.Value Row),
            Yulang.TypeConstraintGraph.Holds (Yulang.ContextualTypeConstraintGraph.model Row empty join leRow) rows
                input problem ↔
              ∃ value,
                (Yulang.ContextualNestedModels.Models leRow compiled.graph compiled.constraints
                    (Yulang.RegularInferenceModel.graph Row) fun index =>
                    Yulang.RegularInferenceModel.State.node (value index)) ∧
                  compiled.restrict value = input
```

```lean
@Yulang.ContextualTypeConstraintGraph.compile_output_instances_exact : ∀ {Row : Type u_1} {m : Nat} (empty : Row)
  (join : Row → Row → Row) (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      ∀ (rows : Fin m → Row) (problem : Yulang.TypeConstraintGraph.Problem m)
        (compiled : Yulang.TypeConstraintGraph.Compiled m Row),
        Yulang.TypeConstraintGraph.compile empty join rows problem = some compiled →
          ∀ (output : Fin m) (expected : Yulang.ContextualTypeConstraintGraph.Value Row),
            (∃ input,
                Yulang.TypeConstraintGraph.Holds (Yulang.ContextualTypeConstraintGraph.model Row empty join leRow) rows
                    input problem ∧
                  Yulang.ProducerContextualRegular.ProducerLe (Yulang.RegularInferenceModel.graph Row) leRow
                    (input output) expected) ↔
              ∃ value,
                (Yulang.ContextualNestedModels.Models leRow compiled.graph compiled.constraints
                    (Yulang.RegularInferenceModel.graph Row) fun index =>
                    Yulang.RegularInferenceModel.State.node (value index)) ∧
                  Yulang.ProducerContextualRegular.ProducerLe (Yulang.RegularInferenceModel.graph Row) leRow
                    (value (compiled.input output)) expected
```

```lean
@Yulang.ContextualTypeConstraintGraph.solve_solution : ∀ {Row : Type u_1} {n : Nat} (rowCheck : Row → Row → Bool)
  (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true → leRow left right) →
        ∀ (graph : Yulang.NestedValueSolver.Graph n Row) (constraints cache : List (Yulang.NestedValueSolver.Edge n)),
          Yulang.NestedValueSolver.solve rowCheck graph constraints = some cache →
            ∀ (parameter : Fin n → Yulang.ContextualTypeConstraintGraph.Value Row),
              Yulang.ContextualNestedModels.Models leRow graph constraints (Yulang.RegularInferenceModel.graph Row)
                fun index =>
                Yulang.RegularInferenceModel.State.node
                  (Yulang.RegularInferenceModel.solution graph cache parameter index)
```

```lean
@Yulang.ContextualTypeConstraintGraph.solve_none_iff : ∀ {Row : Type u_1} {n : Nat} (rowCheck : Row → Row → Bool)
  (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (graph : Yulang.NestedValueSolver.Graph n Row) (constraints : List (Yulang.NestedValueSolver.Edge n)),
          Yulang.NestedValueSolver.solve rowCheck graph constraints = none ↔
            ¬∃ value,
                Yulang.ContextualNestedModels.Models leRow graph constraints (Yulang.RegularInferenceModel.graph Row)
                  fun index => Yulang.RegularInferenceModel.State.node (value index)
```

```lean
@Yulang.ContextualTypeConstraintGraph.compile_solve_none_iff : ∀ {Row : Type u_1} {m : Nat} (empty : Row)
  (join : Row → Row → Row) (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (rows : Fin m → Row) (problem : Yulang.TypeConstraintGraph.Problem m)
          (compiled : Yulang.TypeConstraintGraph.Compiled m Row),
          Yulang.TypeConstraintGraph.compile empty join rows problem = some compiled →
            (Yulang.NestedValueSolver.solve rowCheck compiled.graph compiled.constraints = none ↔
              ¬∃ input,
                  Yulang.TypeConstraintGraph.Holds (Yulang.ContextualTypeConstraintGraph.model Row empty join leRow)
                    rows input problem)
```

```lean
@Yulang.ContextualTypeConstraintGraph.infer_rejected_iff : ∀ {Row : Type u_1} {m : Nat} (empty : Row)
  (join : Row → Row → Row) (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (rows : Fin m → Row) (problem : Yulang.TypeConstraintGraph.Problem m),
          (Yulang.TypeConstraintInference.infer empty join rowCheck rows problem).status =
              Yulang.TypeConstraintInference.Status.rejected ↔
            Yulang.TypeConstraintInference.supported problem = true ∧
              ¬∃ input,
                  Yulang.TypeConstraintGraph.Holds (Yulang.ContextualTypeConstraintGraph.model Row empty join leRow)
                    rows input problem
```

</details>

## TypeSimplificationCheckCost

任意の型項対で型/行 equality と record spine の走査を含む参照 checker が実 symbolicCheck と Bool 一致。入力から再帰深さを選び、行込みサイズ S で (S+1)*128^S 以下となる。

<details>
<summary>14 個の公開定理の完全な型</summary>

```lean
@Yulang.TypeSimplificationCheckCost.rowEqCount_value : ∀ {n : Nat} (first last : Yulang.Inference.RowTerm (Fin n)),
  (Yulang.TypeSimplificationCheckCost.rowEqCount first last).fst = decide (first = last)
```

```lean
@Yulang.TypeSimplificationCheckCost.rowEqCount_bound : ∀ {n : Nat} (first last : Yulang.Inference.RowTerm (Fin n)),
  (Yulang.TypeSimplificationCheckCost.rowEqCount first last).snd ≤ Yulang.InferenceSubstitutionCost.rowNodes first
```

```lean
@Yulang.TypeSimplificationCheckCost.tyEqCount_value : ∀ {n : Nat} (first last : Yulang.Inference.TyTerm (Fin n)),
  (Yulang.TypeSimplificationCheckCost.tyEqCount first last).fst = decide (first = last)
```

```lean
@Yulang.TypeSimplificationCheckCost.tyEqCount_bound : ∀ {n : Nat} (first last : Yulang.Inference.TyTerm (Fin n)),
  (Yulang.TypeSimplificationCheckCost.tyEqCount first last).snd ≤ Yulang.InferenceSubstitutionCost.tyNodes first
```

```lean
@Yulang.TypeSimplificationCheckCost.spineCount_value : ∀ {n : Nat} (term : Yulang.Inference.TyTerm (Fin n)),
  (Yulang.TypeSimplificationCheckCost.spineCount term).fst = Yulang.ValueBoundElimination.recordSpine term
```

```lean
@Yulang.TypeSimplificationCheckCost.spineCount_bound : ∀ {n : Nat} (term : Yulang.Inference.TyTerm (Fin n)),
  (Yulang.TypeSimplificationCheckCost.spineCount term).snd ≤ Yulang.InferenceSubstitutionCost.tyNodes term
```

```lean
@Yulang.TypeSimplificationCheckCost.fuelCount_value : ∀ {n : Nat} (fuel : Nat)
  (source target : Yulang.Inference.TyTerm (Fin n)),
  Yulang.TypeSimplification.nodes source + Yulang.TypeSimplification.nodes target ≤ fuel →
    (Yulang.TypeSimplificationCheckCost.fuelCount fuel source target).fst =
      Yulang.TypeSimplification.symbolicCheck source target
```

```lean
@Yulang.TypeSimplificationCheckCost.step_bound : ∀ {n : Nat}
  (next : Yulang.Inference.TyTerm (Fin n) → Yulang.Inference.TyTerm (Fin n) → Bool × Nat)
  (source target : Yulang.Inference.TyTerm (Fin n)) (size budget : Nat),
  Yulang.InferenceSubstitutionCost.tyNodes source + Yulang.InferenceSubstitutionCost.tyNodes target ≤ size →
    size + 1 ≤ budget →
      (∀ (first last : Yulang.Inference.TyTerm (Fin n)),
          Yulang.InferenceSubstitutionCost.tyNodes first + Yulang.InferenceSubstitutionCost.tyNodes last ≤ size →
            (next first last).snd ≤ budget) →
        (Yulang.TypeSimplificationCheckCost.step next source target).snd ≤ 128 * budget
```

```lean
@Yulang.TypeSimplificationCheckCost.fuelCount_bound : ∀ {n : Nat} (fuel : Nat)
  (source target : Yulang.Inference.TyTerm (Fin n)) (size : Nat),
  Yulang.InferenceSubstitutionCost.tyNodes source + Yulang.InferenceSubstitutionCost.tyNodes target ≤ size →
    (Yulang.TypeSimplificationCheckCost.fuelCount fuel source target).snd ≤ (size + 1) * 128 ^ fuel
```

```lean
@Yulang.TypeSimplificationCheckCost.symbolicCount_value : ∀ {n : Nat} (source target : Yulang.Inference.TyTerm (Fin n)),
  (Yulang.TypeSimplificationCheckCost.symbolicCount source target).fst =
    Yulang.TypeSimplification.symbolicCheck source target
```

```lean
@Yulang.TypeSimplificationCheckCost.symbolicCount_bound : ∀ {n : Nat} (source target : Yulang.Inference.TyTerm (Fin n)),
  (Yulang.TypeSimplificationCheckCost.symbolicCount source target).snd ≤
    (Yulang.InferenceSubstitutionCost.tyNodes source + Yulang.InferenceSubstitutionCost.tyNodes target + 1) *
      128 ^ (Yulang.TypeSimplification.nodes source + Yulang.TypeSimplification.nodes target)
```

```lean
@Yulang.TypeSimplificationCheckCost.nodes_le_total : ∀ {n : Nat} (term : Yulang.Inference.TyTerm (Fin n)),
  Yulang.TypeSimplification.nodes term ≤ Yulang.InferenceSubstitutionCost.tyNodes term
```

```lean
Yulang.TypeSimplificationCheckCost.checkBudget_mono : ∀ (first last : Nat),
  first ≤ last →
    Yulang.TypeSimplificationCheckCost.checkBudget first ≤ Yulang.TypeSimplificationCheckCost.checkBudget last
```

```lean
@Yulang.TypeSimplificationCheckCost.symbolicCount_size_bound : ∀ {n : Nat}
  (source target : Yulang.Inference.TyTerm (Fin n)) (size : Nat),
  Yulang.InferenceSubstitutionCost.tyNodes source + Yulang.InferenceSubstitutionCost.tyNodes target ≤ size →
    (Yulang.TypeSimplificationCheckCost.symbolicCount source target).snd ≤
      Yulang.TypeSimplificationCheckCost.checkBudget size
```

</details>

## ContextualValueBounds

任意行関係・任意 flat bound problem の任意独立 contextual 解を、実 expand の共有 parameter に入れると全 node で要求同値になる。旧構造解を前提にしない。

<details>
<summary>12 個の公開定理の完全な型</summary>

```lean
@Yulang.ContextualValueBounds.bottom_le : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  (type : Yulang.StructuralBase.Ty Row), Yulang.ProducerContextual.ProducerLe leRow Yulang.StructuralBase.Ty.bottom type
```

```lean
@Yulang.ContextualValueBounds.le_top : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  (type : Yulang.StructuralBase.Ty Row), Yulang.ProducerContextual.ProducerLe leRow type Yulang.StructuralBase.Ty.top
```

```lean
@Yulang.ContextualValueBounds.inter_le_left : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  (first last : Yulang.StructuralBase.Ty Row), Yulang.ProducerContextual.ProducerLe leRow (first.inter last) first
```

```lean
@Yulang.ContextualValueBounds.inter_le_right : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  (first last : Yulang.StructuralBase.Ty Row), Yulang.ProducerContextual.ProducerLe leRow (first.inter last) last
```

```lean
@Yulang.ContextualValueBounds.joinTypes_le_iff : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  (types : List (Yulang.StructuralBase.Ty Row)) (upper : Yulang.StructuralBase.Ty Row),
  Yulang.ProducerContextual.ProducerLe leRow (Yulang.ValueBounds.joinTypes types) upper ↔
    ∀ (type : Yulang.StructuralBase.Ty Row), type ∈ types → Yulang.ProducerContextual.ProducerLe leRow type upper
```

```lean
@Yulang.ContextualValueBounds.le_meetTypes_iff : ∀ {Row : Type u_1} {leRow : Row → Row → Prop}
  (lower : Yulang.StructuralBase.Ty Row) (types : List (Yulang.StructuralBase.Ty Row)),
  Yulang.ProducerContextual.ProducerLe leRow lower (Yulang.ValueUpperBounds.meetTypes types) ↔
    ∀ (type : Yulang.StructuralBase.Ty Row), type ∈ types → Yulang.ProducerContextual.ProducerLe leRow lower type
```

```lean
@Yulang.ContextualValueBounds.reaches_le : ∀ {n : Nat} {Row : Type u_1} {leRow : Row → Row → Prop}
  {problem : Yulang.ValueBounds.Problem n Row} {value : Yulang.ValueBounds.Valuation n Row},
  Yulang.ContextualValueBounds.Models leRow problem value →
    ∀ {source target : Fin n},
      Yulang.ValueBounds.Reaches problem source target →
        Yulang.ProducerContextual.ProducerLe leRow (value source) (value target)
```

```lean
@Yulang.ContextualValueBounds.least_below : ∀ {n : Nat} {Row : Type u_1} {leRow : Row → Row → Prop}
  {problem : Yulang.ValueBounds.Problem n Row} {value : Yulang.ValueBounds.Valuation n Row},
  Yulang.ContextualValueBounds.Models leRow problem value →
    ∀ (target : Fin n),
      Yulang.ProducerContextual.ProducerLe leRow (Yulang.ValueBounds.least problem target) (value target)
```

```lean
@Yulang.ContextualValueBounds.greatest_above : ∀ {n : Nat} {Row : Type u_1} {leRow : Row → Row → Prop}
  {problem : Yulang.ValueBounds.Problem n Row} {value : Yulang.ValueBounds.Valuation n Row},
  Yulang.ContextualValueBounds.Models leRow problem value →
    ∀ (source : Fin n),
      Yulang.ProducerContextual.ProducerLe leRow (value source) (Yulang.ValueUpperBounds.greatest problem source)
```

```lean
@Yulang.ContextualValueBounds.variablePart_le_iff : ∀ {n : Nat} {Row : Type u_1} {leRow : Row → Row → Prop}
  (problem : Yulang.ValueBounds.Problem n Row) (parameters : Yulang.ValueBounds.Valuation n Row) (target : Fin n)
  (upper : Yulang.StructuralBase.Ty Row),
  Yulang.ProducerContextual.ProducerLe leRow (Yulang.ValueBoundSchemes.variablePart problem parameters target) upper ↔
    ∀ (source : Fin n),
      Yulang.ValueBounds.Reaches problem source target →
        Yulang.ProducerContextual.ProducerLe leRow
          ((parameters source).inter (Yulang.ValueUpperBounds.greatest problem source)) upper
```

```lean
@Yulang.ContextualValueBounds.contribution_below : ∀ {n : Nat} {Row : Type u_1} {leRow : Row → Row → Prop}
  (problem : Yulang.ValueBounds.Problem n Row) (parameters : Yulang.ValueBounds.Valuation n Row)
  (source target : Fin n),
  Yulang.ValueBounds.Reaches problem source target →
    Yulang.ProducerContextual.ProducerLe leRow
      ((parameters source).inter (Yulang.ValueUpperBounds.greatest problem source))
      (Yulang.ValueBoundSchemes.variablePart problem parameters target)
```

```lean
@Yulang.ContextualValueBounds.expand_equivalent : ∀ {n : Nat} {Row : Type u_1} {leRow : Row → Row → Prop}
  {problem : Yulang.ValueBounds.Problem n Row} {value : Yulang.ValueBounds.Valuation n Row},
  Yulang.ContextualValueBounds.Models leRow problem value →
    ∀ (target : Fin n),
      Yulang.ProducerContextual.ProducerEq leRow (Yulang.ValueBoundSchemes.expand problem value target) (value target)
```

</details>

## ContextualCoalescing

任意の行前順序と正確な行検査の下で、実 coalescer の全自由 parameter family が全独立 regular contextual 解を回収する。全入力定理は成功を前提とせず実返却 cache を結論に含む。

<details>
<summary>11 個の公開定理の完全な型</summary>

```lean
@Yulang.ContextualCoalescing.rigidLayer_eval_equivalent : ∀ {n : Nat} {Row : Type u_1} (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      ∀ (left right : Fin n → Yulang.StructuralBase.Ty Row),
        (∀ (index : Fin n), Yulang.ProducerContextual.ProducerEq leRow (left index) (right index)) →
          ∀ (node : Yulang.NestedValueSolver.Node n Row),
            Yulang.ProducerContextual.ProducerEq leRow
              (Yulang.RegularValueTypes.Layer.eval left (Yulang.RigidValueLayers.rigidLayer node))
              (Yulang.RegularValueTypes.Layer.eval right (Yulang.RigidValueLayers.rigidLayer node))
```

```lean
@Yulang.ContextualCoalescing.template_models_of_edges : ∀ {n : Nat} {Row : Type u_1}
  (graph : Yulang.NestedValueSolver.Graph n Row) (cache : List (Yulang.NestedValueSolver.Edge n))
  (assignment value : Fin n → Yulang.StructuralBase.Ty Row) (leRow : Row → Row → Prop),
  (∀ (index : Fin n),
      graph index ≠ Yulang.NestedValueSolver.Node.var →
        Yulang.ProducerContextual.ProducerEq leRow
          (Yulang.RegularValueTypes.Layer.eval assignment (Yulang.RigidValueLayers.rigidLayer (graph index)))
          (value index)) →
    (∀ (edge : Yulang.NestedValueSolver.Edge n),
        edge ∈ cache → Yulang.ProducerContextual.ProducerLe leRow (value edge.fst) (value edge.snd)) →
      Yulang.ContextualValueBounds.Models leRow
        (Yulang.LayerBoundTemplates.instantiateProblem assignment (Yulang.RegularValueCoalescing.template graph cache))
        value
```

```lean
@Yulang.ContextualCoalescing.coalesceGraph_retract_at : ∀ {n : Nat} {Row : Type u_1} {ParameterState : Type u_2}
  (graph : Yulang.NestedValueSolver.Graph n Row) (cache : List (Yulang.NestedValueSolver.Edge n))
  (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      ∀ (original : Yulang.RegularValueTypes.Graph Row ParameterState) (value : Fin n → ParameterState),
        (∀ (index : Fin n),
            graph index ≠ Yulang.NestedValueSolver.Node.var →
              Yulang.ProducerContextualRegular.ProducerLe original leRow (original (value index))
                  (Yulang.RegularValueTypes.Layer.map value (Yulang.RigidValueLayers.rigidLayer (graph index))) ∧
                Yulang.ProducerContextualRegular.ProducerLe original leRow
                  (Yulang.RegularValueTypes.Layer.map value (Yulang.RigidValueLayers.rigidLayer (graph index)))
                  (original (value index))) →
          (∀ (edge : Yulang.NestedValueSolver.Edge n),
              edge ∈ cache → Yulang.ContextualNestedModels.NodeLe original leRow (value edge.fst) (value edge.snd)) →
            ∀ (depth : Nat) (index : Fin n),
              Yulang.ProducerContextual.ProducerEq leRow
                (Yulang.RegularValueTypes.observe
                  (Yulang.RegularValueCoalescing.coalesceGraph graph cache original fun index => original (value index))
                  depth (Sum.inl index))
                (Yulang.RegularValueTypes.observe original depth (value index))
```

```lean
@Yulang.ContextualCoalescing.coalesceGraph_retraction : ∀ {n : Nat} {Row : Type u_1} {ParameterState : Type u_2}
  (graph : Yulang.NestedValueSolver.Graph n Row) (cache : List (Yulang.NestedValueSolver.Edge n))
  (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      ∀ (original : Yulang.RegularValueTypes.Graph Row ParameterState) (value : Fin n → ParameterState),
        (∀ (index : Fin n),
            graph index ≠ Yulang.NestedValueSolver.Node.var →
              Yulang.ProducerContextualRegular.ProducerLe original leRow (original (value index))
                  (Yulang.RegularValueTypes.Layer.map value (Yulang.RigidValueLayers.rigidLayer (graph index))) ∧
                Yulang.ProducerContextualRegular.ProducerLe original leRow
                  (Yulang.RegularValueTypes.Layer.map value (Yulang.RigidValueLayers.rigidLayer (graph index)))
                  (original (value index))) →
          (∀ (edge : Yulang.NestedValueSolver.Edge n),
              edge ∈ cache → Yulang.ContextualNestedModels.NodeLe original leRow (value edge.fst) (value edge.snd)) →
            ∀ (index : Fin n),
              Yulang.ContextualNestedModels.NodeLe
                  (Yulang.RegularValueCoalescing.coalesceGraph graph cache original fun index => original (value index))
                  leRow (Sum.inl index) (Sum.inr (value index)) ∧
                Yulang.ContextualNestedModels.NodeLe
                  (Yulang.RegularValueCoalescing.coalesceGraph graph cache original fun index => original (value index))
                  leRow (Sum.inr (value index)) (Sum.inl index)
```

```lean
@Yulang.ContextualCoalescing.rigidLayer_map_equivalent : ∀ {n : Nat} {Row : Type u_1} {ParameterState : Type u_2}
  (modelGraph : Yulang.RegularValueTypes.Graph Row ParameterState) (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      ∀ (left right : Fin n → ParameterState),
        Yulang.ContextualCoalescing.Equivalent modelGraph leRow left right →
          ∀ (node : Yulang.NestedValueSolver.Node n Row),
            Yulang.ProducerContextualRegular.ProducerEq modelGraph leRow
              (Yulang.RegularValueTypes.Layer.map left (Yulang.RigidValueLayers.rigidLayer node))
              (Yulang.RegularValueTypes.Layer.map right (Yulang.RigidValueLayers.rigidLayer node))
```

```lean
@Yulang.ContextualCoalescing.models_equivalent : ∀ {n : Nat} {Row : Type u_1} {ParameterState : Type u_2}
  (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      ∀ (graph : Yulang.NestedValueSolver.Graph n Row) (constraints : List (Yulang.NestedValueSolver.Edge n))
        (modelGraph : Yulang.RegularValueTypes.Graph Row ParameterState) (left right : Fin n → ParameterState),
        Yulang.ContextualNestedModels.Models leRow graph constraints modelGraph left →
          Yulang.ContextualCoalescing.Equivalent modelGraph leRow left right →
            Yulang.ContextualNestedModels.Models leRow graph constraints modelGraph right
```

```lean
@Yulang.ContextualCoalescing.producerLe_morphism : ∀ {Row : Type u_1} {ParameterState : Type u_2} {Target : Type u_3}
  (source : Yulang.RegularValueTypes.Graph Row ParameterState) (target : Yulang.RegularValueTypes.Graph Row Target)
  (leRow : Row → Row → Prop) (rename : ParameterState → Target),
  (∀ (state : ParameterState), Yulang.RegularValueTypes.Layer.map rename (source state) = target (rename state)) →
    ∀ (left right : Yulang.RegularValueTypes.Layer Row ParameterState),
      Yulang.ProducerContextualRegular.ProducerLe target leRow (Yulang.RegularValueTypes.Layer.map rename left)
          (Yulang.RegularValueTypes.Layer.map rename right) ↔
        Yulang.ProducerContextualRegular.ProducerLe source leRow left right
```

```lean
@Yulang.ContextualCoalescing.nodeLe_morphism : ∀ {Row : Type u_1} {ParameterState : Type u_2} {Target : Type u_3}
  (source : Yulang.RegularValueTypes.Graph Row ParameterState) (target : Yulang.RegularValueTypes.Graph Row Target)
  (leRow : Row → Row → Prop) (rename : ParameterState → Target),
  (∀ (state : ParameterState), Yulang.RegularValueTypes.Layer.map rename (source state) = target (rename state)) →
    ∀ (left right : ParameterState),
      Yulang.ContextualNestedModels.NodeLe target leRow (rename left) (rename right) ↔
        Yulang.ContextualNestedModels.NodeLe source leRow left right
```

```lean
@Yulang.ContextualCoalescing.parameter_models_iff : ∀ {n : Nat} {Row : Type u_1} {ParameterState : Type u_2}
  (graph : Yulang.NestedValueSolver.Graph n Row) (constraints cache : List (Yulang.NestedValueSolver.Edge n))
  (leRow : Row → Row → Prop) (parameterGraph : Yulang.RegularValueTypes.Graph Row ParameterState)
  (parameter : Fin n → Yulang.RegularValueTypes.Layer Row ParameterState) (value : Fin n → ParameterState),
  (Yulang.ContextualNestedModels.Models leRow graph constraints
      (Yulang.RegularValueCoalescing.coalesceGraph graph cache parameterGraph parameter) fun index =>
      Sum.inr (value index)) ↔
    Yulang.ContextualNestedModels.Models leRow graph constraints parameterGraph value
```

```lean
@Yulang.ContextualCoalescing.solve_models_exact : ∀ {n : Nat} {Row : Type u_1} {ParameterState : Type u_2}
  (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (graph : Yulang.NestedValueSolver.Graph n Row) (constraints cache : List (Yulang.NestedValueSolver.Edge n)),
          Yulang.NestedValueSolver.solve rowCheck graph constraints = some cache →
            ∀ (original : Yulang.RegularValueTypes.Graph Row ParameterState) (value : Fin n → ParameterState),
              Yulang.ContextualNestedModels.Models leRow graph constraints original value ↔
                ∃ parameter,
                  Yulang.ContextualCoalescing.Equivalent
                    (Yulang.RegularValueCoalescing.coalesceGraph graph cache original parameter) leRow Sum.inl
                    fun index => Sum.inr (value index)
```

```lean
@Yulang.ContextualCoalescing.models_exact : ∀ {n : Nat} {Row : Type u_1} {ParameterState : Type u_2}
  (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (graph : Yulang.NestedValueSolver.Graph n Row) (constraints : List (Yulang.NestedValueSolver.Edge n))
          (original : Yulang.RegularValueTypes.Graph Row ParameterState) (value : Fin n → ParameterState),
          Yulang.ContextualNestedModels.Models leRow graph constraints original value ↔
            ∃ cache,
              Yulang.NestedValueSolver.solve rowCheck graph constraints = some cache ∧
                ∃ parameter,
                  Yulang.ContextualCoalescing.Equivalent
                    (Yulang.RegularValueCoalescing.coalesceGraph graph cache original parameter) leRow Sum.inl
                    fun index => Sum.inr (value index)
```

</details>

## ContextualRegularInference

任意の独立解・出力 root・target を実 RegularInferenceModel.solution と同じ carrier で扱い、全自由 parameter family のモデル/出力 instance 完全性を示す。

<details>
<summary>6 個の公開定理の完全な型</summary>

```lean
@Yulang.ContextualRegularInference.solution_nodeLe : ∀ {n : Nat} {Row : Type u_1}
  (source : Yulang.NestedValueSolver.Graph n Row) (cache : List (Yulang.NestedValueSolver.Edge n))
  (parameter : Fin n → Yulang.RegularInferenceModel.Ty Row) (leRow : Row → Row → Prop)
  (left right : Fin n ⊕ Yulang.RegularInferenceModel.State Row),
  Yulang.ContextualNestedModels.NodeLe (Yulang.RegularInferenceModel.graph Row) leRow
      (Yulang.RegularInferenceModel.solutionRef source cache parameter left)
      (Yulang.RegularInferenceModel.solutionRef source cache parameter right) ↔
    Yulang.ContextualNestedModels.NodeLe
      (Yulang.RegularValueCoalescing.coalesceGraph source cache (Yulang.RegularInferenceModel.graph Row) parameter)
      leRow left right
```

```lean
@Yulang.ContextualRegularInference.solve_models_exact : ∀ {n : Nat} {Row : Type u_1} (rowCheck : Row → Row → Bool)
  (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (source : Yulang.NestedValueSolver.Graph n Row) (constraints cache : List (Yulang.NestedValueSolver.Edge n)),
          Yulang.NestedValueSolver.solve rowCheck source constraints = some cache →
            ∀ (value : Fin n → Yulang.RegularInferenceModel.Ty Row),
              Yulang.ContextualRegularInference.Models source constraints leRow value ↔
                ∃ parameter,
                  ∀ (index : Fin n),
                    Yulang.ContextualRegularInference.Equivalent leRow
                      (Yulang.RegularInferenceModel.solution source cache parameter index) (value index)
```

```lean
@Yulang.ContextualRegularInference.solve_solution : ∀ {n : Nat} {Row : Type u_1} (rowCheck : Row → Row → Bool)
  (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (source : Yulang.NestedValueSolver.Graph n Row) (constraints cache : List (Yulang.NestedValueSolver.Edge n)),
          Yulang.NestedValueSolver.solve rowCheck source constraints = some cache →
            ∀ (parameter : Fin n → Yulang.RegularInferenceModel.Ty Row),
              Yulang.ContextualRegularInference.Models source constraints leRow
                (Yulang.RegularInferenceModel.solution source cache parameter)
```

```lean
@Yulang.ContextualRegularInference.models_exact : ∀ {n : Nat} {Row : Type u_1} (rowCheck : Row → Row → Bool)
  (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (source : Yulang.NestedValueSolver.Graph n Row) (constraints : List (Yulang.NestedValueSolver.Edge n))
          (value : Fin n → Yulang.RegularInferenceModel.Ty Row),
          Yulang.ContextualRegularInference.Models source constraints leRow value ↔
            ∃ cache,
              Yulang.NestedValueSolver.solve rowCheck source constraints = some cache ∧
                ∃ parameter,
                  ∀ (index : Fin n),
                    Yulang.ContextualRegularInference.Equivalent leRow
                      (Yulang.RegularInferenceModel.solution source cache parameter index) (value index)
```

```lean
@Yulang.ContextualRegularInference.solve_instances_exact : ∀ {n : Nat} {Row : Type u_1} (rowCheck : Row → Row → Bool)
  (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (source : Yulang.NestedValueSolver.Graph n Row) (constraints cache : List (Yulang.NestedValueSolver.Edge n)),
          Yulang.NestedValueSolver.solve rowCheck source constraints = some cache →
            ∀ (root : Fin n) (target : Yulang.RegularInferenceModel.Ty Row),
              Yulang.ContextualRegularInference.ConstrainedInstance source constraints root leRow target ↔
                Yulang.ContextualRegularInference.SchemeInstance source cache root leRow target
```

```lean
@Yulang.ContextualRegularInference.instances_exact : ∀ {n : Nat} {Row : Type u_1} (rowCheck : Row → Row → Bool)
  (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (source : Yulang.NestedValueSolver.Graph n Row) (constraints : List (Yulang.NestedValueSolver.Edge n))
          (root : Fin n) (target : Yulang.RegularInferenceModel.Ty Row),
          Yulang.ContextualRegularInference.ConstrainedInstance source constraints root leRow target ↔
            ∃ cache,
              Yulang.NestedValueSolver.solve rowCheck source constraints = some cache ∧
                Yulang.ContextualRegularInference.SchemeInstance source cache root leRow target
```

</details>

## ContextualBranchInstances

任意の有限 formula の独立モデル/出力 instance と、実受理 branch の自由 parameter による実 solution block の同値/subsumption が一致する。成功・Closed・解・fuel は前提でない。

<details>
<summary>3 個の公開定理の完全な型</summary>

```lean
@Yulang.ContextualBranchInstances.models_exact : ∀ {n : Nat} {Row : Type u_1} (rowCheck : Row → Row → Bool)
  (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (source : Yulang.NestedValueSolver.Graph n Row) (formula : Yulang.ContextualBranchSolver.Formula n)
          (value : Fin n → Yulang.RegularInferenceModel.Ty Row),
          Yulang.ContextualBranchInstances.Models leRow source formula value ↔
            ∃ branch,
              branch ∈ Yulang.ContextualBranchSolver.solve rowCheck source formula ∧
                ∃ parameter,
                  ∀ (index : Fin n),
                    Yulang.ContextualRegularInference.Equivalent leRow
                      (Yulang.RegularInferenceModel.solution source branch.cache parameter index) (value index)
```

```lean
@Yulang.ContextualBranchInstances.instances_exact : ∀ {n : Nat} {Row : Type u_1} (rowCheck : Row → Row → Bool)
  (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (source : Yulang.NestedValueSolver.Graph n Row) (formula : Yulang.ContextualBranchSolver.Formula n)
          (root : Fin n) (target : Yulang.RegularInferenceModel.Ty Row),
          Yulang.ContextualBranchInstances.ConstrainedInstance leRow source formula root target ↔
            ∃ branch,
              branch ∈ Yulang.ContextualBranchSolver.solve rowCheck source formula ∧
                ∃ parameter,
                  Yulang.ContextualRegularInference.Le leRow
                    (Yulang.RegularInferenceModel.solution source branch.cache parameter root) target
```

```lean
@Yulang.ContextualBranchInstances.solve_nil_iff : ∀ {n : Nat} {Row : Type u_1} (rowCheck : Row → Row → Bool)
  (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (source : Yulang.NestedValueSolver.Graph n Row) (formula : Yulang.ContextualBranchSolver.Formula n),
          Yulang.ContextualBranchSolver.solve rowCheck source formula = [] ↔
            ¬∃ value, Yulang.ContextualBranchInstances.Models leRow source formula value
```

</details>

## ContextualTypeConstraintInference

行前順序と正確な rowCheck の下で、任意 supported 型制約の元割当て/出力 instance と実既存 infer の新 scheme family が一致する。全入力 status を充足可能性と support で分類する。

<details>
<summary>12 個の公開定理の完全な型</summary>

```lean
@Yulang.ContextualTypeConstraintInference.supported_eq_compile : ∀ {m : Nat} {Row : Type u_1} (empty : Row)
  (join : Row → Row → Row) (rows : Fin m → Row) (problem : Yulang.TypeConstraintGraph.Problem m),
  Yulang.ContextualTypeConstraintInference.supported problem =
    (Yulang.TypeConstraintGraph.compile empty join rows problem).isSome
```

```lean
@Yulang.ContextualTypeConstraintInference.infer_correct : ∀ {m : Nat} {Row : Type u_1} (empty : Row)
  (join : Row → Row → Row) (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (rows : Fin m → Row) (problem : Yulang.TypeConstraintGraph.Problem m),
          Yulang.ContextualTypeConstraintInference.Result.Correct empty join leRow rows problem
            (Yulang.ContextualTypeConstraintInference.infer empty join rowCheck rows problem)
```

```lean
@Yulang.ContextualTypeConstraintInference.Scheme.models_instantiate : ∀ {m : Nat} {Row : Type u_1}
  (scheme : Yulang.ContextualTypeConstraintInference.Scheme m Row) (leRow : Row → Row → Prop)
  (parameter : Fin scheme.size → Yulang.ContextualTypeConstraintInference.Value Row),
  scheme.Models leRow (Yulang.ContextualTypeConstraintInference.Scheme.instantiate scheme parameter)
```

```lean
@Yulang.ContextualTypeConstraintInference.Scheme.models_instances_iff : ∀ {m : Nat} {Row : Type u_1}
  (scheme : Yulang.ContextualTypeConstraintInference.Scheme m Row) (leRow : Row → Row → Prop) (output : Fin m)
  (expected : Yulang.ContextualTypeConstraintInference.Value Row),
  (∃ input, scheme.Models leRow input ∧ Yulang.ContextualRegularInference.Le leRow (input output) expected) ↔
    scheme.Instance leRow output expected
```

```lean
@Yulang.ContextualTypeConstraintInference.Result.models_instances_iff : ∀ {m : Nat} {Row : Type u_1}
  (result : Yulang.ContextualTypeConstraintInference.Result m Row) (leRow : Row → Row → Prop) (output : Fin m)
  (expected : Yulang.ContextualTypeConstraintInference.Value Row),
  (∃ input,
      Yulang.ContextualTypeConstraintInference.Result.Models leRow input result ∧
        Yulang.ContextualRegularInference.Le leRow (input output) expected) ↔
    Yulang.ContextualTypeConstraintInference.Result.Instance leRow output expected result
```

```lean
@Yulang.ContextualTypeConstraintInference.infer_unsupported_iff : ∀ {m : Nat} {Row : Type u_1} (empty : Row)
  (join : Row → Row → Row) (rowCheck : Row → Row → Bool) (rows : Fin m → Row)
  (problem : Yulang.TypeConstraintGraph.Problem m),
  Yulang.ContextualTypeConstraintInference.Result.status
        (Yulang.ContextualTypeConstraintInference.infer empty join rowCheck rows problem) =
      Yulang.TypeConstraintInference.Status.unsupported ↔
    Yulang.ContextualTypeConstraintInference.supported problem = false
```

```lean
@Yulang.ContextualTypeConstraintInference.infer_models_exact : ∀ {m : Nat} {Row : Type u_1} (empty : Row)
  (join : Row → Row → Row) (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (rows : Fin m → Row) (problem : Yulang.TypeConstraintGraph.Problem m),
          Yulang.ContextualTypeConstraintInference.supported problem = true →
            ∀ (input : Fin m → Yulang.ContextualTypeConstraintInference.Value Row),
              Yulang.TypeConstraintGraph.Holds (Yulang.ContextualTypeConstraintInference.model Row empty join leRow)
                  rows input problem ↔
                Yulang.ContextualTypeConstraintInference.Result.Models leRow input
                  (Yulang.ContextualTypeConstraintInference.infer empty join rowCheck rows problem)
```

```lean
@Yulang.ContextualTypeConstraintInference.infer_instances_exact : ∀ {m : Nat} {Row : Type u_1} (empty : Row)
  (join : Row → Row → Row) (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (rows : Fin m → Row) (problem : Yulang.TypeConstraintGraph.Problem m),
          Yulang.ContextualTypeConstraintInference.supported problem = true →
            ∀ (output : Fin m) (expected : Yulang.ContextualTypeConstraintInference.Value Row),
              Yulang.ContextualTypeConstraintInference.SourceInstance empty join leRow rows problem output expected ↔
                Yulang.ContextualTypeConstraintInference.Result.Instance leRow output expected
                  (Yulang.ContextualTypeConstraintInference.infer empty join rowCheck rows problem)
```

```lean
@Yulang.ContextualTypeConstraintInference.infer_rejected_iff : ∀ {m : Nat} {Row : Type u_1} (empty : Row)
  (join : Row → Row → Row) (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (rows : Fin m → Row) (problem : Yulang.TypeConstraintGraph.Problem m),
          Yulang.ContextualTypeConstraintInference.Result.status
                (Yulang.ContextualTypeConstraintInference.infer empty join rowCheck rows problem) =
              Yulang.TypeConstraintInference.Status.rejected ↔
            Yulang.ContextualTypeConstraintInference.supported problem = true ∧
              ¬∃ input,
                  Yulang.TypeConstraintGraph.Holds (Yulang.ContextualTypeConstraintInference.model Row empty join leRow)
                    rows input problem
```

```lean
@Yulang.ContextualTypeConstraintInference.infer_inferred_iff : ∀ {m : Nat} {Row : Type u_1} (empty : Row)
  (join : Row → Row → Row) (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (rows : Fin m → Row) (problem : Yulang.TypeConstraintGraph.Problem m),
          Yulang.ContextualTypeConstraintInference.Result.status
                (Yulang.ContextualTypeConstraintInference.infer empty join rowCheck rows problem) =
              Yulang.TypeConstraintInference.Status.inferred ↔
            Yulang.ContextualTypeConstraintInference.supported problem = true ∧
              ∃ input,
                Yulang.TypeConstraintGraph.Holds (Yulang.ContextualTypeConstraintInference.model Row empty join leRow)
                  rows input problem
```

```lean
@Yulang.ContextualTypeConstraintInference.infer_inferred_sound : ∀ {m : Nat} {Row : Type u_1} (empty : Row)
  (join : Row → Row → Row) (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (rows : Fin m → Row) (problem : Yulang.TypeConstraintGraph.Problem m)
          (scheme : Yulang.ContextualTypeConstraintInference.Scheme m Row),
          Yulang.ContextualTypeConstraintInference.infer empty join rowCheck rows problem =
              Yulang.TypeConstraintInference.Result.inferred scheme →
            ∀ (parameter : Fin scheme.size → Yulang.ContextualTypeConstraintInference.Value Row),
              Yulang.TypeConstraintGraph.Holds (Yulang.ContextualTypeConstraintInference.model Row empty join leRow)
                rows (Yulang.ContextualTypeConstraintInference.Scheme.instantiate scheme parameter) problem
```

```lean
@Yulang.ContextualTypeConstraintInference.infer_inferred_instances_exact : ∀ {m : Nat} {Row : Type u_1} (empty : Row)
  (join : Row → Row → Row) (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop),
  (∀ (row : Row), leRow row row) →
    (∀ {a b c : Row}, leRow a b → leRow b c → leRow a c) →
      (∀ (left right : Row), rowCheck left right = true ↔ leRow left right) →
        ∀ (rows : Fin m → Row) (problem : Yulang.TypeConstraintGraph.Problem m)
          (scheme : Yulang.ContextualTypeConstraintInference.Scheme m Row),
          Yulang.ContextualTypeConstraintInference.infer empty join rowCheck rows problem =
              Yulang.TypeConstraintInference.Result.inferred scheme →
            ∀ (output : Fin m) (expected : Yulang.ContextualTypeConstraintInference.Value Row),
              Yulang.ContextualTypeConstraintInference.SourceInstance empty join leRow rows problem output expected ↔
                scheme.Instance leRow output expected
```

</details>

## ContextualJointConstraintInference

任意の反対称な行 join 代数と supported paired 制約について、全元行/値割当てと実 symbolic joint scheme の自由 parameter family を一致させる。意味的 rowCheck は algorithm の入力にしない。

<details>
<summary>14 個の公開定理の完全な型</summary>

```lean
@Yulang.ContextualJointConstraintInference.rowHolds_iff : ∀ {n : Nat} {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row) (rows : Fin n → Row) (constraints : Yulang.RowFlowSchemes.Problem n),
  Yulang.ConstraintProblems.RowHolds (Yulang.ContextualJointConstraintInference.model algebra) rows constraints ↔
    Yulang.RowFlowSchemes.Models algebra constraints rows
```

```lean
@Yulang.ContextualJointConstraintInference.fixed_infer_at_rows : ∀ {n : Nat} {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row) (rowCheck : Row → Row → Bool) (rows : Fin n → Row)
  (types : Yulang.TypeConstraintGraph.Problem n)
  (symbolic : Yulang.TypeConstraintGraph.Compiled n (Yulang.Inference.RowTerm (Fin n))),
  Yulang.TypeConstraintRowInstantiation.symbolicCompile types = some symbolic →
    ∀ (cache : List (Yulang.NestedValueSolver.Edge symbolic.size)),
      Yulang.NestedValueSolver.solve rowCheck
            (Yulang.NestedRowRequirements.instantiateGraph algebra rows symbolic.graph) symbolic.constraints =
          some cache →
        Yulang.ContextualTypeConstraintInference.infer algebra.empty algebra.join rowCheck rows types =
          Yulang.TypeConstraintInference.Result.inferred
            (Yulang.ContextualTypeConstraintInference.Scheme.ofCompiled
              (Yulang.TypeConstraintRowInstantiation.instantiateCompiled algebra.empty algebra.join rows symbolic)
              cache)
```

```lean
@Yulang.ContextualJointConstraintInference.fixed_scheme_instantiate : ∀ {n : Nat} {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row) (rows : Fin n → Row)
  (symbolic : Yulang.TypeConstraintGraph.Compiled n (Yulang.Inference.RowTerm (Fin n)))
  (cache : List (Yulang.NestedValueSolver.Edge symbolic.size))
  (parameter : Fin symbolic.size → Yulang.ContextualJointConstraintInference.Value Row),
  Yulang.ContextualTypeConstraintInference.Scheme.instantiate
      (Yulang.ContextualTypeConstraintInference.Scheme.ofCompiled
        (Yulang.TypeConstraintRowInstantiation.instantiateCompiled algebra.empty algebra.join rows symbolic) cache)
      parameter =
    fun index =>
    Yulang.RegularInferenceModel.solution (Yulang.NestedRowRequirements.instantiateGraph algebra rows symbolic.graph)
      cache parameter (symbolic.input index)
```

```lean
@Yulang.ContextualJointConstraintInference.infer_unsupported_iff : ∀ {n : Nat}
  (problem : Yulang.ConstraintProblems.Problem n),
  (Yulang.ContextualJointConstraintInference.infer problem).status =
      Yulang.JointConstraintInference.Status.unsupported ↔
    Yulang.ContextualJointConstraintInference.supported problem = false
```

```lean
@Yulang.ContextualJointConstraintInference.infer_correct : ∀ {n : Nat} {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (problem : Yulang.ConstraintProblems.Problem n),
      Yulang.ContextualJointConstraintInference.Result.Correct algebra problem
        (Yulang.ContextualJointConstraintInference.infer problem)
```

```lean
@Yulang.ContextualJointConstraintInference.Scheme.models_instantiate : ∀ {n : Nat} {Row : Type u_1}
  (scheme : Yulang.ContextualJointConstraintInference.Scheme n) (algebra : Yulang.RowFlowSchemes.Algebra Row)
  (rowParameter : Fin n → Row) (valueParameter : Fin scheme.size → Yulang.ContextualJointConstraintInference.Value Row),
  scheme.Models algebra
    (Yulang.ContextualJointConstraintInference.Scheme.values scheme algebra rowParameter valueParameter)
    (Yulang.ContextualJointConstraintInference.Scheme.rows scheme algebra rowParameter)
```

```lean
@Yulang.ContextualJointConstraintInference.Scheme.models_instances_iff : ∀ {n : Nat} {Row : Type u_1}
  (scheme : Yulang.ContextualJointConstraintInference.Scheme n) (algebra : Yulang.RowFlowSchemes.Algebra Row)
  (output : Fin n) (expected : Yulang.Inference.Comp (Yulang.ContextualJointConstraintInference.model algebra)),
  (∃ values rows,
      scheme.Models algebra values rows ∧
        Yulang.Inference.Comp.le (Yulang.ContextualJointConstraintInference.model algebra) (values output, rows output)
          expected) ↔
    scheme.Instance algebra output expected
```

```lean
@Yulang.ContextualJointConstraintInference.Result.models_instances_iff : ∀ {n : Nat} {Row : Type u_1}
  (result : Yulang.ContextualJointConstraintInference.Result n) (algebra : Yulang.RowFlowSchemes.Algebra Row)
  (output : Fin n) (expected : Yulang.Inference.Comp (Yulang.ContextualJointConstraintInference.model algebra)),
  (∃ values rows,
      Yulang.ContextualJointConstraintInference.Result.Models algebra values rows result ∧
        Yulang.Inference.Comp.le (Yulang.ContextualJointConstraintInference.model algebra) (values output, rows output)
          expected) ↔
    Yulang.ContextualJointConstraintInference.Result.Instance algebra output expected result
```

```lean
@Yulang.ContextualJointConstraintInference.infer_models_exact : ∀ {n : Nat} {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (problem : Yulang.ConstraintProblems.Problem n),
      Yulang.ContextualJointConstraintInference.supported problem = true →
        ∀ (values : Fin n → Yulang.ContextualJointConstraintInference.Value Row) (rows : Fin n → Row),
          Yulang.ConstraintProblems.Problem.Holds (Yulang.ContextualJointConstraintInference.model algebra) problem
              values rows ↔
            Yulang.ContextualJointConstraintInference.Result.Models algebra values rows
              (Yulang.ContextualJointConstraintInference.infer problem)
```

```lean
@Yulang.ContextualJointConstraintInference.infer_instances_exact : ∀ {n : Nat} {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (problem : Yulang.ConstraintProblems.Problem n),
      Yulang.ContextualJointConstraintInference.supported problem = true →
        ∀ (output : Fin n) (expected : Yulang.Inference.Comp (Yulang.ContextualJointConstraintInference.model algebra)),
          Yulang.ConstraintProblems.Problem.Instance (Yulang.ContextualJointConstraintInference.model algebra) problem
              output expected ↔
            Yulang.ContextualJointConstraintInference.Result.Instance algebra output expected
              (Yulang.ContextualJointConstraintInference.infer problem)
```

```lean
@Yulang.ContextualJointConstraintInference.infer_rejected_iff : ∀ {n : Nat} {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (problem : Yulang.ConstraintProblems.Problem n),
      (Yulang.ContextualJointConstraintInference.infer problem).status =
          Yulang.JointConstraintInference.Status.rejected ↔
        Yulang.ContextualJointConstraintInference.supported problem = true ∧
          ¬∃ values rows,
              Yulang.ConstraintProblems.Problem.Holds (Yulang.ContextualJointConstraintInference.model algebra) problem
                values rows
```

```lean
@Yulang.ContextualJointConstraintInference.infer_inferred_iff : ∀ {n : Nat} {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (problem : Yulang.ConstraintProblems.Problem n),
      (Yulang.ContextualJointConstraintInference.infer problem).status =
          Yulang.JointConstraintInference.Status.inferred ↔
        Yulang.ContextualJointConstraintInference.supported problem = true ∧
          ∃ values rows,
            Yulang.ConstraintProblems.Problem.Holds (Yulang.ContextualJointConstraintInference.model algebra) problem
              values rows
```

```lean
@Yulang.ContextualJointConstraintInference.infer_inferred_sound : ∀ {n : Nat} {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (problem : Yulang.ConstraintProblems.Problem n) (scheme : Yulang.ContextualJointConstraintInference.Scheme n),
      Yulang.ContextualJointConstraintInference.infer problem = Yulang.JointConstraintInference.Result.inferred scheme →
        ∀ (rowParameter : Fin n → Row)
          (valueParameter : Fin scheme.size → Yulang.ContextualJointConstraintInference.Value Row),
          Yulang.ConstraintProblems.Problem.Holds (Yulang.ContextualJointConstraintInference.model algebra) problem
            (Yulang.ContextualJointConstraintInference.Scheme.values scheme algebra rowParameter valueParameter)
            (Yulang.ContextualJointConstraintInference.Scheme.rows scheme algebra rowParameter)
```

```lean
@Yulang.ContextualJointConstraintInference.infer_inferred_instances_exact : ∀ {n : Nat} {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (problem : Yulang.ConstraintProblems.Problem n) (scheme : Yulang.ContextualJointConstraintInference.Scheme n),
      Yulang.ContextualJointConstraintInference.infer problem = Yulang.JointConstraintInference.Result.inferred scheme →
        ∀ (output : Fin n) (expected : Yulang.Inference.Comp (Yulang.ContextualJointConstraintInference.model algebra)),
          Yulang.ConstraintProblems.Problem.Instance (Yulang.ContextualJointConstraintInference.model algebra) problem
              output expected ↔
            scheme.Instance algebra output expected
```

</details>

## TypeSimplificationCost

任意の型項で計数付き4段階 pipeline と候補表構築が実 simplifyAll と同じ値を返し、parameter 数と行込みサイズの明示関数以下となる。instance 保存は既存 StructuralBase モデルについて述べる。

<details>
<summary>35 個の公開定理の完全な型</summary>

```lean
@Yulang.TypeSimplificationCost.occursCount_value : ∀ {n : Nat} (positive : Bool) (index : Fin n)
  (term : Yulang.Inference.TyTerm (Fin n)),
  (Yulang.TypeSimplificationCost.occursCount positive index term).fst =
    Yulang.TypeSimplification.occurs positive index term
```

```lean
@Yulang.TypeSimplificationCost.occursCount_steps : ∀ {n : Nat} (positive : Bool) (index : Fin n)
  (term : Yulang.Inference.TyTerm (Fin n)),
  (Yulang.TypeSimplificationCost.occursCount positive index term).snd = Yulang.TypeSimplification.nodes term
```

```lean
@Yulang.TypeSimplificationCost.supportedCount_value : ∀ {n : Nat} (term : Yulang.Inference.TyTerm (Fin n)),
  (Yulang.TypeSimplificationCost.supportedCount term).fst = Yulang.TypeSimplification.supported term
```

```lean
@Yulang.TypeSimplificationCost.supportedCount_bound : ∀ {n : Nat} (term : Yulang.Inference.TyTerm (Fin n)) (size : Nat),
  Yulang.InferenceSubstitutionCost.tyNodes term ≤ size →
    (Yulang.TypeSimplificationCost.supportedCount term).snd ≤ Yulang.InferenceSubstitutionCost.tyNodes term * (size + 1)
```

```lean
@Yulang.TypeSimplificationCost.replacementCount_value : ∀ {n : Nat} (term : Yulang.Inference.TyTerm (Fin n))
  (index : Fin n),
  (Yulang.TypeSimplificationCost.replacementCount term index).fst = Yulang.TypeSimplification.replacement term index
```

```lean
@Yulang.TypeSimplificationCost.replacementCount_bound : ∀ {n : Nat} (term : Yulang.Inference.TyTerm (Fin n))
  (index : Fin n),
  (Yulang.TypeSimplificationCost.replacementCount term index).snd ≤
    1 + 2 * Yulang.InferenceSubstitutionCost.tyNodes term
```

```lean
@Yulang.TypeSimplificationCost.valuesCount_value : ∀ {n : Nat} (term : Yulang.Inference.TyTerm (Fin n))
  (replacement : Fin n → Yulang.Inference.TyTerm (Fin n) × Nat),
  (Yulang.TypeSimplificationCost.valuesCount term replacement).fst =
    Yulang.TypeSimplification.substituteValues term fun index => (replacement index).fst
```

```lean
@Yulang.TypeSimplificationCost.valuesCount_bound : ∀ {n : Nat} (term : Yulang.Inference.TyTerm (Fin n))
  (replacement : Fin n → Yulang.Inference.TyTerm (Fin n) × Nat) (cost : Nat),
  (∀ (index : Fin n), (replacement index).snd ≤ cost) →
    (Yulang.TypeSimplificationCost.valuesCount term replacement).snd ≤
      Yulang.InferenceSubstitutionCost.tyNodes term * (cost + 1)
```

```lean
@Yulang.TypeSimplificationCost.simplifyCount_value : ∀ {n : Nat} (term : Yulang.Inference.TyTerm (Fin n)),
  (Yulang.TypeSimplificationCost.simplifyCount term).fst = Yulang.TypeSimplification.simplify term
```

```lean
@Yulang.TypeSimplificationCost.simplifyCount_bound : ∀ {n : Nat} (term : Yulang.Inference.TyTerm (Fin n)) (size : Nat),
  Yulang.InferenceSubstitutionCost.tyNodes term ≤ size →
    (Yulang.TypeSimplificationCost.simplifyCount term).snd ≤ size * (2 + 2 * size)
```

```lean
@Yulang.TypeSimplificationCost.simplifySafeCount_value : ∀ {n : Nat} (term : Yulang.Inference.TyTerm (Fin n)),
  (Yulang.TypeSimplificationCost.simplifySafeCount term).fst = Yulang.TypeSimplification.simplifySafe term
```

```lean
@Yulang.TypeSimplificationCost.simplifySafeCount_bound : ∀ {n : Nat} (term : Yulang.Inference.TyTerm (Fin n))
  (size : Nat),
  Yulang.InferenceSubstitutionCost.tyNodes term ≤ size →
    (Yulang.TypeSimplificationCost.simplifySafeCount term).snd ≤ Yulang.TypeSimplificationCost.varianceBudget size
```

```lean
@Yulang.TypeSimplificationCost.applySandwichCount_value : ∀ {n : Nat} (index : Fin n)
  (fixed term : Yulang.Inference.TyTerm (Fin n)),
  (Yulang.TypeSimplificationCost.applySandwichCount index fixed term).fst =
    Yulang.TypeSimplification.applySandwich index fixed term
```

```lean
@Yulang.TypeSimplificationCost.applySandwichCount_bound : ∀ {n : Nat} (index : Fin n)
  (fixed term : Yulang.Inference.TyTerm (Fin n)) (size : Nat),
  Yulang.InferenceSubstitutionCost.tyNodes fixed ≤ 1 →
    Yulang.InferenceSubstitutionCost.tyNodes term ≤ size →
      (Yulang.TypeSimplificationCost.applySandwichCount index fixed term).snd ≤
        Yulang.TypeSimplificationCost.sandwichBudget size
```

```lean
@Yulang.TypeSimplificationCost.mergeCheckCount_value : ∀ {n : Nat} (positive : Bool) (first second : Fin n)
  (term : Yulang.Inference.TyTerm (Fin n)),
  (Yulang.TypeSimplificationCost.mergeCheckCount positive first second term).fst =
    Yulang.TypeSimplification.mergeCheck positive first second term
```

```lean
@Yulang.TypeSimplificationCost.mergeCheckCount_bound : ∀ {n : Nat} (positive : Bool) (first second : Fin n)
  (term : Yulang.Inference.TyTerm (Fin n)) (size : Nat),
  Yulang.InferenceSubstitutionCost.tyNodes term ≤ size →
    (Yulang.TypeSimplificationCost.mergeCheckCount positive first second term).snd ≤
      1 + 4 * size + Yulang.TypeSimplificationCheckCost.checkBudget (4 * size)
```

```lean
@Yulang.TypeSimplificationCost.applyMergeCount_value : ∀ {n : Nat} (first second : Fin n)
  (term : Yulang.Inference.TyTerm (Fin n)),
  (Yulang.TypeSimplificationCost.applyMergeCount first second term).fst =
    Yulang.TypeSimplification.applyMerge first second term
```

```lean
@Yulang.TypeSimplificationCost.applyMergeCount_bound : ∀ {n : Nat} (first second : Fin n)
  (term : Yulang.Inference.TyTerm (Fin n)) (size : Nat),
  Yulang.InferenceSubstitutionCost.tyNodes term ≤ size →
    (Yulang.TypeSimplificationCost.applyMergeCount first second term).snd ≤
      Yulang.TypeSimplificationCost.mergeBudget size
```

```lean
@Yulang.TypeSimplificationCost.mergeCandidatesCount_value : ∀ {n : Nat} (candidates : List (Fin n × Fin n))
  (term : Yulang.Inference.TyTerm (Fin n)),
  (Yulang.TypeSimplificationCost.mergeCandidatesCount candidates term).fst =
    Yulang.TypeSimplification.mergeCandidates candidates term
```

```lean
@Yulang.TypeSimplificationCost.mergeCandidatesCount_bound : ∀ {n : Nat} (candidates : List (Fin n × Fin n))
  (term : Yulang.Inference.TyTerm (Fin n)) (size : Nat),
  Yulang.InferenceSubstitutionCost.tyNodes term ≤ size →
    (Yulang.TypeSimplificationCost.mergeCandidatesCount candidates term).snd ≤
      candidates.length * (Yulang.TypeSimplificationCost.mergeBudget size + 1)
```

```lean
@Yulang.TypeSimplificationCost.sandwichCandidatesCount_value : ∀ {n : Nat}
  (candidates : List (Fin n × Yulang.Inference.TyTerm (Fin n))) (term : Yulang.Inference.TyTerm (Fin n)),
  (Yulang.TypeSimplificationCost.sandwichCandidatesCount candidates term).fst =
    Yulang.TypeSimplification.sandwichCandidates candidates term
```

```lean
@Yulang.TypeSimplificationCost.sandwichCandidatesCount_bound : ∀ {n : Nat}
  (candidates : List (Fin n × Yulang.Inference.TyTerm (Fin n))),
  (∀ (pair : Fin n × Yulang.Inference.TyTerm (Fin n)),
      pair ∈ candidates → Yulang.InferenceSubstitutionCost.tyNodes pair.snd ≤ 1) →
    ∀ (term : Yulang.Inference.TyTerm (Fin n)) (size : Nat),
      Yulang.InferenceSubstitutionCost.tyNodes term ≤ size →
        (Yulang.TypeSimplificationCost.sandwichCandidatesCount candidates term).snd ≤
          candidates.length * (Yulang.TypeSimplificationCost.sandwichBudget size + 1)
```

```lean
@Yulang.TypeSimplificationCost.mapCount_value : ∀ {α : Type u_1} {β : Type u_2} (map : α → β) (entries : List α),
  (Yulang.TypeSimplificationCost.mapCount map entries).fst = List.map map entries
```

```lean
@Yulang.TypeSimplificationCost.mapCount_steps : ∀ {α : Type u_1} {β : Type u_2} (map : α → β) (entries : List α),
  (Yulang.TypeSimplificationCost.mapCount map entries).snd = entries.length
```

```lean
@Yulang.TypeSimplificationCost.appendCount_value : ∀ {α : Type u_1} (first last : List α),
  (Yulang.TypeSimplificationCost.appendCount first last).fst = first ++ last
```

```lean
@Yulang.TypeSimplificationCost.appendCount_steps : ∀ {α : Type u_1} (first last : List α),
  (Yulang.TypeSimplificationCost.appendCount first last).snd = first.length
```

```lean
@Yulang.TypeSimplificationCost.productCount_value : ∀ {α : Type u_1} {β : Type u_2} (first : List α) (last : List β),
  (Yulang.TypeSimplificationCost.productCount first last).fst =
    List.flatMap (fun entry => List.map (fun x => (entry, x)) last) first
```

```lean
@Yulang.TypeSimplificationCost.productCount_steps : ∀ {α : Type u_1} {β : Type u_2} (first : List α) (last : List β),
  (Yulang.TypeSimplificationCost.productCount first last).snd = first.length * (1 + 2 * last.length)
```

```lean
@Yulang.TypeSimplificationCost.mergeAllCount_value : ∀ {n : Nat} (term : Yulang.Inference.TyTerm (Fin n)),
  (Yulang.TypeSimplificationCost.mergeAllCount term).fst = Yulang.TypeSimplification.mergeAll term
```

```lean
@Yulang.TypeSimplificationCost.mergeAllCount_bound : ∀ {n : Nat} (term : Yulang.Inference.TyTerm (Fin n)) (size : Nat),
  Yulang.InferenceSubstitutionCost.tyNodes term ≤ size →
    (Yulang.TypeSimplificationCost.mergeAllCount term).snd ≤ Yulang.TypeSimplificationCost.mergeAllBudget n size
```

```lean
@Yulang.TypeSimplificationCost.sandwichAllCount_value : ∀ {n : Nat} (term : Yulang.Inference.TyTerm (Fin n)),
  (Yulang.TypeSimplificationCost.sandwichAllCount term).fst = Yulang.TypeSimplification.sandwichAll term
```

```lean
@Yulang.TypeSimplificationCost.sandwichAllCount_bound : ∀ {n : Nat} (term : Yulang.Inference.TyTerm (Fin n))
  (size : Nat),
  Yulang.InferenceSubstitutionCost.tyNodes term ≤ size →
    (Yulang.TypeSimplificationCost.sandwichAllCount term).snd ≤ Yulang.TypeSimplificationCost.sandwichAllBudget n size
```

```lean
@Yulang.TypeSimplificationCost.simplifyAllCount_value : ∀ {n : Nat} (term : Yulang.Inference.TyTerm (Fin n)),
  (Yulang.TypeSimplificationCost.simplifyAllCount term).fst = Yulang.TypeSimplification.simplifyAll term
```

```lean
@Yulang.TypeSimplificationCost.simplifyAllCount_bound : ∀ {n : Nat} (term : Yulang.Inference.TyTerm (Fin n)),
  (Yulang.TypeSimplificationCost.simplifyAllCount term).snd ≤
    Yulang.TypeSimplificationCost.totalBudget n (Yulang.InferenceSubstitutionCost.tyNodes term)
```

```lean
@Yulang.TypeSimplificationCost.simplifyAllCount_instances_exact : ∀ {RowType : Type u_1} {n : Nat} (empty : RowType)
  (join : RowType → RowType → RowType) (leRow : RowType → RowType → Prop),
  (∀ (row : RowType), leRow row row) →
    (∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c) →
      ∀ (rows : Fin n → RowType) (term : Yulang.Inference.TyTerm (Fin n)) (expected : Yulang.StructuralBase.Ty RowType),
        Yulang.TypeSimplification.Instances empty join leRow rows
            (Yulang.TypeSimplificationCost.simplifyAllCount term).fst expected ↔
          Yulang.TypeSimplification.Instances empty join leRow rows term expected
```

</details>

## ContextualSourcePrincipalInference

任意の反対称な行 join 代数、旧 supported source、任意結果で、実 infer の新 instance と独立 Typing が同値。RecordFree では checker 結果を前提にせず主型性・拒否完全性・unsupported 排除を得る。

<details>
<summary>18 個の公開定理の完全な型</summary>

```lean
Yulang.ContextualSourcePrincipalInference.collect_none_iff : ∀
  (clauses : List (Yulang.ConstraintNormalForm.Clause (Option Empty))),
  Yulang.ContextualSourcePrincipalInference.collect clauses = none ↔
    ∃ clause,
      clause ∈ clauses ∧
        Yulang.ContextualJointConstraintInference.supported (Yulang.ConstraintProblems.split clause.pack) = false
```

```lean
Yulang.ContextualSourcePrincipalInference.collect_some_supported : ∀
  (clauses : List (Yulang.ConstraintNormalForm.Clause (Option Empty)))
  (result : Yulang.ContextualSourcePrincipalInference.Principal),
  Yulang.ContextualSourcePrincipalInference.collect clauses = some result →
    ∀ (clause : Yulang.ConstraintNormalForm.Clause (Option Empty)),
      clause ∈ clauses →
        Yulang.ContextualJointConstraintInference.supported (Yulang.ConstraintProblems.split clause.pack) = true
```

```lean
Yulang.ContextualSourcePrincipalInference.infer_unsupported_iff : ∀ (expression : Yulang.Inference.Expr),
  (Yulang.ContextualSourcePrincipalInference.infer expression).status =
      Yulang.SourcePrincipalInference.Status.unsupported ↔
    Yulang.ContextualSourcePrincipalInference.supported expression = false
```

```lean
Yulang.ContextualSourcePrincipalInference.infer_optional_unsupported : ∀ (expression : Yulang.Inference.Expr),
  expression.requiredFieldsOnly = false →
    Yulang.ContextualSourcePrincipalInference.infer expression = Yulang.SourcePrincipalInference.Result.unsupported
```

```lean
Yulang.ContextualSourcePrincipalInference.recordFree_supported : ∀ (expression : Yulang.Inference.Expr),
  Yulang.SourceConstraintSupport.RecordFree expression →
    Yulang.ContextualSourcePrincipalInference.supported expression = true
```

```lean
Yulang.ContextualSourcePrincipalInference.recordFree_ne_unsupported : ∀ (expression : Yulang.Inference.Expr),
  Yulang.SourceConstraintSupport.RecordFree expression →
    (Yulang.ContextualSourcePrincipalInference.infer expression).status ≠
      Yulang.SourcePrincipalInference.Status.unsupported
```

```lean
@Yulang.ContextualSourcePrincipalInference.collect_instances_exact : ∀ {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (clauses : List (Yulang.ConstraintNormalForm.Clause (Option Empty)))
      (result : Yulang.ContextualSourcePrincipalInference.Principal),
      Yulang.ContextualSourcePrincipalInference.collect clauses = some result →
        ∀ (target : Yulang.Inference.Comp (Yulang.ContextualSourcePrincipalInference.model algebra)),
          Yulang.ContextualSourcePrincipalInference.Principal.Instance algebra result target ↔
            ∃ clause,
              clause ∈ clauses ∧
                Yulang.ConstraintProblems.Problem.Instance (Yulang.ContextualSourcePrincipalInference.model algebra)
                  (Yulang.ConstraintProblems.split clause.pack) (Fin.last clause.locals) target
```

```lean
@Yulang.ContextualSourcePrincipalInference.infer_instances_exact : ∀ {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (expression : Yulang.Inference.Expr),
      Yulang.ContextualSourcePrincipalInference.supported expression = true →
        ∀ (target : Yulang.Inference.Comp (Yulang.ContextualSourcePrincipalInference.model algebra)),
          Yulang.ContextualSourcePrincipalInference.Result.Instance algebra target
              (Yulang.ContextualSourcePrincipalInference.infer expression) ↔
            Yulang.Inference.Typing (Yulang.ContextualSourcePrincipalInference.model algebra) [] expression target
```

```lean
@Yulang.ContextualSourcePrincipalInference.infer_inferred_exact : ∀ {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (expression : Yulang.Inference.Expr) (result : Yulang.ContextualSourcePrincipalInference.Principal),
      Yulang.ContextualSourcePrincipalInference.infer expression =
          Yulang.SourcePrincipalInference.Result.inferred result →
        ∀ (target : Yulang.Inference.Comp (Yulang.ContextualSourcePrincipalInference.model algebra)),
          Yulang.ContextualSourcePrincipalInference.Principal.Instance algebra result target ↔
            Yulang.Inference.Typing (Yulang.ContextualSourcePrincipalInference.model algebra) [] expression target
```

```lean
@Yulang.ContextualSourcePrincipalInference.infer_rejected_sound : ∀ {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (expression : Yulang.Inference.Expr),
      Yulang.ContextualSourcePrincipalInference.infer expression = Yulang.SourcePrincipalInference.Result.rejected →
        ¬∃ target,
            Yulang.Inference.Typing (Yulang.ContextualSourcePrincipalInference.model algebra) [] expression target
```

```lean
@Yulang.ContextualSourcePrincipalInference.Alternative.instance_of_parameters : ∀ {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row) (alternative : Yulang.ContextualSourcePrincipalInference.Alternative)
  (rowParameter : Fin alternative.slots → Row)
  (valueParameter : Fin alternative.scheme.size → Yulang.ContextualJointConstraintInference.Value Row),
  Yulang.ContextualSourcePrincipalInference.Alternative.Instance algebra alternative
    (alternative.scheme.instantiate algebra rowParameter valueParameter alternative.output)
```

```lean
Yulang.ContextualSourcePrincipalInference.infer_inferred_nonempty : ∀ (expression : Yulang.Inference.Expr)
  (result : Yulang.ContextualSourcePrincipalInference.Principal),
  Yulang.ContextualSourcePrincipalInference.infer expression = Yulang.SourcePrincipalInference.Result.inferred result →
    result ≠ []
```

```lean
@Yulang.ContextualSourcePrincipalInference.infer_inferred_has_typing : ∀ {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (expression : Yulang.Inference.Expr) (result : Yulang.ContextualSourcePrincipalInference.Principal),
      Yulang.ContextualSourcePrincipalInference.infer expression =
          Yulang.SourcePrincipalInference.Result.inferred result →
        ∃ target, Yulang.Inference.Typing (Yulang.ContextualSourcePrincipalInference.model algebra) [] expression target
```

```lean
@Yulang.ContextualSourcePrincipalInference.infer_rejected_iff : ∀ {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (expression : Yulang.Inference.Expr),
      (Yulang.ContextualSourcePrincipalInference.infer expression).status =
          Yulang.SourcePrincipalInference.Status.rejected ↔
        Yulang.ContextualSourcePrincipalInference.supported expression = true ∧
          ¬∃ target,
              Yulang.Inference.Typing (Yulang.ContextualSourcePrincipalInference.model algebra) [] expression target
```

```lean
@Yulang.ContextualSourcePrincipalInference.infer_principal_formula_exact : ∀ {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (expression : Yulang.Inference.Expr),
      Yulang.ContextualSourcePrincipalInference.supported expression = true →
        ∀ (target : Yulang.Inference.Comp (Yulang.ContextualSourcePrincipalInference.model algebra)),
          Yulang.ContextualSourcePrincipalInference.Result.Instance algebra target
              (Yulang.ContextualSourcePrincipalInference.infer expression) ↔
            Yulang.Inference.Formula.Holds (Yulang.ContextualSourcePrincipalInference.model algebra)
              (Yulang.Inference.extend Empty.elim target) (Yulang.Inference.principal [] expression)
```

```lean
@Yulang.ContextualSourcePrincipalInference.recordFree_instances_exact : ∀ {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (expression : Yulang.Inference.Expr),
      Yulang.SourceConstraintSupport.RecordFree expression →
        ∀ (target : Yulang.Inference.Comp (Yulang.ContextualSourcePrincipalInference.model algebra)),
          Yulang.ContextualSourcePrincipalInference.Result.Instance algebra target
              (Yulang.ContextualSourcePrincipalInference.infer expression) ↔
            Yulang.Inference.Typing (Yulang.ContextualSourcePrincipalInference.model algebra) [] expression target
```

```lean
@Yulang.ContextualSourcePrincipalInference.recordFree_rejected_iff : ∀ {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (expression : Yulang.Inference.Expr),
      Yulang.SourceConstraintSupport.RecordFree expression →
        ((Yulang.ContextualSourcePrincipalInference.infer expression).status =
            Yulang.SourcePrincipalInference.Status.rejected ↔
          ¬∃ target,
              Yulang.Inference.Typing (Yulang.ContextualSourcePrincipalInference.model algebra) [] expression target)
```

```lean
@Yulang.ContextualSourcePrincipalInference.recordFree_principal_formula_exact : ∀ {Row : Type u_1}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (expression : Yulang.Inference.Expr),
      Yulang.SourceConstraintSupport.RecordFree expression →
        ∀ (target : Yulang.Inference.Comp (Yulang.ContextualSourcePrincipalInference.model algebra)),
          Yulang.ContextualSourcePrincipalInference.Result.Instance algebra target
              (Yulang.ContextualSourcePrincipalInference.infer expression) ↔
            Yulang.Inference.Formula.Holds (Yulang.ContextualSourcePrincipalInference.model algebra)
              (Yulang.Inference.extend Empty.elim target) (Yulang.Inference.principal [] expression)
```

</details>

## CoreContextualSourceInference

同じ exactness を独立 Core Typing と実 RequiredInference.infer へ移し、旧直接 family との定義一致と、決定46の同じ結果行での旧 Typing 反映を示す。full presence 統合ではない。

<details>
<summary>15 個の公開定理の完全な型</summary>

```lean
Yulang.Core.ContextualRequiredInference.infer_embed : ∀ (expression : Yulang.Inference.Expr),
  Yulang.Core.ContextualRequiredInference.infer (Yulang.Core.Required.embed expression) =
    Yulang.ContextualSourcePrincipalInference.infer expression
```

```lean
Yulang.Core.ContextualRequiredInference.infer_unsupported_iff : ∀
  (expression : Yulang.Core.ContextualRequiredInference.Term),
  Yulang.SourcePrincipalInference.Result.status (Yulang.Core.ContextualRequiredInference.infer expression) =
      Yulang.SourcePrincipalInference.Status.unsupported ↔
    Yulang.Core.ContextualRequiredInference.supported expression = false
```

```lean
@Yulang.Core.ContextualRequiredInference.infer_instances_exact : ∀ {Row : Type}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (expression : Yulang.Core.ContextualRequiredInference.Term),
      Yulang.Core.ContextualRequiredInference.supported expression = true →
        ∀ (target : Yulang.Inference.Comp (Yulang.Core.ContextualRequiredInference.model algebra)),
          Yulang.Core.ContextualRequiredInference.Instance algebra
              (Yulang.Core.ContextualRequiredInference.infer expression) target ↔
            Yulang.Core.Typing (Yulang.Core.Required.model (Yulang.Core.ContextualRequiredInference.model algebra)) []
              expression target
```

```lean
@Yulang.Core.ContextualRequiredInference.principal_exact : ∀ {Row : Type} (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (expression : Yulang.Core.ContextualRequiredInference.Term),
      Yulang.Core.ContextualRequiredInference.supported expression = true →
        ∀ (target : Yulang.Inference.Comp (Yulang.Core.ContextualRequiredInference.model algebra)),
          Yulang.Core.Typing (Yulang.Core.Required.model (Yulang.Core.ContextualRequiredInference.model algebra)) []
              expression target ↔
            ∃ principal,
              Yulang.Core.ContextualRequiredInference.infer expression =
                  Yulang.SourcePrincipalInference.Result.inferred principal ∧
                ∃ alternative,
                  alternative ∈ principal ∧
                    ∃ rows values,
                      Yulang.Inference.Comp.le (Yulang.Core.ContextualRequiredInference.model algebra)
                        (alternative.scheme.instantiate algebra rows values alternative.output) target
```

```lean
@Yulang.Core.ContextualRequiredInference.infer_rejected_iff : ∀ {Row : Type}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (expression : Yulang.Core.ContextualRequiredInference.Term),
      Yulang.SourcePrincipalInference.Result.status (Yulang.Core.ContextualRequiredInference.infer expression) =
          Yulang.SourcePrincipalInference.Status.rejected ↔
        Yulang.Core.ContextualRequiredInference.supported expression = true ∧
          ¬∃ target,
              Yulang.Core.Typing (Yulang.Core.Required.model (Yulang.Core.ContextualRequiredInference.model algebra)) []
                expression target
```

```lean
Yulang.Core.ContextualRequiredInference.recordFree_supported : ∀
  (expression : Yulang.Core.ContextualRequiredInference.Term),
  Yulang.Core.ContextualRequiredInference.RecordFree expression →
    Yulang.Core.ContextualRequiredInference.supported expression = true
```

```lean
Yulang.Core.ContextualRequiredInference.recordFree_ne_unsupported : ∀
  (expression : Yulang.Core.ContextualRequiredInference.Term),
  Yulang.Core.ContextualRequiredInference.RecordFree expression →
    Yulang.SourcePrincipalInference.Result.status (Yulang.Core.ContextualRequiredInference.infer expression) ≠
      Yulang.SourcePrincipalInference.Status.unsupported
```

```lean
@Yulang.Core.ContextualRequiredInference.recordFree_instances_exact : ∀ {Row : Type}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (expression : Yulang.Core.ContextualRequiredInference.Term),
      Yulang.Core.ContextualRequiredInference.RecordFree expression →
        ∀ (target : Yulang.Inference.Comp (Yulang.Core.ContextualRequiredInference.model algebra)),
          Yulang.Core.ContextualRequiredInference.Instance algebra
              (Yulang.Core.ContextualRequiredInference.infer expression) target ↔
            Yulang.Core.Typing (Yulang.Core.Required.model (Yulang.Core.ContextualRequiredInference.model algebra)) []
              expression target
```

```lean
@Yulang.Core.ContextualRequiredInference.recordFree_principal : ∀ {Row : Type}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (expression : Yulang.Core.ContextualRequiredInference.Term),
      Yulang.Core.ContextualRequiredInference.RecordFree expression →
        ∀ (target : Yulang.Inference.Comp (Yulang.Core.ContextualRequiredInference.model algebra)),
          Yulang.Core.Typing (Yulang.Core.Required.model (Yulang.Core.ContextualRequiredInference.model algebra)) []
              expression target ↔
            ∃ principal,
              Yulang.Core.ContextualRequiredInference.infer expression =
                  Yulang.SourcePrincipalInference.Result.inferred principal ∧
                ∃ alternative,
                  alternative ∈ principal ∧
                    ∃ rows values,
                      Yulang.Inference.Comp.le (Yulang.Core.ContextualRequiredInference.model algebra)
                        (alternative.scheme.instantiate algebra rows values alternative.output) target
```

```lean
@Yulang.Core.ContextualRequiredInference.recordFree_rejected_iff : ∀ {Row : Type}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (expression : Yulang.Core.ContextualRequiredInference.Term),
      Yulang.Core.ContextualRequiredInference.RecordFree expression →
        (Yulang.SourcePrincipalInference.Result.status (Yulang.Core.ContextualRequiredInference.infer expression) =
            Yulang.SourcePrincipalInference.Status.rejected ↔
          ¬∃ target,
              Yulang.Core.Typing (Yulang.Core.Required.model (Yulang.Core.ContextualRequiredInference.model algebra)) []
                expression target)
```

```lean
@Yulang.Core.ContextualRequiredInference.producerInstance_iff : ∀ {Row : Type}
  (algebra : Yulang.RowFlowSchemes.Algebra Row) (result : Yulang.Core.ContextualRequiredInference.Result)
  (target : Yulang.Inference.Comp (Yulang.Core.ContextualRequiredInference.model algebra)),
  Yulang.Core.ContextualRequiredInference.Instance algebra result target ↔
    Yulang.Core.ProducerContextualInstances.Instance algebra result target
```

```lean
@Yulang.Core.ContextualRequiredInference.legacy_source_typing_exact : ∀ {Row : Type}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (expression : Yulang.Inference.Expr),
      Yulang.SourcePrincipalInference.supported expression = true →
        ∀ (target : Yulang.Inference.Comp (Yulang.Core.ContextualRequiredInference.model algebra)),
          Yulang.Core.ProducerContextualInstances.Instance algebra (Yulang.SourcePrincipalInference.infer expression)
              target ↔
            Yulang.Inference.Typing (Yulang.Core.ContextualRequiredInference.model algebra) [] expression target
```

```lean
@Yulang.Core.ContextualRequiredInference.legacy_core_typing_exact : ∀ {Row : Type}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (expression : Yulang.Inference.Expr),
      Yulang.SourcePrincipalInference.supported expression = true →
        ∀ (target : Yulang.Inference.Comp (Yulang.Core.ContextualRequiredInference.model algebra)),
          Yulang.Core.ProducerContextualInstances.Instance algebra (Yulang.SourcePrincipalInference.infer expression)
              target ↔
            Yulang.Core.Typing (Yulang.Core.Required.model (Yulang.Core.ContextualRequiredInference.model algebra)) []
              (Yulang.Core.Required.embed expression) target
```

```lean
@Yulang.Core.ContextualRequiredInference.source_typing_exact_modulo : ∀ {Row : Type}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (expression : Yulang.Inference.Expr),
      Yulang.SourcePrincipalInference.supported expression = true →
        ∀ (target : Yulang.Inference.Comp (Yulang.Core.ContextualRequiredInference.model algebra)),
          Yulang.Inference.Typing (Yulang.Core.ContextualRequiredInference.model algebra) [] expression target ↔
            ∃ oldValue,
              Yulang.Inference.Typing (Yulang.SourcePrincipalInference.model algebra) [] expression
                  (oldValue, target.snd) ∧
                Yulang.Core.ProducerContextualInstances.Equivalent algebra oldValue target.fst
```

```lean
@Yulang.Core.ContextualRequiredInference.core_typing_exact_modulo : ∀ {Row : Type}
  (algebra : Yulang.RowFlowSchemes.Algebra Row),
  (∀ {left right : Row}, algebra.le left right → algebra.le right left → left = right) →
    ∀ (expression : Yulang.Inference.Expr),
      Yulang.SourcePrincipalInference.supported expression = true →
        ∀ (target : Yulang.Inference.Comp (Yulang.Core.ContextualRequiredInference.model algebra)),
          Yulang.Core.Typing (Yulang.Core.Required.model (Yulang.Core.ContextualRequiredInference.model algebra)) []
              (Yulang.Core.Required.embed expression) target ↔
            ∃ oldValue,
              Yulang.Core.Typing (Yulang.Core.Required.model (Yulang.SourcePrincipalInference.model algebra)) []
                  (Yulang.Core.Required.embed expression) (oldValue, target.snd) ∧
                Yulang.Core.ProducerContextualInstances.Equivalent algebra oldValue target.fst
```

</details>

## ContextualBranchCost

任意 formula の実分岐数・枝長・総辺数、任意行検査での受理枝数・総 cache 長に入力上界を与える。線形構文サイズで指数個の重複枝が生じる実例も証明する。

<details>
<summary>9 個の公開定理の完全な型</summary>

```lean
@Yulang.ContextualBranchCost.branches_both_length : ∀ {n : Nat} (left right : Yulang.ContextualBranchSolver.Formula n),
  (left.both right).branches.length = left.branches.length * right.branches.length
```

```lean
@Yulang.ContextualBranchCost.branches_length_le : ∀ {n : Nat} (formula : Yulang.ContextualBranchSolver.Formula n),
  formula.branches.length ≤ 2 ^ Yulang.ContextualBranchCost.eitherNodes formula
```

```lean
@Yulang.ContextualBranchCost.branch_length_le : ∀ {n : Nat} (formula : Yulang.ContextualBranchSolver.Formula n)
  (branch : List (Yulang.NestedValueSolver.Edge n)),
  branch ∈ formula.branches → branch.length ≤ Yulang.ContextualBranchCost.edgeLeaves formula
```

```lean
@Yulang.ContextualBranchCost.branches_total_edges_le : ∀ {n : Nat} (formula : Yulang.ContextualBranchSolver.Formula n),
  (List.map List.length formula.branches).sum ≤
    2 ^ Yulang.ContextualBranchCost.eitherNodes formula * Yulang.ContextualBranchCost.edgeLeaves formula
```

```lean
@Yulang.ContextualBranchCost.solve_length_le : ∀ {n : Nat} {Row : Type u_1} (rowCheck : Row → Row → Bool)
  (graph : Yulang.NestedValueSolver.Graph n Row) (formula : Yulang.ContextualBranchSolver.Formula n),
  (Yulang.ContextualBranchSolver.solve rowCheck graph formula).length ≤
    2 ^ Yulang.ContextualBranchCost.eitherNodes formula
```

```lean
@Yulang.ContextualBranchCost.accepted_input_length_le : ∀ {n : Nat} {Row : Type u_1} (rowCheck : Row → Row → Bool)
  (graph : Yulang.NestedValueSolver.Graph n Row) (formula : Yulang.ContextualBranchSolver.Formula n)
  (branch : Yulang.ContextualBranchSolver.Branch n),
  branch ∈ Yulang.ContextualBranchSolver.solve rowCheck graph formula →
    branch.input.length ≤ Yulang.ContextualBranchCost.edgeLeaves formula
```

```lean
@Yulang.ContextualBranchCost.accepted_total_input_edges_le : ∀ {n : Nat} {Row : Type u_1} (rowCheck : Row → Row → Bool)
  (graph : Yulang.NestedValueSolver.Graph n Row) (formula : Yulang.ContextualBranchSolver.Formula n),
  (List.map (fun branch => branch.input.length) (Yulang.ContextualBranchSolver.solve rowCheck graph formula)).sum ≤
    2 ^ Yulang.ContextualBranchCost.eitherNodes formula * Yulang.ContextualBranchCost.edgeLeaves formula
```

```lean
@Yulang.ContextualBranchCost.accepted_total_cache_edges_le : ∀ {n : Nat} {Row : Type u_1} (rowCheck : Row → Row → Bool)
  (graph : Yulang.NestedValueSolver.Graph n Row) (formula : Yulang.ContextualBranchSolver.Formula n),
  (List.map (fun branch => branch.cache.length) (Yulang.ContextualBranchSolver.solve rowCheck graph formula)).sum ≤
    2 ^ Yulang.ContextualBranchCost.eitherNodes formula * (n * n)
```

```lean
@Yulang.ContextualBranchCost.duplicateTruth_counts : ∀ {n : Nat} (alternatives : Nat),
  Yulang.ContextualBranchCost.eitherNodes (Yulang.ContextualBranchCost.duplicateTruth alternatives) = alternatives ∧
    Yulang.ContextualBranchCost.edgeLeaves (Yulang.ContextualBranchCost.duplicateTruth alternatives) = 0 ∧
      (Yulang.ContextualBranchCost.duplicateTruth alternatives).branches.length = 2 ^ alternatives
```

</details>

## ModuleScheduling

任意の局所 pure compiler と topological な依存表で、実 store の依存 lookup から計算する合法 schedule が同じ全体 build を返す。同じ処理集合で順序独立、compile は各 node 高々一回。

<details>
<summary>12 個の公開定理の完全な型</summary>

```lean
@Yulang.ModuleScheduling.build_at : ∀ {Source : Type u_1} {Interface : Type u_2}
  (compile : Source → List Interface → Interface) (source : Nat → Source)
  (dependencies : Yulang.ModuleIncremental.Dependencies) (n : Nat) (node : Fin n),
  Yulang.ModuleIncremental.build compile source dependencies n node =
    Yulang.ModuleScheduling.canonical compile source dependencies ↑node
```

```lean
@Yulang.ModuleScheduling.canonical_equation : ∀ {Source : Type u_1} {Interface : Type u_2}
  (compile : Source → List Interface → Interface) (source : Nat → Source)
  (dependencies : Yulang.ModuleIncremental.Dependencies) (node : Nat),
  Yulang.ModuleScheduling.canonical compile source dependencies node =
    compile (source node)
      (List.map (fun prior => Yulang.ModuleScheduling.canonical compile source dependencies ↑prior) (dependencies node))
```

```lean
@Yulang.ModuleScheduling.collect_known : ∀ {Interface : Type u_1} (artifacts : Yulang.ModuleScheduling.Store Interface)
  (value : Nat → Interface) (nodes : List Nat),
  (∀ (node : Nat), node ∈ nodes → artifacts node = some (value node)) →
    Yulang.ModuleScheduling.collect artifacts nodes = some (List.map value nodes)
```

```lean
@Yulang.ModuleScheduling.empty_exact : ∀ {Source : Type u_1} {Interface : Type u_2}
  (compile : Source → List Interface → Interface) (source : Nat → Source)
  (dependencies : Yulang.ModuleIncremental.Dependencies),
  Yulang.ModuleScheduling.Exact compile source dependencies (fun x => none) []
```

```lean
@Yulang.ModuleScheduling.step_ready : ∀ {Source : Type u_1} {Interface : Type u_2}
  (compile : Source → List Interface → Interface) (source : Nat → Source)
  (dependencies : Yulang.ModuleIncremental.Dependencies) (done : List Nat)
  (artifacts : Yulang.ModuleScheduling.Store Interface),
  Yulang.ModuleScheduling.Exact compile source dependencies artifacts done →
    ∀ (node : Nat),
      ¬node ∈ done →
        (∀ (prior : Fin node), prior ∈ dependencies node → ↑prior ∈ done) →
          ∃ next,
            Yulang.ModuleScheduling.step compile source dependencies node artifacts = some next ∧
              Yulang.ModuleScheduling.Exact compile source dependencies next (node :: done)
```

```lean
@Yulang.ModuleScheduling.run_legal : ∀ {Source : Type u_1} {Interface : Type u_2}
  (compile : Source → List Interface → Interface) (source : Nat → Source)
  (dependencies : Yulang.ModuleIncremental.Dependencies) (done order : List Nat)
  (artifacts : Yulang.ModuleScheduling.Store Interface),
  Yulang.ModuleScheduling.Exact compile source dependencies artifacts done →
    Yulang.ModuleScheduling.Legal dependencies done order →
      ∃ result,
        Yulang.ModuleScheduling.run compile source dependencies order artifacts = some (result, order) ∧
          Yulang.ModuleScheduling.Exact compile source dependencies result (order.reverse ++ done)
```

```lean
Yulang.ModuleScheduling.legal_not_done : ∀ (dependencies : Yulang.ModuleIncremental.Dependencies)
  (done order : List Nat),
  Yulang.ModuleScheduling.Legal dependencies done order → ∀ (node : Nat), node ∈ order → ¬node ∈ done
```

```lean
Yulang.ModuleScheduling.legal_nodup : ∀ (dependencies : Yulang.ModuleIncremental.Dependencies) (done order : List Nat),
  Yulang.ModuleScheduling.Legal dependencies done order → order.Nodup
```

```lean
Yulang.ModuleScheduling.legal_length_le : ∀ (dependencies : Yulang.ModuleIncremental.Dependencies)
  (done order : List Nat),
  Yulang.ModuleScheduling.Legal dependencies done order →
    ∀ (n : Nat), (∀ (node : Nat), node ∈ order → node < n) → order.length ≤ n
```

```lean
@Yulang.ModuleScheduling.run_once_bound : ∀ {Source : Type u_1} {Interface : Type u_2}
  (compile : Source → List Interface → Interface) (source : Nat → Source)
  (dependencies : Yulang.ModuleIncremental.Dependencies) (order : List Nat),
  Yulang.ModuleScheduling.Legal dependencies [] order →
    ∀ (n : Nat),
      (∀ (node : Nat), node ∈ order → node < n) →
        ∃ artifacts calls,
          (Yulang.ModuleScheduling.run compile source dependencies order fun x => none) = some (artifacts, calls) ∧
            calls = order ∧ calls.Nodup ∧ calls.length ≤ n
```

```lean
@Yulang.ModuleScheduling.run_build_exact : ∀ {Source : Type u_1} {Interface : Type u_2}
  (compile : Source → List Interface → Interface) (source : Nat → Source)
  (dependencies : Yulang.ModuleIncremental.Dependencies) (order : List Nat),
  Yulang.ModuleScheduling.Legal dependencies [] order →
    ∀ (n : Nat),
      (∀ (node : Nat), node ∈ order ↔ node < n) →
        ∃ artifacts,
          (Yulang.ModuleScheduling.run compile source dependencies order fun x => none) = some (artifacts, order) ∧
            (∀ (node : Fin n),
                artifacts ↑node = some (Yulang.ModuleIncremental.build compile source dependencies n node)) ∧
              ∀ (node : Nat), n ≤ node → artifacts node = none
```

```lean
@Yulang.ModuleScheduling.schedule_independent : ∀ {Source : Type u_1} {Interface : Type u_2}
  (compile : Source → List Interface → Interface) (source : Nat → Source)
  (dependencies : Yulang.ModuleIncremental.Dependencies) (first last : List Nat),
  Yulang.ModuleScheduling.Legal dependencies [] first →
    Yulang.ModuleScheduling.Legal dependencies [] last →
      (∀ (node : Nat), node ∈ first ↔ node ∈ last) →
        ∃ artifacts,
          (Yulang.ModuleScheduling.run compile source dependencies first fun x => none) = some (artifacts, first) ∧
            (Yulang.ModuleScheduling.run compile source dependencies last fun x => none) = some (artifacts, last)
```

</details>

## MethodResolutionScheduling

任意の局所 pure prepare が実行中に作る Site 群へ実 resolve を適用する。二合法 schedule で計算する snapshot と三状態回答が同じになり、任意位置の unique 結果 iff 独立 Selects。

<details>
<summary>6 個の公開定理の完全な型</summary>

```lean
@Yulang.MethodResolutionScheduling.canonical_compiled : ∀ {Row : Type} {Export : Type u_1} {Source : Type u_2}
  (prepare :
    Source →
      List (Yulang.MethodResolutionScheduling.Artifact Row Export) →
        Yulang.MethodResolutionScheduling.Snapshot Row Export)
  (source : Nat → Source) (dependencies : Yulang.ModuleIncremental.Dependencies) (node : Nat),
  Yulang.ModuleScheduling.canonical (Yulang.MethodResolutionScheduling.compile prepare) source dependencies node =
    { snapshot := Yulang.MethodResolutionScheduling.canonicalSnapshot prepare source dependencies node,
      answers :=
        List.map Yulang.MethodResolution.resolve
          (Yulang.MethodResolutionScheduling.canonicalSnapshot prepare source dependencies node).sites }
```

```lean
@Yulang.MethodResolutionScheduling.run_artifacts_exact : ∀ {Row : Type} {Export : Type u_1} {Source : Type u_2}
  (prepare :
    Source →
      List (Yulang.MethodResolutionScheduling.Artifact Row Export) →
        Yulang.MethodResolutionScheduling.Snapshot Row Export)
  (source : Nat → Source) (dependencies : Yulang.ModuleIncremental.Dependencies) (order : List Nat),
  Yulang.ModuleScheduling.Legal dependencies [] order →
    ∃ artifacts,
      (Yulang.ModuleScheduling.run (Yulang.MethodResolutionScheduling.compile prepare) source dependencies order
            fun x => none) =
          some (artifacts, order) ∧
        ∀ (node : Nat),
          node ∈ order →
            artifacts node =
              some
                { snapshot := Yulang.MethodResolutionScheduling.canonicalSnapshot prepare source dependencies node,
                  answers :=
                    List.map Yulang.MethodResolution.resolve
                      (Yulang.MethodResolutionScheduling.canonicalSnapshot prepare source dependencies node).sites }
```

```lean
@Yulang.MethodResolutionScheduling.run_snapshots_and_answers : ∀ {Row : Type} {Export : Type u_1} {Source : Type u_2}
  (prepare :
    Source →
      List (Yulang.MethodResolutionScheduling.Artifact Row Export) →
        Yulang.MethodResolutionScheduling.Snapshot Row Export)
  (source : Nat → Source) (dependencies : Yulang.ModuleIncremental.Dependencies) (order : List Nat),
  Yulang.ModuleScheduling.Legal dependencies [] order →
    ∃ artifacts,
      (Yulang.ModuleScheduling.run (Yulang.MethodResolutionScheduling.compile prepare) source dependencies order
            fun x => none) =
          some (artifacts, order) ∧
        ∀ (node : Nat),
          node ∈ order →
            Option.map Yulang.MethodResolutionScheduling.Artifact.snapshot (artifacts node) =
                some (Yulang.MethodResolutionScheduling.canonicalSnapshot prepare source dependencies node) ∧
              ∀ (position : Nat),
                Yulang.MethodResolutionScheduling.answerAt artifacts node position =
                  Option.map Yulang.MethodResolution.resolve
                    (Yulang.MethodResolutionScheduling.canonicalSnapshot prepare source dependencies
                          node).sites[position]?
```

```lean
@Yulang.MethodResolutionScheduling.run_selection_exact : ∀ {Row : Type} {Export : Type u_1} {Source : Type u_2}
  (prepare :
    Source →
      List (Yulang.MethodResolutionScheduling.Artifact Row Export) →
        Yulang.MethodResolutionScheduling.Snapshot Row Export)
  (source : Nat → Source) (dependencies : Yulang.ModuleIncremental.Dependencies) (order : List Nat),
  Yulang.ModuleScheduling.Legal dependencies [] order →
    ∃ artifacts,
      (Yulang.ModuleScheduling.run (Yulang.MethodResolutionScheduling.compile prepare) source dependencies order
            fun x => none) =
          some (artifacts, order) ∧
        ∀ (node : Nat),
          node ∈ order →
            ∀ (position : Nat) (reference : Yulang.MethodResolution.Reference),
              Yulang.MethodResolutionScheduling.answerAt artifacts node position =
                  some (Yulang.Methods.Selection.unique reference) ↔
                Yulang.MethodResolutionScheduling.SelectsAt
                  (Yulang.MethodResolutionScheduling.canonicalSnapshot prepare source dependencies node) position
                  reference
```

```lean
@Yulang.MethodResolutionScheduling.schedule_independent : ∀ {Row : Type} {Export : Type u_1} {Source : Type u_2}
  (prepare :
    Source →
      List (Yulang.MethodResolutionScheduling.Artifact Row Export) →
        Yulang.MethodResolutionScheduling.Snapshot Row Export)
  (source : Nat → Source) (dependencies : Yulang.ModuleIncremental.Dependencies) (first last : List Nat),
  Yulang.ModuleScheduling.Legal dependencies [] first →
    Yulang.ModuleScheduling.Legal dependencies [] last →
      (∀ (node : Nat), node ∈ first ↔ node ∈ last) →
        ∃ artifacts,
          (Yulang.ModuleScheduling.run (Yulang.MethodResolutionScheduling.compile prepare) source dependencies first
                fun x => none) =
              some (artifacts, first) ∧
            (Yulang.ModuleScheduling.run (Yulang.MethodResolutionScheduling.compile prepare) source dependencies last
                  fun x => none) =
                some (artifacts, last) ∧
              ∀ (node : Nat),
                node ∈ first →
                  Option.map Yulang.MethodResolutionScheduling.Artifact.snapshot (artifacts node) =
                      some (Yulang.MethodResolutionScheduling.canonicalSnapshot prepare source dependencies node) ∧
                    ∀ (position : Nat),
                      Yulang.MethodResolutionScheduling.answerAt artifacts node position =
                        Option.map Yulang.MethodResolution.resolve
                          (Yulang.MethodResolutionScheduling.canonicalSnapshot prepare source dependencies
                                node).sites[position]?
```

```lean
@Yulang.MethodResolutionScheduling.scheduled_once : ∀ {Row : Type} {Export : Type u_1} {Source : Type u_2}
  (prepare :
    Source →
      List (Yulang.MethodResolutionScheduling.Artifact Row Export) →
        Yulang.MethodResolutionScheduling.Snapshot Row Export)
  (source : Nat → Source) (dependencies : Yulang.ModuleIncremental.Dependencies) (order : List Nat),
  Yulang.ModuleScheduling.Legal dependencies [] order →
    ∀ (count : Nat),
      (∀ (node : Nat), node ∈ order → node < count) →
        ∃ artifacts calls,
          (Yulang.ModuleScheduling.run (Yulang.MethodResolutionScheduling.compile prepare) source dependencies order
                fun x => none) =
              some (artifacts, calls) ∧
            calls = order ∧ calls.Nodup ∧ calls.length ≤ count
```

</details>
