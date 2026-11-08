# Cycle 2: T3 variance / nominal bridges inventory

状態: 読み取り調査。新しい言語意味論や T3 の完了を宣言しない。
対象 base: integration/m1-final `5fd6ffa2c`。調査日 2026-11-08。

## 結論

宣言方程式の `Program` から variance 表、metadata head inspector、普通 solver の
全 solution family までの道は既にある。これを「手渡しの variance 表しかない」と
扱うのは誤り。一方、この道の `SourceSubtype` は collapsed head comparison であり、
既存 `CommonNominalFullCarrier.Subtype` の mixed-variance 拡張ではない。
cast の実 evaluator と data-independent cost bound もあるが、宣言の解析結果から
その `Plan` と `check plan = true` を導く typed-plan producer は残る。

## 既存結果と境界

| 部品 | 実在する入口 | 証明済み範囲と残る境界 |
|---|---|---|
| 使用・再帰解析 | `CommonDeclarationVarianceOccurrences.occurrences_exact`, `CommonDeclarationVarianceGraph.analyze_exact` | 有限 Universe 上の Horn 解析 iff 独立使用/再帰判断。Universe の全要素性はその structure の契約。 |
| 表 | `CommonDeclarationVarianceTable.derive_variance_exact` | Program の全 parameter の表と独立 TableJudgment の iff。`invariant_propagates` は呼出先の不変性伝播。 |
| Body lowering | `CommonDeclarationVarianceLowering.lower_exact` | CommonNominalFieldTemplates.Body から解析 Expr への成功 iff Lowered。全 resolved source 宣言群の assembly とは別。 |
| 元 header 保持 | `CommonDeclarationVarianceRegistry.registry_exact` | header の kind/formal identity から計算した registry iff RegistryJudgment。kind/arity 保存もあり。 |
| 宣言由来 head 比較 | `CommonDeclarationVarianceInspection.inspect_exact` | 元引数 term を評価した SourceSubtype iff 実 metadata inspector 充足。full recursive carrier ではない。 |
| 無制約 family | `CommonDeclarationVarianceSourceFamily.solve_all_instances_exact` | original ordinary atoms の child/width/rows grammar を前提に、全元 assignment を返却 scheme の parameter で回収。 |
| 元 generator clause | `CommonDeclarationVarianceSourceFamily.generated_models_exact` | principal から生成済み clause に接続。ただし comparisons と invariant occurrences 自体は入力。source 全体からの生成ではない。 |
| cast cycle check | `CommonDeclaredCastCostGraph.check_exact` | 与えられた finite Plan の immediate graph acyclic iff check 成功。 |
| cast 実行・費用 | `CommonDeclaredCastEvaluation.execute_checked_bound` | executeChecked の成功からチェック成功と Run と budget 上界を導く。値型と source typing との adequacy は別。 |
| function wrapper | `CommonDeclaredCastCost.wrapper_creation`, `invocation_bound` | 作成費用1と一呼出の有限plan上界を分離。ユーザーcast本体の費用・停止性を含めない。 |
| 旧 full nominal | `CommonNominalFullCarrier.nominal_regular_invariant_exact` | 全引数不変の point carrier。mixed-variance の一般結論へ流用不可。 |
| 旧 source typing | `CommonNominalFullCoreSource.generate_nominal_core_exact` | 同じ旧 full carrier 上の生成と typing iff。carrier を置換した証明ではない。 |

設計根拠は `notes/design/2026-11-08-b5-interval-invariance.md` と
`notes/questions/2026-11-08-b5-declaration-recursive-variance.md`。
後者は候補1承認済み。未承認の候補を選び直さない。

## 名前つきの不足する橋（以下は提案名で、存在する定理ではない）

1. **`resolved_declarations_to_variance_program_exact`**:
   任意の解決済み宣言群から、同じ元 formal/node/nominal identity を持つ Program・Universe・headers
   を計算し、各 body の Lowered と宣言 well-formedness を一つの iff にする。
   個々の `lower_exact` と registry の正しさを whole source へ接続する。
2. **`declared_nominal_carrier_subtype_exact`**:
   同じ導出済み registry を参照する再帰的 carrier の nominal rule を、SourceSubtype の方向と
   対応づける。共変boxのjoin/grouping、反変位置、不変位置の区間、nominal opaque identity を保持する。
   既存 all-invariant carrier を一般 carrier と読み替えない。
3. **`declaration_cast_plan_checked`** と **`typed_cast_execution_cost`**:
   許可された元source/target変換から finite typed Plan を実生成し、その check 成功を
   宣言の即時再帰解析から導く。さらに同じ carrier の cast judgment と evaluator の値型保存を結び、
   execute_checked_bound を source-level 費用定理にする。単に accepted を引数として足さない。
4. **`source_nominal_sites_metadata_exact`**:
   元 construction/cast expression から comparisons と invariant occurrences を生成し、
   同じ source slot・順序・kind と deferred construction site を保持する。既存 generated_models_exact の
   外部 comparisons/occurrences をここで埋める。
5. **`invariant_context_interval_normalization_exact`**:
   不変位置の内部の共変/反変を不変として処理する source inspection と同頭端点単純化を、
   上の carrier と同じ judgment で結ぶ。局所表や normalizer の単独結果を X15/X17 の外側適合としない。

着手順は 1 の有限 resolved Body 断片、3 の同じ断片の plan 生成、2/4 への接続が候補。
これは作業分解であり、source semantics の選択ではない。

## exact signatures（既存ファイルから抜粋、各名前空間内）

以下は現在の宣言の型そのもの。暗黙変数・typeclass は元ファイルの namespace/variable 文脈を参照。
外部前提を省いた要約を完成した全体定理として読まない。

### `CommonDeclarationVarianceTable.derive_variance_exact`

```lean
theorem derive_variance_exact (program : Program Index Parameter) (pool : Universe Index Parameter)
    (table : List (Parameter × Variance)) :
    deriveVariance program pool = table ↔ TableJudgment program pool.parameters table
```

### `CommonDeclarationVarianceTable.invariant_propagates`

```lean
theorem invariant_propagates (program : Program Index Parameter) (first next : Parameter)
    (called : Transition program false (program.body (program.root first)) first (program.root next, next))
    (mode : Mode program next .invariant) : Mode program first .invariant
```

### `CommonDeclarationVarianceLowering.lower_exact`

```lean
theorem lower_exact (scope : Scope Index Parameter nodes types rows) (resolve : Resolver Parameter)
    (body : Body nodes types rows) (result : Expr Index Parameter) :
    lower scope resolve body = some result ↔ Lowered scope resolve body result
```

### `CommonDeclarationVarianceLowering.lower_arguments_preserves_every_kind`

```lean
theorem lower_arguments_preserves_every_kind (scope : Scope Index Parameter nodes types rows)
    (formals : Header Parameter) (actuals : List (Argument nodes types rows)) (result)
    (compiled : lowerArguments scope formals actuals = some result) :
    formals.map Prod.fst = actuals.map argumentKind
```

### `CommonDeclarationVarianceRegistry.registry_exact`

```lean
theorem registry_exact (program : Program Index Formal) (pool : Universe Index Formal)
    (headers : List (Header Formal)) (result : Registry) :
    registry program pool headers = result ↔ RegistryJudgment program headers result
```

### `CommonDeclarationVarianceRegistry.declaration_preserves_kinds`

```lean
theorem declaration_preserves_kinds (program : Program Index Formal) (pool : Universe Index Formal)
    (header : Header Formal) :
    (declaration program pool header).map CommonDeclaredNominalInspection.Parameter.kind =
      header.map Prod.fst
```

### `CommonDeclarationVarianceRegistry.registry_preserves_arity`

```lean
theorem registry_preserves_arity (program : Program Index Formal) (pool : Universe Index Formal)
    (headers : List (Header Formal)) :
    (registry program pool headers).map List.length = headers.map List.length
```

### `CommonDeclarationVarianceInspection.subtype_exact`

```lean
theorem subtype_exact (program : Program Index Formal) (pool : Universe Index Formal)
    (headers : List (Header Formal)) (first last : Head) :
    CommonDeclaredNominalInspection.DeclaredSubtype (registry program pool headers) first last ↔
      SourceSubtype program headers first last
```

### `CommonDeclarationVarianceInspection.inspect_exact`

```lean
theorem inspect_exact (program : Program Index Formal) (pool : Universe Index Formal)
    (headers : List (Header Formal)) (first last : HeadTerm α)
    (assignment : α → Comp Common.model) :
    Satisfied assignment (CommonDeclaredNominalInspection.inspect
      (registry program pool headers) first last) ↔
      SourceSubtype program headers (first.eval assignment) (last.eval assignment)
```

### `CommonDeclarationVarianceSourceFamily.solve_all_instances_exact`

```lean
theorem solve_all_instances_exact (program : Program Index Formal) (pool : Universe Index Formal)
    (headers : List (Header Formal)) (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots))) (occurrences : List (Occurrence (Fin slots)))
    (child : PresenceGeneratedChildGrammar.GoodAtoms original)
    (width : PresenceGeneratedWidth.WidthAtoms original)
    (rows : PresenceSourceConstraintSupport.GoodAtoms original)
    (assignment : Fin slots → Comp Common.model) :
    Models program headers original comparisons occurrences assignment ↔
      ∃ scheme ∈ solve program pool headers original comparisons occurrences,
        ∃ rowParameters : Fin slots → Common.Row, ∃ parameters : scheme.Parameters,
          AssignmentEquivalent (scheme.instantiate rowParameters parameters) assignment
```

### `CommonDeclarationVarianceSourceFamily.generated_models_exact`

```lean
theorem generated_models_exact (expression : Inference.Expr) (clause : Clause (Option Empty))
    (generated : clause ∈ normalise (Core.PresenceGeneration.principal
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (program : Program Index Formal) (pool : Universe Index Formal) (headers : List (Header Formal))
    (comparisons : List (Comparison (Fin (clause.locals + 1))))
    (occurrences : List (Occurrence (Fin (clause.locals + 1))))
    (assignment : Fin (clause.locals + 1) → Comp Common.model) :
    Models program headers clause.pack comparisons occurrences assignment ↔
      ∃ scheme ∈ solve program pool headers clause.pack comparisons occurrences,
        ∃ rowParameters : Fin (clause.locals + 1) → Common.Row, ∃ parameters : scheme.Parameters,
          AssignmentEquivalent (scheme.instantiate rowParameters parameters) assignment
```

### `CommonDeclaredCastCostGraph.check_exact`

```lean
theorem check_exact (plan : Plan n) : check plan = true ↔ Acyclic plan
```

### `CommonDeclaredCastCost.run_bound`

```lean
theorem run_bound (plan : Plan n) (accepted : check plan = true)
    (execution : Run plan node cost) : cost ≤ budget plan accepted node
```

### `CommonDeclaredCastCost.wrapper_creation`

```lean
theorem wrapper_creation (plan : Plan n) (accepted : check plan = true)
    (node argument result : Fin n) (shape : plan node = .function argument result) :
    budget plan accepted node = 1 ∧ Run plan node 1
```

### `CommonDeclaredCastCost.invocation_bound`

```lean
theorem invocation_bound (plan : Plan n) (accepted : check plan = true)
    (wrapper argument result : Fin n) (shape : plan wrapper = .function argument result)
    (execution : Invocation plan wrapper cost) : cost ≤ callBudget plan accepted argument result
```

### `CommonDeclaredCastEvaluation.execute_checked_bound`

```lean
theorem execute_checked_bound (plan : Plan n) (leaf : Leaf n)
    (node : Fin n) (input output : Value n) (cost : Nat)
    (returned : executeChecked plan leaf node input = some (output, cost)) :
    ∃ accepted : check plan = true, Run plan node cost ∧ cost ≤ budget plan accepted node
```

### `CommonNominalFullCarrier.nominal_regular_invariant_exact`

```lean
theorem nominal_regular_invariant_exact (name other : Nat) (first last : List Argument) :
    Subtype (nominal name first) (nominal other last) ↔
      name = other ∧ first.length = last.length ∧ ArgumentsEquivalent first last
```

### `CommonNominalFullCoreSource.generate_nominal_core_exact`

```lean
theorem generate_nominal_core_exact (symbolic : PresenceGeneration.SchemeEnv α)
    (environment : List (Binding CommonNominalFullCarrier.model))
    (source : List (PresenceGeneration.Binding CommonNominalFullCarrier.model))
    (assignment : α → Comp CommonNominalFullCarrier.model) (expression : Term)
    (output : PresenceGeneration.CompTerm α)
    (actualRelated : EnvRel CommonNominalFullCarrier.model environment source)
    (symbolicRelated : PresenceGeneration.EnvRel CommonNominalFullCarrier.model assignment symbolic source) :
    (generateNominalCore symbolic expression output).Holds CommonNominalFullCarrier.model assignment ↔
      Typing CommonNominalFullCarrier.model environment expression (output.eval CommonNominalFullCarrier.model assignment)
```

## 調査方法と未確認

元ファイル・設計ノート・計画表の読み取り。コード変更、定理追加、削除はない。
関連する全 nominal パッケージを列挙し尽くしたとは主張しない。
この文書単独のためのビルドは未実施。既存結果の型とファイル内の boundary コメントを照合した。
