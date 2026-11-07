# M1: symbolic saturation、全自由 scheme、公開入口の実装結果

2026-11-07。対象ブランチは `integration/m1-common`。
[復旧記録](2026-11-07-m1-common-recovery-results.md) §7.1–7.5 の契約を基準とする。
内部表現と採用しなかった案は [共通モデルの設計](../design/2026-11-07-m1-common-model.md) §13–26 に記す。
本書は完了した証明と、その時点で残る数学的義務の記録である。
並行して追加された solver・固定旧境界・constructor family の定理群については、
[有限飽和・公開入口の実装結果](2026-11-07-m1-common-saturation-results.md) も参照する。

## 1. 到達点と範囲

| 元の契約 | 到達点 | 残り |
| --- | --- | --- |
| 7.1 symbolic rigid exactness | 実生成 source/Core clause、独立した全 rows/values、元 constructor 方程式に対する iff が閉じた | この契約の残りなし |
| 7.2 有限閉性・全 parameter soundness | 実 worklist の停止、全 rigid 比較の分解、任意の行・型・再帰 parameter に対する元 Models を閉じた | この契約の残りなし |
| 7.3 全解回収 | 任意実生成 clause の任意独立 Models iff 返却 scheme の自由具体化。全元 node の要求同値と行の等号を回収 | この契約の残りなし |
| 7.4 公開入口 | 実 `Core.infer` の principal iff、rejected iff 型付け不能、unsupported 不出現が閉じた。実旧 instance の保存も閉じた | 任意旧 supported source の新 instance から、同じ結果行の要求同値な実旧 instance を回収する一般反映 |
| 7.5 完全 interface 標準形 | 異 arity の scalar family、弱い変数の固定、実 scalar Interface への接続、Form の正負位置による instance 保存まで追加 | 全有限 public interface の完全 encoding と実 inference/export/display の一体的な接続 |

公開型判断は `Core.Typing (Core.PresenceGeneration.CoreRules.model Common.model)`。
record 構築・whole recordDefault・lambda/application・value-let/computed-let を含む presence モデルを扱う。
effect/qualified/case 等の混合言語全体を、このモデルの型付けと同一視しない。
従来からの required/effect/qualified 等の入口とその定理は変更していない。

作業中の `origin/yulang3` の更新を取り込み、spread だけの `{..rest}` が record である確定仕様も保持した。
同じ作業ブランチへ並行して届いた別の solver/source 証明も統合した。詳細は §6.4。
push 先は `integration/m1-common` のみであり、`integration/types` と `yulang3` には push していない。

## 2. 記法と自由 parameter

`S ≤ T` は `Common.Subtype S T`、`S ≈ T` は `Common.Equivalent S T`。
両者は既存の独立な要求解釈に基づき、全展開深さ・負文脈 rank・具体型環境・要求を量化する。
有限サンプルや推論 fuel の範囲に量化を縮めていない。

実生成 clause `C` に対して `m = C.locals + 1`、`a = C.pack`、`G = compile a` と書く。
`rows : Fin m → Common.Row` と `values : Fin G.size → Common.Ty` は独立に量化する。
`G.Models rows values` は元の constructor 方程式、元の全型比較辺、元の全行制約の conjunction である。
後から solver の成立や trace の法則をこの意味に加えていない。

`CommonBoundRefSolver.Scheme` は有限 clamped family と元 node の readout だけを持つ。
source scheme はさらに出力の型 ID と行 ID を持つ。parameter の領域は次の普通の積である。

```text
行 parameter       : Fin m → Common.Row
型 parameter       : Fin m → Common.Ty
再帰 node parameter: Fin extendedPool.size → Common.Ty
```

`Common.Ty` の自由代入には mask・exact/default・regular graph・関数を含む。
`Models`、`ResidualHolds`、support、solver 成功、Closed、fuel、型付け証拠を parameter の条件にしない。
有限 pool が持つ証明 field は、変数の収録・部分構文の閉包・重複なしという構文の条件だけである。
parameter 領域の inhabitance も証明しており、空の領域による空虚な全称健全性ではない。

## 3. 7.1: 代入前に固定する symbolic rigid 分解

### 3.1 `CommonGeneratedRigidInspection.saturate_common_rigid_exact`

任意の source 式 `e`、任意の

```text
C ∈ normalise (PresenceGeneration.principal [] e)
```

および任意の独立 `rows/values` に対して、元 pool の constructor 方程式 `Realizes pool rows values` を仮定する。
`E` を実 `compile C.pack` の変数上下限伝播後の rigid 比較列とすると、

```text
EdgesHold E values
  ↔ ∃ branch ∈ saturate pool E,
      branch の child / row / profile / presence 制約が rows/values で成立する
```

が成り立つ。`saturate_common_core_rigid_exact` は同じ量化と前提を任意の `Core.Required.Term` と
`principalCore [] e` の実生成 clause に対して述べる。

`saturate` の入力は有限の元構文・共有 ID と比較列だけである。具体化した Common 型を inspector に渡して
分岐を作る計算ではない。生成・scheme 置換・binder packing から endpoint grammar を内部供給する。
未知 slot の field/optional profile、presence、外側 mask は同じ元 ID を参照する。

### 3.2 支持・共有・深さを保持する補助定理

- `CommonSymbolicTailView.symbolic_tail_exact`：任意の隠す label 集合、二つの symbolic tail、任意 slot 割当てで、
  同深さ tail 比較と、同じ ID を読む有限 view の通常比較が同値。元の式にない label の観測も保存する。
- `CommonGeneratedRigidDescent.residual_omits_original` / `residual_child_decreases` / `residual_profile_decreases`：
  任意の実 rigid 分解について、元比較を同じ比較に包み直さず、返却 child/profile の構文 weight が減少する。
- `CommonGeneratedProfileSupport.saturate_support`：任意の元 pool と比較列に対し、first-pass の全返却型参照は
  代入前に作る有限支持に入る。`universe_length_le` の上界は `8N(N+1)`。
- `CommonSymbolicProfileCoherence.compileNode_reconstruction`：任意の独立 profile table が有限支持上で一つの
  元 values と一致するなら、七項目の意味を回収する。`independent_projection_not_sound` は、その一致を落とすと
  scalar が required を満たす偽解を作れることを示す。

この profile の条件を自由 parameter の制限として残さず、次節では同じ元 node を読む型境界へ変換して解く。

## 4. 7.2: 有限 universe、停止、全 parameter soundness

### 4.1 Optional/default を有限の通常比較へ変換する

`CommonOptionalBound.optional_payload_branches_exact` は、任意 label/source/payload に対する optional 義務を、
top/width の枝と `exactEmpty | required label payload` への比較の枝へ完全分解する。
`CommonDefaultBounds.default_required_branches_exact` は、任意 label/source/fallback/payload に対し、
whole default の required 比較を通常の型比較だけからなる固定三枝へ完全分解する。
source の shape/presence や solver 成功を前提にしない。

深さ 0 の raw optional bound を width と同一視しない。有限 soundness は guarded child と同深さ tail/presence を
分ける。`CommonFiniteBoundInspection.required_at_sound` / `optional_at_sound` と
`CommonFiniteOptionalInspection.default_branches_at_sound` の `BranchAtSource` は、全 child の guarded 比較に加え、
non-rigid source では全 child の同深さ比較を要求する。最終 proof はその追加前提も帰納法から供給する。

### 4.2 `CommonBoundRefAllParameters.saturation_closed`

任意の有限 pool、任意の初期 bound-reference 比較列 `E`、任意の `state ∈ CommonBoundRefWorklist.run pool E`
について、他の前提なしで次の三つを同時に結論する。

```text
Closed actualRigid actualInspect state
pending actualInventory actualRigid state = none
state.trace.length ≤ (5 * pool.size + 3)²
```

元の `N` node と top/width/exactEmpty、固定 query ごとの required/rawOpt が有限 inventory を構成する。
追加 node は高々 `5N+3`。lower/upper の伝播、projection、default の分解、再 inspection はこの inventory を出ない。
各 step は未処理の pair を一つ消費する。公開 `run` に fuel の引数はない。
この上限は各 branch の trace 長であり、branch 総数や実行時間の多項式上界ではない。

`CommonBoundRefWorklist.generated_run_models_exact` / `generated_core_run_models_exact` は、任意の実生成 clause、
任意独立 rows/values、元 constructor realizer の下で、元の全比較辺の成立と、いずれかの返却 state の
比較・行補助制約の成立の iff を示す。生成文法・幅条件は生成から内部供給する。

### 4.3 全行・型 parameter で元 Models が成立する

`CommonBoundRefAllParameters.generated_all_parameters_models` / `generated_core_all_parameters_models` は、
任意の source/Core 式、任意の実生成 clause、任意の実返却 state、任意の行・型・再帰 node parameter に対し、
同時 row/clamped family の出力を元 ID へ制限すると元 `compile C.pack` の `Models` を満たす、と述べる。

証明では次を内部供給する。

1. 実 worklist の trace から、各最終 rigid 比較に選択した finite branch を回収する。
2. 実 finite inspector と観測深さ/source weight の二重帰納から、全最終型比較を導く。
3. 元行制約と追加行制約を同じ row scheme で解き、任意 row parameter から全 aux を成立させる。
4. optional pool を元 ID へ制限し、元 constructor 方程式と全元比較辺を保持する。

`CommonBoundRefClosedSoundness.returned_solve_soundness` 単体の `AuxHolds` は、この最終 theorem には残らない。
幅や残比較の成立を仮定して同じ比較を結論する循環でもない。

上限 clamp は必要である。`CommonSameDepthUpperObstruction.solver_recovers_counterexample` は、異なる label a/b と
任意 payload P/Q に対し、従来の独立方程式解が元方程式を満たしつつ上限 required b Q を破る具体例を示す。
その独立 graph が実 source の完全な clause だとは主張しない。
新 `CommonPresenceClampedBounds.solve_retract` は元方程式と全辺を満たす任意モデルを回収するため、
clamp によって既存の元解を失ってはいない。

## 5. 7.3: 全自由 scheme の健全性と全解回収

### 5.1 `CommonBoundRefSolver.all_parameter_sound`

任意の `m`、任意の atom 列 `a : List (Atom (Fin m))`、任意の

```text
S ∈ solveAll (compile a)
```

任意の `rowParameters : Fin m → Common.Row` と任意の `valueParameters : S.Parameters` に対して、

```text
(compile a).Models
  (S.instantiateRows rowParameters)
  (S.instantiateValues rowParameters valueParameters)
```

が成り立つ。この健全性には実生成文法の前提もない。

### 5.2 `generated_models_exact` / `generated_core_models_exact`

任意の source/Core 式、任意のその実生成 clause `C`、任意の独立 `rows` と任意の元 compiled node 割当て
`values` に対して、次が成り立つ。

```text
(compile C.pack).Models rows values
  ↔ ∃ S ∈ solveAll (compile C.pack),
      ∃ rowParameters, ∃ valueParameters : S.Parameters,
        S.instantiateRows rowParameters = rows
        ∧ ∀ i,
          S.instantiateValues rowParameters valueParameters i ≈ values i
```

前提は clause が実生成・正規化結果に属することだけである。全元 node を量化し、出力 node だけに縮めない。
値の回収は両方向の要求同値であり、負の arrow child も共有する。行は相互包含だけでなく literal equality。

内部の `compiled_models_exact` は任意 atom 列に対する行文法・recursive child grammar・WidthAtoms の
三つの構文条件を明示する。上の生成版はその全条件を内部で証明する。
`ofState_retract` は元モデルを optional pool に保存的に拡張し、元 rows と全元 values から parameter を構成する。
`models_congr` は任意 Compiled・任意 rows・任意の二つの値割当てについて、全 node が要求同値なら
元 Models も iff になることを示す。

### 5.3 Compiled metadata の保証範囲

`Compiled.origin : Option (Problem inputs)` は元の有限構文を保存する欄で、実 compile が構成する。
`Compiled.models_origin_irrelevant` は任意 graph/metadata/rows/values で、この欄を変えても Models が変わらないことを示す。

`solveAll` は origin の存在と node 数を調べ、origin と手製 graph の definitions/edges/rows/input 全体の一致までは
検査しない。したがって任意の手製 Compiled と無関係な origin の組に対する健全性は主張しない。
上記 theorem と実公開入口は必ず `solveAll (compile a)` を使うので、要求された保証範囲にこの不一致は入らない。

## 6. 7.4: 公開入口、旧 instance の保存と反映の部分結果

### 6.1 `Core.infer_principal`

任意の `e : Core.Required.Term` と任意の `c : PresenceGeneration.Comp Common.model` について、前提なしで、

```text
Core.Typing (PresenceGeneration.CoreRules.model Common.model) [] e c
  ↔ ∃ S ∈ Core.infer e, ∃ parameters : S.Parameters,
      PresenceGeneration.Comp.le Common.model (S.instantiate parameters) c
```

が成り立つ。`CommonSolvedSource.source_principal` は任意の `Inference.Expr` に対する同じ source 版、
`core_principal` は公開 Result に分類する前の実 finite List 版である。
`Core.infer_instances_exact` はこの iff を実 `Result.Instance` の向きに述べる。

`Core.infer_instantiates` は、任意 e、任意 S ∈ Core.infer e、任意 parameters に対し、
`S.instantiate parameters` 自体に独立な Core Typing が付くと述べる。

計算は実 generate → normalise → pack → compile → finite worklist/row solver → finite scheme List の経路を通る。
`Core.infer` は Formula.Holds の別名ではない。

### 6.2 `Core.infer_rejected_iff` / `infer_ne_unsupported`

任意の `e : Core.Required.Term` について、前提なしで、

```text
Core.infer e = .rejected
  ↔ ¬ ∃ c,
      Core.Typing (PresenceGeneration.CoreRules.model Common.model) [] e c
```

および `Core.infer e ≠ .unsupported` が成り立つ。
support checker・成功・closed cache・fuel・残比較を公開前提にしない。
presence モデルに規則のない構文は、この入口では型付け不能として rejected に分類する。
他の Core モデルでの型付け不能を結論するものではない。

### 6.3 決定46の保存と旧型を割り当てた場合の exactness

`CommonSolvedLegacyPreservation.legacy_core_parameters` は、任意旧 source e、
`SourcePrincipalInference.supported e = true`、任意旧結果 c と
実 `(SourcePrincipalInference.infer e).Instance Common.rowAlgebra c` に対して、

```text
∃ S ∈ Core.infer (Core.Required.embed e), ∃ p : S.Parameters,
  (S.instantiate p).1 ≈ Common.embedOld c.1
  ∧ (S.instantiate p).2 = c.2
```

を返す。`legacy_source_parameters` は実 source List 版、`legacy_core_entry_parameters` は旧 Core entry 自体の
Instance を前提にする版。`legacy_instances_preserved` / `legacy_core_entry_preserved` は新 Result.Instance に接続する。
旧 instance を単なる旧 Typing 前提に置き換えていない。

反映に関しては次まで閉じた。

- `CommonLegacyEmptyReflection.exact_empty_upper_contextual_iff`：任意旧 regular target T について、
  exactEmpty ≤ embedOld T iff 旧 contextual emptyRecord ≤ T。regular・負の arrow・行を除外しない。
- `empty_record_typing_exact` / `empty_record_legacy_instances_reflected`：任意旧結果 c に対する empty-record source の
  Common Typing と旧 contextual Typing が iff。実旧 instance を、同じ結果行と要求同値な埋込み値で回収する。
- `CommonLegacyGenerationTranslation.generate_translation`：任意 requiredFieldsOnly source、任意 captured scheme env、
  任意 symbolic output に対し、新 generator の構文変換が実旧 generator と literal equality。
  `normalise_translation` は任意 formula で実 clause List の map equality、`clause_locals` / `clause_pack` は ID 保持。
- `legacy_generated_clause_exact`：任意旧 supported source と任意実 presence clause から、変換先の実旧 clause membership、
  部分変換の成功、全共有旧 assignment に対する全 atom の意味の iff を同時に得る。grammar/変換成功の追加前提なし。
- `CommonLegacyEmbeddedWitnesses.embedded_witnesses_iff_typing`：任意 requiredFieldsOnly source と任意旧結果 c について、
  実 presence clause を一つ選び、全 slot を一つの旧 assignment の埋込みで満たして出力を c に固定できること iff
  旧 contextual Typing [] e c。旧 solver support は不要。
- `contextual_typing_preserved`：同じ requiredFieldsOnly 前提で、旧 contextual Typing を独立な Common Typing へ保存する。

### 6.4 並行して入った別の構成

`CommonBoundRefSolvedRows` / `CommonBoundRefSolved` / `CommonBoundRefSolvedExact` と
`CommonPresenceSolvedSource` は、同じ worklist を使う別の atoms 入力 solver/source 構成として保持した。
`CommonBoundRefSolved.generated_solve_all_instances_exact` と Core 版も実生成 clause の全モデル回収を述べる。

その構文 gate 付き Core entry は `Core.SyntaxGatedCommonInference` に移し、元の scheme・計算と theorem の
量化・前提・結論を保持した。この別 entry の拒否 iff には presence 構文への所属前提がある。
公開 `Core.infer` は §6.1–6.2 の入口を使い、その前提を混ぜない。元の二つの証明を捨てて統合したものではない。

## 7. 閉じていない補題

以下の名前は残契約の名前であり、証明済み theorem として引用しない。
元の復旧記録 §7.1–7.3 は §§3–5 で閉じ、7.4 の一般反映と 7.5 の全文法に関する部分が残る。

### 7.4 `legacy_shared_witness_recovery`

最小の未証明境界は、任意旧 supported source e と任意旧 computation c について、
Common Typing [] e (embedComp c) から、実生成 clause の共有旧 witness を回収することである。

```text
∀ e : Inference.Expr,
  SourcePrincipalInference.supported e = true →
  ∀ c : Inference.Comp oldModel,
    PresenceGeneration.Typing Common.model [] e (Common.embedComp c) →
    ∃ C ∈ PresenceNormalForm.normalise (PresenceGeneration.principal [] e),
      ∃ τ : Fin (C.locals + 1) → Inference.Comp oldModel,
        τ (Fin.last C.locals) = c
        ∧ PresenceNormalForm.All Common.model
            (CommonLegacyTyping.assignment τ) C.pack
```

`oldModel = SourcePrincipalInference.model Common.rowAlgebra`。
ここでは、最初の Common Typing に用いた clause と同じ clause を使うことも、中間 slot の全行を保存することも
追加要求しない。全 slot を一つの τ で同時に割り当て、出力 computation を c に保つことが必要である。

これが閉じれば、既証明の iff と旧 contextual instance 反映により、任意旧 supported e・任意旧 target c に対し、

```text
(Core.infer (Core.Required.embed e)).Instance (Common.embedComp c)
  → ∃ old : Inference.Comp oldModel,
      (SourcePrincipalInference.infer e).Instance Common.rowAlgebra old
      ∧ Common.Equivalent (Common.embedOld c.1) (Common.embedOld old.1)
      ∧ c.2 = old.2
```

という決定46の残る反映を得る。任意の新 exact/default target に無条件に反映する契約には拡張しない。

不足の理由は、embedding exactness が両端の旧像についての theorem であり、任意 Common witness の存在量化を
旧像へ移す theorem ではないことにある。旧 solver の全解回収も最初から旧 carrier のモデルを入力とする。
旧 parameters を一律 bottom へ変えるだけでは固定した出力 c を保持できない。

`CommonLegacyErasureBoundary.no_uniform_two_sided_erasure` は、全 Common 型を一つの関数で旧型へ消し、
全旧 target への比較と全旧 source からの比較をともに exact にする関数が存在しない、と証明する。
exactEmpty と width は全旧 target への上限比較が同じだが、width ≤ exactEmpty は偽なので矛盾する。
これは一様 erase という方法の否定であり、上の有限問題に依存した witness 回収の反例ではない。

並行更新の `CommonLegacyReflection.fixed_bounds_output_exact` も統合した。
任意の有限 lower/flow/upper/check 問題、任意の固定旧境界型の評価、任意の出力 slot と任意旧 target について、
Common witness がモデルを満たし出力が旧 target 以下となること iff 旧 witness が同じ条件を満たすことを示す。
これは全深さの Common.Subtype による意味的な有限 envelope であり、実行可能な型比較器ではない。
固定旧境界と全 flow は同時に保つが、未知子に依存する constructor 方程式はこの問題の入力に含まれない。
`CommonLegacyReflectionConstructors.envelope_does_not_preserve_pair_equation` は、任意二つの Common 型について、
top だけを test とする envelope が pair の方程式を保存しないことを示す。
したがって固定境界の補間を元 graph の共有 constructor witness 回収と同一視せず、上の残契約は維持する。

### 7.5 完全な public interface canonical encoding

残契約の量化は引き続き、任意の有限 public interface I/J に対する

```text
仕様上の等価性 I J ↔ canonicalEncoding I = canonicalEncoding J
```

である。ここでいう全 public interface を、既存 Form や固定 arity α 同値へ定義し直さない。
必要な未接続部分を次の三つへ分ける。

1. **有限 public 構文への意味を保つ readback**：任意の実 solved scheme/export を、弱い変数と一般化変数、共有 ID、
   出力行、regular graph、nominal identity、role obligations を保つ有限 public 表現へ読むこと。
   既存 Interface.scheme が表す局所 qualifier に加え、ambient-only の pending obligations と exportability を
   `finishModule` の意味まで保持すること。scheme.Holds だけの同値で pending も済んだことにしない。
2. **一般の再 parameter 化の完全性**：異なる一般化数 n/m を許す任意 I/J について、同じ weak/ambient 割当てと
   任意の結果・行・role 文脈を量化した仕様上の instance family 同値 iff 同じ有限 code。
   正負共有、共起、weakness、一般行式、regular/nominal/role を同時に扱うこと。
3. **実 export/display の接続**：その code を実 inference からの export と表示器が使い、変数の初出順、変数先行、
   具体型の辞書順、同一構成子の成分ごとの union grouping を保つこと。code の同一性と実表示の標準性を接続すること。

単なる全単射 α 正規化、未使用 slot 除去、各 scalar 葉の独立正規化、正負位置による instance 保存のどれも、
この全量化の代用にはならない。新しい意味論の選択ではなく、有限表現・同時求解・読み出しの内部接続義務として残す。

## 8. 7.5 で独立に閉じた部分

### 8.1 未使用 parameter と一般の有限置換

`CommonCanonicalParameters.compact_project_exact` / `compact_expand_exact` は、任意 n/Form・任意 rows と
任意旧/新 parameter について、実使用 k slot への除去の具体化を literal equality で両方向に回収する。
`compact_instances_exact` と subtype 版は全 instance family を保存・反映する。k=0 を許す。

`reparameterization_instances_exact` と subtype 版は、任意異 arity の Form と二つの有限 scalar 置換について、
両方向の pointwise 要求同値を前提に、全 instance family の一致を導く。置換の単射性や逆写像は要求しない。
ただし、その置換が存在するかを完全に判定する手続きではない。

### 8.2 `CommonCanonicalScalarFamilies.exactCanonicalEncoding_exact`

任意 w/n/m、任意の scalar lattice 式 `E : Expr (w+n)` と `F : Expr (w+m)` について、
先頭 w slot の assignment を両側で同じものに固定し、残る一般化 parameter だけを存在量化する。
全個数はゼロも許す。任意固定 ambient と任意 Common target T について、

```text
∃ p, instantiate (ambient,p) E ≈ T
  ↔ instantiate ambient (lower E) ≤ T
      ∧ T ≤ instantiate ambient (upper E)
```

を `exact_instances_iff_bounds` で証明する。lower/upper は全一般化 slot に bottom/top を置いた実構文。
`diagonal_retract` は全一般化 slot に T を置く具体的回収を与える。

その結果、全 ambient/T に関する exact family 同値 iff 二端点の canonical code 等号、
subsumption 後の family 同値 iff 下端の code 等号を、それぞれ
`exactCanonicalEncoding_exact` / `canonicalEncoding_exact` で証明する。
使用中の二変数の union と一変数を同じ family として比較でき、同数 α 同値への置換ではない。
弱い slot は同じ ID と値を保ち、一般化 slot と一緒には消さない。

### 8.3 `CommonCanonicalScalarExports.interface_canonicalEncoding_exact`

任意 w/n/m と上の二つの scalar 式に対して、obligations=[] の実 `QualifiedInference.Interface` を構成する。
任意 role theory・任意固定 ambient computation assignment・任意 target computation を量化した既存
`Interface.scheme.Holds` の同値が、上記 canonical code の等号と iff になる。
public interface の意味を新しく定義していない。role/row/regular を含む全文法への接続ではない。

### 8.4 `CommonCanonicalPolarity.simplify_instances_exact` / `normalize_instances_exact`

任意 n、任意 `Form n`、任意 `rows : Nat → Common.Row`、任意 `frozen : Fin n → Bool`、
任意固定 ambient 値、任意 Common target T について、frozen slot の値を ambient に固定した全 parameter の
upward instance family が、有限 simplify とその後の normalize で保存・反映される。

simplify は正だけに現れる非固定 parameter を bottom、負だけを top に置き、frozen と正負共有 slot は残す。
`instantiate_ordered` は各正出現で first≤last、各負出現で last≤first を仮定すると Form の値が first≤last に
なることを、任意 Common 型と任意行で示す。`selected_frozen` / `selected_mixed` は保持の literal equality。
role などの理由で固定すべき slot の自動発見は、この Form pass では証明していない。
この pass は role obligations 自体を持たず、role 付きの実 qualified Interface の意味を保存する接続も未証明である。
一般化 slot を変換中に固定する場合、その slot の値を保った上で元の外側の存在量化を残す必要があり、
弱い変数へ変更することを意味しない。
並行更新の `CommonCanonicalPolarityBoundary.normalize_not_idempotent` も保持した。
具体的な `'a -> ('a & bottom)` は一回目に `'a -> bottom`、二回目に `top -> bottom` となり、
一回の pass 自体は冪等ではない。全 instance の保存と、固定点に達する完全な標準形は区別する。

### 8.5 誤った一般化を防ぐ二つの反例

この節では、arrow の行割当て・引数行・結果行、および qualified interface の対象 computation の行を空行に固定する。

`CommonCanonicalScalarExports.Examples.shared_arrow_instances_iff` は、任意 Common 引数 A と結果 B に対し、
共有 `'a -> 'a` の instance に A→B が入ること iff A≤B を示す。
`negative_sharing_cannot_be_split` は int→str が独立 `'a -> 'b` には入るが共有型には入らないと証明する。

`qualified_output_instances_iff` は、実 qualified interface の正の出力変数に int だけの role 証拠を付けた場合、
任意 target T が instance になること iff int≤T を示す。
`positive_role_cannot_be_erased` は str がこの qualifier の有無を区別すると証明する。
正位置だけという理由で role 義務まで消す変換は採用しない。

### 8.6 並行更新の constructor family への拡張

`CommonCanonicalIntervals` は固定 captured slot と一般化 slot を分けた scalar family について、
同じ二端点による exact encoding と下端による upward encoding を別の構成で証明する。両構成を保持した。

`CommonCanonicalPositive.canonicalEncoding_exact` は、任意の fixed/n/m、任意の二つの Form について、
両方が `Positive` であることを仮定する。Positive は、一般化 slot の出現がすべて共変で、各 arrow domain が
captured slot だけを使うという構文条件である。captured slot 自体は正負に共有してよい。
この前提の下で、任意行割当て・任意固定 captured 値・任意 Common target を量化した upward family の同値と、
実 canonical code の等号が iff になる。n/m は異なってよく、pair・required・variant・arrow を含む Form の範囲まで
完全比較が広がる。一般化 slot が負位置にも共有される場合、全文法、role 義務や実全 export の完全性は含まない。

`CommonCanonicalObstructions` は、全変数が実際に現れる同 arity でも全単射 α 同値だけでは family 同値を
特徴づけられないこと、scalar の exact interval をそのまま pair の image へ一般化できないこと、
captured slot と一般化 slot、正負共有を区別する必要があることを証明する。

## 9. 検証と新しい問い

実行した統合 gate は次の二つ。

```sh
lake build --wfail
lake env lean --trust=0 Audit.lean
```

全新 module を `Yulang.lean` に登録し、`Audit.lean` の全 Yulang 宣言 allowlist 検査と主要 theorem の
`#print axioms` に接続した。許可する依存公理は既存の `propext`、`Classical.choice`、`Quot.sound` のみ。
sorry、追加の公理、native_decide は使わない。
環境復旧時の self-executable path shim は toolchain の起動を修復するもので、kernel や証明項は変更しない。

統合 build の末尾（exit 0）：

```text
Build completed successfully (554 jobs).
```

Audit の全宣言検査と末尾（exit 0）：

```text
Axiom allowlist passed for 47115 declarations from Yulang modules
...
'Yulang.CommonCanonicalPolarityBoundary.first_pass_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonCanonicalPolarityBoundary.second_pass_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonCanonicalPolarityBoundary.successive_passes_different' depends on axioms: [propext]
'Yulang.CommonCanonicalPolarityBoundary.normalize_not_idempotent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

最終 fetch で追加された `origin/yulang3` の `6a4cf521ac8472f1629c7f70b5f2fcfd7a8719dd` まで merge し、
その統合状態でも両 gate を再実行して exit 0 を確認した。追加更新は対象なしの `catch:`、
act 操作署名下の `where` などの parser・仕様・説明文書であり、上記の Lean 宣言数は変わらない。
`git diff --check` も成功した。

実計算の smoke では、int literal と empty record への int default が inferred を返し、int への int 適用と
未束縛変数を fallback に持つ default が rejected を返すことを確認した。
証明の代わりにこの有限例を使ってはいない。

**今回 `notes/questions/` に積んだ新しい問いは 0 件。**
残っている witness 回収・canonical readback・一般再 parameter 化は内部の証明義務であり、
Yulang のコードで区別できる新しい仕様選択として質問にしない。
