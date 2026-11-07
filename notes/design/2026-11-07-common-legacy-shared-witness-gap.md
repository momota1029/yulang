# A1: 全旧 supported source の共有 witness に残る構成

日付: 2026-11-07。状態: **Draft — 調査結果。元の A1 statement は未証明。**

対象は [前回の引継ぎ](../handoff/2026-11-07-core-common-coverage-results.md) §7.1 の
`legacy_generated_shared_witnesses` そのもの。このメモは新しい部分言語 theorem を追加せず、
既存結果で消えている部分と、まだ必要な構成を区別する。

## 1. 変更しない目標

`old Comp := Inference.Comp CommonLegacyEmptyReflection.legacyModel` とする。
必要な量化と前提は次の通りである。

```text
任意 e : Inference.Expr,
  SourcePrincipalInference.supported e = true →
任意 c : old Comp,
  PresenceGeneration.Typing Common.model [] e (Common.embedComp c) →
∃ clause ∈ PresenceNormalForm.normalise (PresenceGeneration.principal [] e),
∃ values : Fin (clause.locals + 1) → old Comp,
  values (Fin.last clause.locals) = c ∧
  PresenceNormalForm.All Common.model
    (CommonLegacyTyping.assignment values) clause.pack
```

旧結果 `c` の値は任意の旧 regular 型、行も任意である。
`ClosedConstructors e`、旧 solver 成功、既知の共有 witness は前提にしない。
target を任意の新 exact/default 型に広げる主張でもない。

回収するのは、一つの実 generated clause と、その全 slot に対する一つの共有旧割当てである。
出力 slot は値と行の組として `c` に等しく保つ。
元の Common 導出と同じ clause を選ぶことや、元の全内部 type/row witness を保存することは要求していない。

## 2. 既存 iff による正確な不足部分

`CommonLegacyEmbeddedWitnesses.embedded_witnesses_iff_typing` は、任意 `e`、
`e.requiredFieldsOnly = true`、任意旧 `c` について、上の結論の共有 witness 存在と

```text
Inference.Typing CommonLegacyEmptyReflection.contextualModel [] e c
```

が同値であることを既に示している。実 clause の翻訳、binder slot と出力の対応もこの theorem に含まれる。
`SourcePrincipalInference.supported e = true` から `requiredFieldsOnly` は定義により得られる。
したがって A1 の残りは、正確に次の反映である。

```text
任意 e : Inference.Expr,
  SourcePrincipalInference.supported e = true →
任意 c : old Comp,
  PresenceGeneration.Typing Common.model [] e (Common.embedComp c) →
  Inference.Typing CommonLegacyEmptyReflection.contextualModel [] e c
```

これは単なる十分条件への強化ではなく、上の既存 iff の下で元の A1 と同値な不足である。
反対向きの旧 contextual typing から Common typing への保存は、既存
`CommonLegacyEmbeddedWitnesses.contextual_typing_preserved` が任意 required-field source に対して証明済み。
残る片方向を示せば、旧 contextual completeness と既存の `Core.infer_embed` を使って、
全旧 supported source の instance 反映へ進める。

## 3. なぜ constructor 部分言語の追加では閉じないか

`SourcePrincipalInference.recordFree_supported` は、任意の
`SourceConstraintSupport.RecordFree e` に対して `supported e = true` を示す。
この文法は var、一般の λ/application、両 let、branch、pair と射影、field、variant、empty record を再帰的に含む。
たとえば `.lam (.app (.var 0) (.var 0))` も support の対象である。
support は制約表現の条件であり、式が型付くことや solver が成功することではない。

既存 `CommonLegacyWitnessSource.typing_exact` / `shared_witness_recovery` は
`ClosedConstructors` を前提とする。そこには var がなく、λ の body 自体が閉じている。
これらを保持したまま一般の binder 利用、共有、application、let を扱う必要がある。

一般の Common 導出の内部型は旧型の埋込みとは限らない。
生成された arrow、pair、record などの子に同じ unknown が現れ、比較の両側にもその値が共有される。
arrow の入力では比較の向きが反転する。
必要なのは、これらの constructor 条件と共有比較を一つの旧 regular 割当てで同時に満たし、
計算行の比較も満たした上で、指定された出力 `c` をそのまま回収する構成である。

## 4. 既存道具で届く範囲

| 既存結果 | 示している範囲 | A1 に残る差 |
| --- | --- | --- |
| `CommonLegacyReflection.fixed_bounds_models_exact` / `fixed_bounds_output_exact` | 固定された旧 bound と共有 variable flow、および任意旧出力との比較の反映 | bound 自身の constructor の子に共有 unknown が入る場合は対象外 |
| `CommonLegacyReflectionConstructors` の pair/variant/arrow 境界補題 | 任意 Common の子を持つ constructor と、固定旧 constructor との一境界比較 | 複数境界で共有する未知の子と constructor 方程式全体の同時実現は示さない |
| `CommonLegacyWitnessPositive.Agrees.arrow` | 旧入力型の埋込みと、対応する出力を持つ arrow の観測一致 | 任意の新しい負位置を旧型へ移す構成は含まない |
| `TypeConstraintGraphEquivalence.compile_extend_exact` | 同じ model 内での有限 source compiler と constructor realization の対応 | Common の realization から旧 carrier の realization を作る theorem ではない |

独立に各 node へ有限 envelope を適用する方法は、既存
`CommonLegacyReflection.envelope_does_not_preserve_pair_equation` により pair 方程式を保たない。
全新型を一様に旧型へ写し、全旧型との比較を両方向で保つ方法も、既存
`CommonLegacyErasureBoundary.no_uniform_two_sided_erasure` により成立しない。

**いずれも A1 自体の反例ではない。** A1 は全域の一様 erasure を要求せず、
個々の source の制約を見て適切な共有旧 witness を選べる。
また、元の各内部 witness を node ごとに固定した写像で置換することも要求していない。
これらの反例から A1 が偽だとは結論しない。

## 5. 次に必要な構成

次は、元の source と固定旧出力を入力に、constructor の正負位置、共有 slot、行比較をまとめて扱う
旧 regular witness の再構成を作る必要がある。
有限 graph の解を共同で作る方法でも、環境の関係を補強した source induction でもよいが、
追加する内部不変条件は実 generated source から証明し、A1 の前提へ移さない。

とくに、fixed-bound の反映を呼ぶ前に constructor の子を独立した旧定数だと扱うことはできない。
選んだ値を他の constructor と flow が共有する条件まで同時に回収する必要がある。
循環する制約を含む場合も有限 regular 表現として処理し、
成功 cache や都合のよい witness を外から受け取る theorem で代用しない。

今回、この構成と元の `legacy_generated_shared_witnesses` は追加していない。
同名の前提を強めた theorem も作っていない。新しい `notes/questions/` はなし。
