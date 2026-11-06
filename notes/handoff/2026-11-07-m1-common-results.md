# M1 共通 carrier・自由 presence family の実装結果

Status: Partial — proved concrete model and declared solver fragments; full source infer and full interface canonicality remain open.

Date: 2026-11-07

Branch: `integration/m1-common`, starting from `integration/types` at `1b9361b`.

`origin/yulang3` は作業中に `a50f015`、続いて `89004af` まで merge した。
`integration/types` と `yulang3` への書込みは行っていない。

この記録は [残契約](../design/2026-11-07-m1-remaining-contracts.md) の実装結果である。
新しい言語仕様の決定ではない。内部構成と代案は
[共通モデルの設計](../design/2026-11-07-m1-common-model.md) を参照する。

## 1. 到達点と境界

| 依頼の項目 | 到達点 | 残り |
| --- | --- | --- |
| 1. 共通 carrier | 独立な finite/regular 構文・再帰的要求意味、任意 parameter 環境、旧 regular 型の順序の保存／反映、無制限の arrow iff | 全 constructor graph の求解への接続は後続項目 |
| 2. exact/required/default | exact と width の意味的識別、strict whole-default の正確な data image、任意一観測の finite inspector、required／同名 record target の完全分解 | 任意 target の subtype 全体を有限 branch へ変える完全 inspector |
| 3. mask と同深さ tail | 全 mask の合同性、実 record/default の同深さ循環と guarded payload／負の arrow 子を共有する regular block の自由 family と回収 | 全入力不等式 compiler |
| 4. 行との同時接続 | guarded 子と同深さ tail を共有する有限 row/presence 方程式構文の全入力で simultaneous exactness。行は等号で回収 | 全 source clause と全型 inspector からの入力変換 |
| 5. Formula・束縛・source | 実 Formula の正規化、局所 slot packing、捕捉環境と全 Core/source 型判断の iff、生成 row support | 原子制約の全求解と全自由 family への接続 |
| 6. 公開 theorem・旧入口 | 旧 Typing／実旧 instance から独立した Common source/Core Typing への保存 | 統合 Core.infer、全 source 主型性・拒否完全性・unsupported 不出現、新 instance からの旧 instance 回収 |
| 7. 標準形 | scalar 格子式と固定 constructor Shape 内の完全 code、変数先頭・base 辞書順、Common の全代入への移送 | 全 interface 構文、α 正規化、行式、混合 head、regular graph、再parameter化 |

既存の theorem の結論・前提は弱めていない。旧 `normalize_not_complete` は旧 pass の正しい反例として
残し、新 pass の正しさと区別する。新しい統合 `Core.infer` を Formula.Holds の別名として導入していない。

## 2. 共通モデルの定理

以下で `S ≤ T` は `Common.Subtype S T`、`S ≈ T` はその双方向比較を表す。
`Row` は `(Nat × List Int) → Prop`、`rowLe` は集合包含である。有限／無限の自由行を保持する。

### 2.1 要求順序・旧型・arrow

`Common.common_subtype_exact` は、任意の `S T : Common.Ty` について、

```lean
Common.model.subTy S T ↔
  ∀ depth rank env demand,
    Common.AcceptAt depth rank env T demand →
      Common.AcceptAt depth rank env S demand
```

を示す。`Ty`、`Demand`、`Environment`、`AcceptAt` は solver／Typing／法則の field を使わない
独立構文と再帰的解釈である。環境には任意の finite 型または regular 型を割り当てる。
自由な source/scheme 変数は `TyTerm.var` と family parameter に保持し、具体化でこの carrier へ代入する。

`Common.contextual_embedding_exact` は、任意の旧 regular 型 `S T : RegularInferenceModel.Ty Common.Row` について、

```lean
Common.model.subTy (Common.embedOld S) (Common.embedOld T) ↔
  ProducerContextualRegular.ProducerLe
    (RegularInferenceModel.graph Common.Row) Common.rowLe S T
```

を示す。新環境を旧型に限定しない。`CommonFiniteEmbedding.contextual_embedding_exact_at` は任意の
行関係・旧有限型・rank で有限版を示し、`Common.embedOld_observe_exact` が任意深さの観測を保存する。
`Common.contextual_equivalence_exact` は双方向の同値版である。

`Common.common_arrow_iff` は任意の `A A' B B' : Common.Ty` と任意の四行について、

```lean
arrow A ei B eo ≤ arrow A' ei' B' eo' ↔
  A' ≤ A ∧ rowLe ei' ei ∧ B ≤ B' ∧ rowLe eo eo'
```

を示す。引数・結果の mask、default、regular graph、自由 parameter の具体化を除外しない。
行の前順序と反対称性は具体集合演算から証明し、公開 theorem の追加前提にしていない。
`common_pair_iff`、`common_variant_iff` も任意共通型の成分比較を保存・反映する。

### 2.2 Record と strict data image

- `exactEmpty_below_width`、`width_not_below_exactEmpty`：exact empty は width 以下で、逆は成立しない。
- `required_as_width_tail`：任意 label・payload で `record label payload emptyRecord = required label payload`。
- `common_record_iff`：任意 label・A・B・R・T で、`record label A R ≤ record label B T` iff `A ≤ B` と
  `RecordTailLe [label] R T`。残る tail 関係は同じ深さの、先頭 label 以外の field／非自明 optional 要求だけを比較する。
- `common_singleton_requirement_iff`：任意 label・A・B・R で、`record label A R ≤ required label B` iff `A ≤ B`。
  tail の record-shape 制約は構築時の型規則に残すが、同名 field 要求を tail に追加しない。
- `common_shadowed_head_equivalent`：任意 label・payload・hidden payload・rest で、同名の内側 head を消しても要求同値。

`Common.DataReadout` は同じ Common 構文上の独立帰納的 runtime 解釈である。任意の data 値 `v` について、
`exactEmpty_data_exact` は exact empty の読取り iff `v = record []`、`width_data_exact` は width の読取り iff
ある field 列の record であることを示す。

`default_data_image` は任意の label・source・fallback・result に対して、

```lean
DataReadout (recordDefault label source fallback) result ↔
  ∃ fields value,
    DataReadout source (.record fields) ∧
    DataReadout fallback value ∧
    result = .record (SourceDataRuntime.Fields.insertDefault label value fields)
```

を示す。present source でも fallback の値の存在を残す。`default_inhabited_iff`、`default_bottom_fallback` は
この strictness を補足する。要求同値から data 集合の同一性を仮定せず、関数を空の data 集合で代用しない。

`default_guarantees_field` は任意 label・source・fallback について、`source ≤ emptyRecord` を前提に
`recordDefault label source fallback ≤ required label top` を示す。
`default_exactEmpty` は source が exactEmpty の場合、`default_present_record` は source が同名の構文上の record head
である場合に限った要求同値を示す。`common_default_mono`／`common_default_congr` は任意 source/fallback 比較を扱う。

単に source ≤ required label top であることから default を消すことはできない。
`CommonDefaultBoundary.presence_does_not_erase_default` は任意 label について、
`inter exactEmpty (required label int)` を使う反例を示す。source ≤ width も同時に成立する。

### 2.3 Mask と Layer 合同性

`common_mask_parameter` は任意型・hidden label 列・深さ・rank・環境・要求で、実 mask の受理と独立した
`MaskedAcceptAt` を同値にする。`common_mask_composition` は任意型・二つの mask で、合成と label 列の連結を同値にする。

`common_mask_mono`／`common_mask_type_congr` は任意の `H,S,T` について、`S≤T`／`S≈T` なら mask 後も同じ比較を
与える。`common_equivalent_iff_masked` は通常の要求同値 iff 任意外側 mask 後の要求同値を示す。
parameter に別の mask 安定性証明を要求しない。

`CommonSyntax.Layer.evalAt_congr` は任意 Row・Index・行前順序・深さ・Layer・二つの payload 割当てで、各 payload が
全 rank の有限 `ProducerEq` で等しければ評価も等しいことを示す。`evalAt_masked_probe_iff` は全 rank・環境・mask・観測版。
負の arrow に payload の単調性を仮定せず、双方向同値の合同性を用いる。

## 3. 自由 family・生成器・標準形

### 3.1 実 record/default の同深さ方程式

`Common.common_record_polynomial` は任意 label・A・R について、

```text
record l A R ≈ inter (record l A top) (union (record l A bottom) R)
```

を示す。`CommonRecordTailElimination.compile_models_exact` はこの実 compiler の保存・反映である。
旧 data-demand の `inter(required l A)(mask [l] R)` をそのまま使わない。実際に tail=bottom では異なり、
`common_record_not_naive_required_mask` が任意 label・payload について否定する。

`CommonPresenceTailElimination` の入力は任意の有限 `atom/ref/union/inter/mask/record/recordDefault` graph。
未知 ref は同深さの tail と default source に置け、任意に循環してよい。payload/fallback の固定 atom は
任意の Common 型であり、その内部の arrow・mask・regular graph は制限しない。

名前空間内の三つの定理は、任意 graph `g`・任意 parameter／独立割当て `ρ` について次を示す。

```lean
solve_models (g) (parameters) : Models g (solve g parameters)

solve_retract (g) (ρ) (valid : Models g ρ) (i) :
  Common.Equivalent (solve g ρ i) (ρ i)

solved_instances_exact (g) (ρ) :
  Models g ρ ↔
    ∃ parameters : Fin slots → Common.Ty,
      ∀ i, Common.Equivalent (solve g parameters i) (ρ i)
```

`Models` は元の Body.eval の方程式であり solve を参照しない。右辺の parameter に残余 Models、support、
成功、Closed、fuel を付けない。有限反復は全深さ・全 rank・全環境・任意外側 mask・全観測に一様である。

さらに `CommonPresenceTailLayers.solveLayers_quote`／`solveLayers_map`／`solveLayers_evalAt` は、任意の symbolic graph、
Layer parameter、payload index 割当て、深さに対して、同じ四 mode 反復と引用／rename／有限評価が文字通り可換であることを示す。

`CommonPresenceTailRegular` は同じ graph の未知型を guarded 子と同深さ tail に同時に代入し、実 `closeBlock` で閉じる。
任意の有限 graph・任意の独立 `ρ : Fin slots → Common.Ty` について、次を証明した。

```lean
solveBlock_models (g) (parameters) : Models g (solveBlock g parameters)

solveBlock_retract (g) (ρ) (valid : Models g ρ) (i) :
  Common.Equivalent (solveBlock g ρ i) (ρ i)

guarded_solved_instances_exact (g) (ρ) :
  Models g ρ ↔
    ∃ parameters : Fin slots → Common.Ty,
      ∀ i, Common.Equivalent (solveBlock g parameters i) (ρ i)
```

ここでは payload/fallback や負の arrow 引数も同じ未知 slot を参照してよい。任意の既存 Common state への外部参照も許す。
`Models` は同じ ρ を両参照位置へ代入する元の方程式。parameter に成功・fuel・Closed・残余 Models は要求しない。
深さ帰納では前の深さの全 rank の payload 同値を用い、負位置に単調性を仮定しない。

### 3.2 行との同時求解

`CommonRowTailInference.joint_instances_exact` は、任意の宣言した有限 Problem・独立行割当て・独立型割当てについて、

```lean
Models problem rows values ↔
  ∃ rowParameters, ∃ valueParameters,
    (solve problem).instantiateRows rowParameters = rows ∧
      ∀ i, Common.Equivalent
        ((solve problem).instantiateValues rowParameters valueParameters i)
        (values i)
```

を示す。入力の行右辺は構文上 var/empty、左辺は任意 join。型 atom/payload/fallback は有限 Common 型構文に
symbolic arrow 行を持ち、行制約と同じ ID を共有する。same-depth source の record/default 循環も扱う。
加えて symbolic `.layer`、`.recordRef`、`.recordDefaultRef` により、guarded 子／負の arrow 引数／payload／fallback が
同じ未知型 ID を共有する。元の Body.eval と実 atRows の双方でその共有を保つ。
`solve_models` はどの自由行／値 parameter 割当てもモデルを与え、`solve_retract` は解自身を parameter にして回収する。
`unconstrained_rows_exact` は制約のない行を空へ default せず、そのまま保持する。

### 3.3 実 Formula と全 source

`PresenceNormalForm.presence_normalise_exact` は、任意 model・型 α・Formula α・自由 computation 割当て ρ について、

```lean
formula.Holds model ρ ↔
  ∃ clause ∈ normalise formula,
    ∃ locals : Fin clause.locals → Comp model,
      clause.Holds model ρ locals
```

を示す。旧 Formula と異なる実 presence Formula を処理し、局所値／行、共有 ID、捕捉 slot を保持する。
`principal_clauses_exact` は任意 source・schemes・bindings・割当て・結果と `EnvRel` の前提の下で型判断と同値。
`Clause.pack_exact` は閉 source の局所 slot と結果 slot を有限 index に移し、結果 computation を等号で保持する。

`closed_source_exact`／`closed_core_exact` は任意 model・任意閉式・任意結果 c で、独立 Typing iff
有限 clause の一つと、結果 slot が c に等しく全原子制約を満たす割当ての存在を示す。
support checker・推論成功・fuel は前提にない。ただし原子制約が残るため、これは全自由 solved family ではない。

`PresenceSourceConstraintSupport.generated_row_shapes` と `generated_explicit_rows_supported` は、任意 source e と
その生成 Formula の normalise に含まれる任意 clause について成立する。record/default も含む。
`generated_explicit_rows_models_exact` は任意行代数・任意独立行解で、実 row solver の自由 family から相互包含で回収する。

`CommonPresenceInspection.default_inspect_at_exact` は、任意 label・source・fallback・depth・rank・環境・一観測について、
whole default の受理 iff 実有限 DNF の子観測／負引数／行／role obligations の充足を示す。元の未分解 whole-default 比較は
atom に残さない。`CommonPresenceInspectionRows.inspected_rows_supported` は、source と query の行が var/empty である
前提の下で、実 branch の row atom を RowFlowSchemes が扱えることを示す。全 target の型比較への変換はまだ別である。

`CommonDefaultRequired.default_required_iff` は任意 label・S・F・P に対して、

```text
recordDefault l S F ≤ required l P
  iff OptionalPayload l S P ∧ (present l S = true ∨ F ≤ P)
```

を示す。`OptionalPayload` は任意 depth d・rank・有限環境・payload 観測について、P の深さ d の受理が
S の深さ d+1 の optional field 受理を含意するという独立条件である。`present` は outer syntax の実 Bool 計算で、
正の全深さにおける存在観測に一致する。深さ0は別に処理し、source shape の前提を要求しない。
`inspect_required_exact` はこれを独立な optional／presence／child 比較の実2 branch にする。

`default_record_iff` はさらに任意 tail T を量化し、同名の `record l P T` target に対する比較を、上の二条件と
`Common.RecordTailLe [l] S T` の三条件へ完全分解する。任意 source/fallback/payload/tail を扱う。
未知 source slot の optional/presence 条件を自由 parameter family まで解消したという主張ではない。

### 3.4 旧入口の保存

`CommonLegacyTyping.presence_typing_preserved` は任意旧閉式・任意旧結果について、旧 Typing を前提に
Common presence Typing を同じ行で保存する。`eval_value_observe` は任意旧 TyTerm・割当て・深さで評価の観測を等号で保存し、
`formula_preserved` は実 existential witness を移す。`compatible` の各条件は Common の具体演算から証明済み。

`legacy_instances_preserved`／`legacy_core_instances_preserved` は任意の旧 supported e・任意旧結果 c とその実旧 instance を
前提に、Common source/Core Typing を `embedComp c` に導く。新しい `Core.infer` の instance や反映の主張ではない。

### 3.5 Canonical encoding

`ProducerCanonicalClauses.canonicalEncoding_exact`／`normalize_exact` は、任意の行関係と閉 scalar lattice 式の二つについて、
contextual 要求同値 iff 同じ minimal clause code iff 同じ normalize 構文を示す。旧反例の int/str 順序は新 pass で一致する。

`CommonCanonicalOpen.canonicalEncoding_exact`／`normalize_exact` は、任意 n・二つの scalar lattice 式について、

```text
(同じ共有 ID への全 ρ : Fin n → Common.Ty の代入で要求同値)
  iff canonicalEncoding が同じ
  iff normalize が同じ構文
```

を示す。割当てには任意の regular/mask/default/arrow 型を含む。変数は先、base は bool/int/str/unit の辞書順。

`CommonCanonicalShapes.canonicalEncoding_exact`／`normalize_exact` は任意 n、固定した Shape と行割当て、二つの Term について
同じ主張を示す。nested pair、単一 required field、tag、scalar 引数と共通行 slot を持つ arrow、正の union を含む。
`collect_equivalent`／`normalize_equivalent` は任意の同時 parameter 割当てで評価を保存する。

これは固定した共有 ID に対する pointwise equality であり、存在的 instance 集合の再parameter化ではない。
Shape 内の code は Shape 自身の label・行 ID を省くため、異なる Shape を比較する standalone encoding ではない。
参照アルゴリズムは n+4 atom の全 profile を列挙する。既存 infer/display の呼出経路には接続していない。

## 4. 閉じていない正確な補題

ここで挙げる名前は実装済み declaration ではなく、未実装契約である。

### 4.1 任意 target の有限 inspector と全 compiler

任意 label・source・fallback・target について、

```lean
Common.Subtype (Common.recordDefault label source fallback) target ↔
  ∃ branch ∈ inspectDefault label source fallback target,
    IndependentObligationsHold branch
```

を示す `default_inspect_exact` が残る。任意一観測と、required／同名 record target についての完全分解はあるが、
任意 target の全観測の含意を一つの有限 branch にまとめる定理ではない。元の比較を obligation に包んで残す方法では
閉じたと数えない。新しい OptionalPayload／presence 義務も、未知共有 slot の全入力 graph 上で求解する必要がある。

`presence_compile_exact` は任意 finite input g・任意独立 computation 割当て ρ について、元 Models iff
実 compile が返すある branch の独立 Models と、全 slot の CompEquivalent な readback を要求する。
この変換が共有型／行 ID、負位置、exact/optional、mask、strict default を保つ必要がある。

### 4.2 全 source の solved family と公開 infer

`presence_joint_instances_exact` の全入力版と、実 packed clause をその入力へ変換する補題が残る。
既存の row theorem は explicit atom と一点観測 inspector の辺を扱うが、未完成の全 target compiler が作る全辺まで
扱ったとは主張できない。

`presence_generated_solved_exact` は任意 source e・結果 c で、生成 principal Formula の充足 iff
実際の有限 solved scheme と、制約なしの自由 row/value parameter の具体化が c 以下であることを要求する。
現在の `closed_core_exact` に残る `All` 原子制約を、この段階で消去する必要がある。

これが閉じるまで、全 source の `core_infer_principal`、`core_infer_rejected_iff`、`core_infer_not_unsupported` は未完。
同様に `legacy_instances_reflected` は、任意旧 supported e・任意の旧結果の埋込みについて、新 infer instance から
同じ結果行の要求同値な旧 instance を回収する部分が残る。既存 instance の定義を変えて代用していない。

### 4.3 完全な interface 標準形

有限 interface 構文の任意二つ I,J について、仕様の interface equality iff 自己完結した canonical encoding の一致を
示す必要がある。現在の固定 ID／固定 Shape の定理からは次が残る。

- binder の出現順による α 正規化、weak variable、正負位置に基づく parameter の消去／併合と再parameter化。
- row 式と共有行 ID、異なる shape、mixed constructor heads、一般 record/default/mask。
- nominal／条件付き role の interface 義務、regular graph の同値判定と一意化。
- 表示と export の実際の interface 構文への接続、参照アルゴリズムの費用評価。

全 concrete Common.Row は任意述語なので、その全 inhabitant を直接有限文字列へ計算可能に符号化する契約にはしない。

## 5. 検証

Lean 4.35.0 の公式 release toolchain を使用する。コード検証の gate は次の二つ。

```sh
lake build
lake env lean --trust=0 Audit.lean
```

両方とも最終統合後に **exit code 0** で成功した。build 末尾：

```text
✔ [444/447] Built Yulang.CommonDefaultRequired (2.8s)
✔ [445/447] Built Yulang.CommonDefaultRecord (664ms)
✔ [446/447] Built Yulang (1.1s)
Build completed successfully (447 jobs).
```

Audit 末尾：

```text
'Yulang.CommonDefaultRequired.default_exactEmpty_required_iff' depends on axioms: [propext, Quot.sound]
'Yulang.CommonDefaultRequired.default_present_required_iff' depends on axioms: [propext, Quot.sound]
'Yulang.CommonDefaultRequired.default_optional_required_iff' depends on axioms: [propext, Quot.sound]
'Yulang.CommonDefaultRequired.presence_cutoff_differs' depends on axioms: [propext, Quot.sound]
'Yulang.CommonDefaultRequired.finite_default_record_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonDefaultRequired.default_record_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonDefaultRequired.default_record_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

全 Audit 出力で現れた公理名の集合は `Classical.choice`、`Quot.sound`、`propext` のみ。
新しい Lean module 36 個について `sorry`／`admit`／追加 `axiom`／`native_decide` の実コード使用は0件。
元から存在した `lean/Yulang/*.lean` の theorem module は変更していない。
`git diff --check` も成功した。

実行環境では公式 Lean バイナリが読む `/proc/<pid>/exe` の公開差を補う起動用 shim を使用した。
自プロセスの executable path を `/proc/self/exe` から読むだけであり、Lean kernel／elaborator／証明の信頼設定は変更していない。
通常の Lean 環境では上記二コマンドをそのまま使う。

## 6. 新しい問い

`notes/questions/` に追加した新しい問いは **0件**。
今回の未完部分は既存仕様の下での Lean 内部の構成・compiler 補題であり、Yulang の観測可能な仕様選択として
ユーザーへ返す問いを新たに作っていない。Q1・Q5 の回答と Q4 の仮前提を変更していない。
