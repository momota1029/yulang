# M1 共通モデル作業の復旧と追加実装

Status: Partial — finite outer record/default inspection and actual source graph elimination are proved; unconstrained source inference and full interface canonicality remain open.

Date: 2026-11-07

Branch: `integration/m1-common`

復旧元は、このブランチの clean な `e4c12b9450d5ca073c1d87eb07d86a12394a8de4`。
`integration/types` の `1b9361b` から開始した既存作業を継続し、同じ成果を作り直さずに未完部分を追加した。
作業中に `origin/yulang3` を再取得し、`89004af` が既に merge 済みであることを確認した。
書込み先は `integration/m1-common` のみであり、`integration/types` と `yulang3` は変更していない。

[元の残契約](../design/2026-11-07-m1-remaining-contracts.md) の量化・前提は縮小していない。
[初回の結果](2026-11-07-m1-common-results.md) は復旧元 snapshot の記録として残す。
内部構成、採用しなかった案、理由は [共通モデルの設計 §9–12](../design/2026-11-07-m1-common-model.md) に追記した。

## 1. 到達点

| 依頼の項目 | 復旧後の追加 | 現在の境界 |
| --- | --- | --- |
| 1. 独立共通 carrier | 既存の具体構文・再帰的要求意味と任意の負位置・regular graph を保持。新たに payload 射影、境界消去、生成 graph を同じ carrier へ接続 | solver の成功や法則を carrier の定義に埋め込んでいない |
| 2. exact/required/default | 任意 target に対する whole default・通常 record・required の完全な有限 outer inspector。optional の深さ付き義務と全 label の tail 義務も普通の子型比較へ消去 | regular な子比較の反復と、未知 slot を扱う symbolic saturation は未完 |
| 3. mask と同深さ tail | 実 source pool の変数辺を共有方程式へ置換し、既存の同深さ/guarded regular solver に接続。全元 slot の要求同値な回収 | 残る非変数 node 間比較の解消 |
| 4. 行との simultaneous 接続 | 全明示行制約と変数辺・定義方程式を同時に消去。元の行 ID と arrow の両行を保持し、行は等号で回収 | symbolic inspector が追加する行辺まで含む閉性・完全性 |
| 5. Formula・束縛・source | 実 normalize/pack/pool/row/regular solver を結び、任意閉式・任意結果について残余条件付き principal iff | parameter の条件を一切残さない family への接続 |
| 6. 公開 theorem・旧入口 | support・成功・fuel の公開前提がない残余条件付き source/Core theorem | 要求された `Core.infer`、拒否 iff、対象断片の unsupported 不出現、新 solved instance から同じ行の旧 instance の回収 |
| 7. interface 標準形 | Shape/label/共有行 ID を含む自己完結 code。有限型パラメータの同時全単射による α 正規化と、最初の出現順の番号付け | 全 interface 構文、正負位置による消去・併合、一般再parameter化、行の α 同値、弱い変数、regular interface、実表示への接続 |

**M1 全体を完了とはしていない。** 今回は concrete outer inspector を閉じ、実生成入力から未解消の比較だけを取り出すところまで進めた。
残余を `Models` や scheme の law field に隠したり、旧 theorem を限定したりしていない。

## 2. 記法と量化範囲

- `S ≤ T` は `Common.Subtype S T`、`S ≈ T` はその双方向比較。
- `Common.Ty` は既存の独立 finite/regular 構文。mask、whole default、任意の負の arrow 子を除外しない。
- `Common.Row` は `(Nat × List Int) → Prop`。有限行に制限せず、比較は集合包含。
- `Holds E v` は有限比較列 E の各 `(i,j)` について `v i ≤ v j` が成り立つこと。
- `GoodAtoms a` は明示行制約の右辺が構文上 var/empty である条件。左辺には join を許す。
  実 source 生成器の全 clause が満たすことは既存の `generated_row_shapes` により証明済み。
- source は `Inference.Expr`、Core は `Core.Required.Term` と presence 用の `CoreRules.model Common.model`。
  後者は全 Core 構文を量化するが、全言語の型規則を一つに統合したモデルではない。
  presence 断片外ではこのモデルの型判断が存在せず、対応する生成 clause は空となる。

以下は主な公開 theorem の説明である。内部の合同性・リスト操作の補題も同じ global Audit の対象となる。

## 3. Payload 射影と任意 target の有限分解

### 3.1 `CommonPayloadProjection.optional_type_exact` / `field_type_exact`

任意の外側 mask `H : List Nat`、label `l : Nat`、source `S : Common.Ty`、
深さ `d : Nat`、負文脈 rank `r : Nat`、有限要求環境 `env`、観測 `o` について、

```text
MaskedProbeAt r env H (observeTy (d+1) S) (optional l o)
  ↔ ProfileAt d r env (optionalType H l S) o

MaskedProbeAt r env H (observeTy (d+1) S) (field l o)
  ↔ ProfileAt d r env (fieldType H l S) o
```

が成立する。`optionalType` / `fieldType` は実 Layer を走査し、元の guarded 子参照を保持した有限格子式を作る。
regular graph を深さの有限サンプルへ置き換えない。`none` は自明観測さえ受理しない profile、
`some top` は自明観測を受理する profile なので区別する。

基礎の `optionalProject_exact` / `fieldProject_exact` は任意の行関係、要求環境、引数比較関係、
payload 割当て、深さ、mask、label、Layer、観測について有限解釈の同じ iff を証明する。
`Payload.observe_common` は任意の深さ・射影 payload について、子参照を Common graph へ戻す操作と有限観測の可換性を保証する。

### 3.2 `profileBelow_exact` / `profileLe_exact` / `optional_payload_exact`

任意の `p q : Option Common.Ty` と `T : Common.Ty` について、

```text
ProfileBelow p T
  ↔ ∀ d r env o, ProbeAt r env (observeTy d T) o → ProfileAt d r env p o

ProfileLe p q
  ↔ ∀ d r env o, ProfileAt d r env q o → ProfileAt d r env p o
```

が成立する。`ProfileBelow none T = False`、`ProfileBelow (some S) T = (S ≤ T)`。
`ProfileLe p none = True`、`ProfileLe p (some T) = ProfileBelow p T` である。

任意の `l S T` について、

```text
CommonDefaultRequired.OptionalPayload l S T
  ↔ ProfileBelow (optionalType [] l S) T
```

が成立する。従来の全深さ・全観測にわたる shifted optional 義務を、普通の subtype 比較へ消去した。

`default_required_projected_iff` は任意の `l S F P` について、

```text
recordDefault l S F ≤ required l P
  ↔ ProfileBelow (optionalType [] l S) P
      ∧ (present l S = true ∨ F ≤ P)
```

を証明する。`default_record_projected_iff` は任意の追加 tail `T` に対する
`record l P T` への比較で、同じ右辺に `RecordTailLe [l] S T` を加えた iff となる。
source の存在判定や shape を呼出側の前提にはしない。

### 3.3 `CommonRecordEnvelope.envelope_below_iff`

任意の `T : Common.Ty` について、

```text
Common.record 0 bottom bottom ≤ T ↔ outsideRecords T = false
```

が成立する。`outsideRecords` は対象 Layer の role/head 式を実際に評価する Bool。
任意の子型、mixed head、mask、regular 参照を許し、非 record head による障害をこの有限判定へ集める。

### 3.4 `CommonRecordTailProfiles.tail_profiles_exact` / `CommonRecordTailFinite.tail_finite_exact`

任意の `H : List Nat`、`S T : Common.Ty` について、

```text
RecordTailLe H S T
  ↔ ∀ l, l ∉ H → AtLabel S T l
  ↔ ∀ l ∈ inspectLabels H S T, l ∉ H → AtLabel S T l
```

が成立する。`AtLabel` は次の四条件の積であり、元の tail 義務を含まない。

1. target の深さ0 field Bool が true なら source も true。
2. target の深さ0の非自明 optional Bool が true なら source も true。
3. `ProfileLe (fieldType [] l S) (fieldType [] l T)`。
4. `Subtype ((optionalType [] l S).getD top) ((optionalType [] l T).getD top)`。

`inspectLabels` は H と S/T の outer record/default/mask に現れる label、それらにない fresh label 一つからなる。
`inspectLabels_length` は任意の H/S/T について、その長さが
`H.length + (labels S).length + (labels T).length + 1` と等しいことを証明する。
label が重複したままでも正しい。payload 内の label を外側の層に混ぜない。

### 3.5 `CommonDefaultInspection.default_inspect_exact`

任意の `l : Nat`、`S F T : Common.Ty` について、前提なしで、

```text
recordDefault l S F ≤ T
  ↔ ∃ branch ∈ inspectDefault l S F T,
      ∀ (A,B) ∈ branch, A ≤ B
```

が成立する。head/presence/深さ0の Bool を実行してから、最終 branch として
`List (Common.Ty × Common.Ty)` だけを返す。失敗は空リスト、成功は子比較の branch 一つとなる。
`OptionalPayload`、`RecordTailLe`、元の whole-default 比較、Formula、Typing を最終 atom に残さない。

中間の `CommonDefaultTargetSplit.default_target_split` は同じ任意入力で、
head guard、selected field/optional の profile 比較、label l を隠した source-tail 比較への iff を与える。
`compileDefault_exact` / `discharge_exact` はこの分解を実有限 inspector の出力へ接続する。

これは outer 一層の完全な分解である。子比較が regular graph の同じ state に戻る場合の
有限飽和や、parameter を具体化する前の symbolic 分岐・閉性までを主張していない。

### 3.6 `CommonRecordInspection.record_inspect_exact` / `required_inspect_exact`

任意の `l : Nat`、payload `P`、rest `R`、target `T : Common.Ty` について、

```text
record l P R ≤ T
  ↔ ∃ branch ∈ inspectRecord l P R T,
      ∀ (A,B) ∈ branch, A ≤ B
```

が成立する。任意の `l P T` について required 版は、rest を `Common.emptyRecord` にした同じ iff となる。
`record_target_split` は head guard・P の field/optional 比較・`RecordTailLe [l] R T` の四条件への iff、
`record_tail_hidden` は構築した先頭 field を tail 義務から取り除く同値を証明する。
実装はこの分解を直接 compile し、default への付替えを実行していない。
`emptyRecord` を exact empty と読み替えず、spec 4.3 の先頭 field を除く規則を保つ。

## 4. 実 atom 列・共有 graph・行・変数辺の消去

### 4.1 `CommonPresenceConstraintGraph.compile_atoms_exact` / `realizes_evaluate`

任意の `m : Nat`、実 packed atom 列 `a : List (Atom (Fin m))`、独立 computation 割当て
`assignment : Fin m → Comp Common.model` について、

```text
All Common.model assignment a
  ↔ ∃ values : Fin (compile a).size → Common.Ty,
      (compile a).Models (fun i => (assignment i).row) values
      ∧ (compile a).readback (fun i => (assignment i).row) values = assignment
```

が成立する。Models は実 constructor 方程式、有限 subtype edge、元の行制約の独立な積である。
solver や Typing で定義していない。pool は元変数をすべて保存し、`input_injective` / `compile_input_injective`
はその埋込みが任意の pool/problem で単射であることを証明する。

`realizes_evaluate` は任意の pool・rows・node 割当てについて、元の constructor 方程式を実現するなら、
pool 内のすべての subterm が元の変数の readback による評価と要求同値となることを保証する。
正準的に構成した一つの割当てだけをモデルとする証明ではない。

### 4.2 `CommonPresenceClauseFamily.family_instantiates` / `family_retracts`

任意の `m`、atom 列 a、`good : GoodAtoms a`、任意の
`rowParameters : Fin m → Row` と `valueParameters : Fin (compile a).size → Ty` について、
実 `family a good` の具体化は全定義方程式と全明示行制約を満たす。
parameters に別の意味的条件を課さない。

同じ a/good の任意の独立モデル rows/values に対して、元 rows/values を parameters に選ぶと、
具体化した全行が元の行と等しく、全 node の値が元の値と要求同値になる。

`eliminate_definitions_exact` は任意の a/good/rows/values について、元 Models が、
この行等号・全値同値を満たす parameters と、具体化した値で元 subtype edge が成立することの存在に同値である。
ここでは subtype edge は明示的な残余条件として残る。

### 4.3 `CommonBoundCoalescing` の固定境界消去

任意の `n : Nat`、型 `Bound`、固定した解釈 `evaluate : Bound → Ty`、有限問題
`P : LayerBoundTemplates.Problem n Bound` について、次を証明した。

- `rigid_comparisons_exact`:
  `Consistent evaluate P ↔ Models evaluate P (lower evaluate P)`。
- `expand_satisfies`:
  `Consistent evaluate P` が成立すれば、任意の `parameters : Fin n → Ty` に対して
  `Models evaluate P (expand evaluate P parameters)`。
- `expand_retraction`:
  任意の `value : Fin n → Ty` が `Models evaluate P value` を満たせば、すべての i で
  `expand evaluate P value i ≈ value i`。
- `all_instances_exact`:
  任意の `value : Fin n → Ty` について、
  `Models evaluate P value ↔ Consistent evaluate P ∧ ∃ parameters, ∀ i, expand evaluate P parameters i ≈ value i`。

`Consistent` は実際に計算した有限リスト `rigidComparisons P` の固定境界間比較だけである。
変数間の全経路を伝播した lower/upper の比較と、元の check を含む。
lower/flow/upper/check の向きと変数循環を保つ。求解可能性や非循環性を入力前提にしない。
自由 parameter を一つの型カタログや正位置だけに制限しない。

### 4.4 `CommonPresenceVariableBounds` の実 source pool への接続

`template_models_exact` は任意の `pool : Pool m`、有限 edge 列 E、全 node の境界割当て v、
元変数割当て p について、分類した lower/flow/upper/check のモデルであることと、
元変数 node だけを p に替えた `mixed pool v p` が元 E を満たすことが同値であると証明する。

`variable_some_iff` は任意の pool/slot/index について、実 node が変数 index と判定される iff
`slot = pool.input index` を証明する。`residuals_rigid` は任意の pool/E と、計算した残比較の任意の要素について、
両端が元 pool の非変数 node であることを証明する。

`solve_realizes` は任意の pool/E/rows、任意の型 parameter p、任意の recursive parameter q について、
実 regular solver の `solve pool E rows p q` が元の全 constructor 方程式を実現することを保証する。

`solve_edges` は同じ入力について、計算した rigid 比較が解上で成立することを前提に、元の全 edge の成立を与える。
`solve_retract` は任意の元 node 割当て v が元方程式と E を満たせば、p に元入力変数、q に全 v を選ぶことで、
すべての元 node が要求同値で回収されることを証明する。

`eliminate_variable_edges_exact` は任意の pool/E/rows/v について、

```text
Realizes pool rows v ∧ Holds E v
  ↔ ∃ p : Fin m → Ty, ∃ q : Fin pool.size → Ty,
      Holds (rigidComparisons (template pool E)) (solve pool E rows p q)
      ∧ ∀ i, solve pool E rows p q i ≈ v i
```

を証明する。元の変数 edge と definition witness は右辺から消えている。

`compiled_joint_elimination_exact` は、任意の m、実 atom 列 a、`good : GoodAtoms a`、
独立行割当て rows、全 compiled node 割当て v について、

```text
(compile a).Models rows v
  ↔ ∃ rowParameters, ∃ parameters, ∃ recursiveParameters,
      solveRows a good rowParameters = rows
      ∧ Holds (rigidComparisons (template pool edges)) solvedValues
      ∧ ∀ i, solvedValues i ≈ v i
```

を証明する。ここで pool/edges は実 compile のもの、`solvedValues` は同じ具体化行を arrow annotation に
代入した `solve pool edges (solveRows a good rowParameters) parameters recursiveParameters`。
三つの parameter の型はそれぞれ `Fin m → Row`、`Fin m → Ty`、`Fin (compile a).size → Ty` である。

ここで「rigid」は元 pool の非変数 node を意味する。境界型が未知 graph の子に依存しない、という意味ではない。
残る `Holds` は parameters に依存し、全自由 family の完成を主張していない。

## 5. 残余条件付き source/Core principal theorem

### 5.1 方程式・行制約を消去した入口

`CommonPresenceSourceFamily.residual_source_principal` は任意の `e : Inference.Expr` と任意の
`c : Comp Common.model` について、公開前提なしで、

```text
Typing Common.model [] e c
  ↔ ∃ S ∈ inferSource e,
      ∃ rows : Fin S.rowParameters → Row,
      ∃ values : Fin S.valueParameters → Ty,
        S.ResidualHolds rows values ∧ S.instantiate rows values ≤ c
```

を証明する。`residual_core_principal` は任意の `e : Core.Required.Term` と同じ任意の c について、
左辺を `Core.Typing (CoreRules.model Common.model) [] e c`、右辺の入口を `inferCore e` に替えた同じ iff である。

`inferSource` / `inferCore` は実際の normalize、binder packing、共有 pool、同時 row/definition solver を呼ぶ。
捕捉された poly/signature の環境を含む `typing_subsume` を別途証明して、任意の上位結果 c への接続を保つ。
support checker、推論成功、solver 解、fuel を公開前提にはしない。

この module の `ResidualHolds` は具体化した元の有限 subtype edge 列の成立である。
元の `Typing` や `Formula.Holds` の別名ではないが、存在的制約が消えた全自由 family でもない。
専用 namespace の入口として置き、公開 `Core.infer` にはしていない。

### 5.2 変数辺も消去した実 source/Core 入口

`CommonPresenceCoalescedSource.residual_source_principal` は任意の `e : Inference.Expr` と任意の
`c : Comp Common.model` について、前提なしで、

```text
Typing Common.model [] e c
  ↔ ∃ S ∈ inferSource e,
      ∃ rows : Fin S.parameters → Row,
      ∃ types : Fin S.parameters → Ty,
      ∃ recursiveTypes : Fin S.pool.size → Ty,
        S.ResidualHolds rows types recursiveTypes
        ∧ S.instantiate rows types recursiveTypes ≤ c
```

を証明する。同 namespace の `residual_core_principal` は任意の `e : Core.Required.Term` と同じ任意 c について、
左辺を `Core.Typing (CoreRules.model Common.model) [] e c`、右辺を `inferCore e` に替えた同じ iff である。
実 pool、元 edge topology、求解済み行構文、出力 ID だけを持つ有限 Scheme を生成し、
具体化時に元変数の境界消去と regular solver を実行する。型付け証拠や意味的モデル証明を Scheme に格納しない。

この新入口の `ResidualHolds` は計算した `rigidComparisons` の成立だけであり、元の全 edge 列ではない。
`Scheme.residuals_rigid` は任意の Scheme と、その residual の任意の比較について、両端が元 pool の非変数 node であることを証明する。
その子には未知変数が現れてよいので、残余は依然として三 parameter family に依存する。

`clause_parameter_retraction` は任意の clause、`good : GoodAtoms clause.pack`、
任意の元割当てについて、packed atoms が成立すれば三 family が存在し、残余成立、結果値の要求同値、
結果行の文字どおりの等号がすべて成り立つことを証明する。
`clause_instantiation_models` は任意の clause/good と任意の三 family について、残余が成立すれば、
その具体化が元 compiled graph の全 constructor 方程式・行制約・変数辺を満たすことを証明する。

二つの principal theorem では GoodAtoms を生成不変量から供給するため、公開前提に残さない。
support、推論成功、solver model、fuel も公開前提にない。
これは residual の内容を rigid-rigid 比較まで減らした接続であり、residual 自体を除いた最終公開 theorem ではない。

## 6. 自己完結した code・α 正規化・名前順

対象は `CommonCanonicalInterface.Form n` および `Interface n` の有限文法である。
scalar lattice、nested pair、単一 required field、単一 tag、scalar 引数と同じ行 ID を共有する arrow を扱う。
`Interface` は自身の Shape とその Shape の `Term` を持ち、同じ構成子の union は従来の `collect` で成分ごとにまとめる。
二つの interface が同じ Shape であることを比較の前提にしない。

### 6.1 `CommonCanonicalInterface.interface_canonicalEncoding_exact`

任意の `n : Nat`、任意の `I J : Interface n` について、

```text
(∀ rows : Nat → Row, ∀ parameters : Fin n → Ty,
   I.instantiate rows parameters ≈ J.instantiate rows parameters)
  ↔ I.canonicalEncoding = J.canonicalEncoding
```

が成立する。`canonicalEncoding_exact` は Form 版、`interface_normalize_exact` / `normalize_exact` は
code の一致を実 normalize 出力の一致へ替えた定理である。
`interface_normalize_equivalent` は任意の I/rows/parameters について意味保存、
`normalize_idempotent` は任意の Form について冪等性を証明する。

code は構成子、label、arrow の共有行 ID を含む。
`equivalent_root` / `equivalent_required_label` / `equivalent_arrow_rows` は、各文法の任意入力が全代入で同値なら、
対応する root/label/両行 ID が等しいことを実観測で証明する。
`Examples.int_str_order_fixed` は `int | str` と `str | int` の新出力が同じであることを kernel で検証する。
旧 `normalize_not_complete` の正しい反例は削除・弱化していない。

### 6.2 `CommonCanonicalAlpha.canonicalEncoding_exact` / `normalize_exact`

任意の n と二つの `F G : Form n` について、

```text
(∃ π : Fin n の全単射,
   ∀ rows : Nat → Row, ∀ parameters : Fin n → Ty,
     (rename π F).instantiate rows parameters ≈ G.instantiate rows parameters)
  ↔ canonicalEncoding F = canonicalEncoding G
```

が成立する。右辺の canonicalEncoding はこの module の α encoder である。
独立な左辺を `AlphaEquivalent` とし、同値を encoder の等号で定義していない。
同じ n の実有限 forward map を列挙し、逆写像を lookup で回収して、最小 code を選ぶ。
任意 n について `permutations_length_le` は候補数が `n^n` 以下であることを証明する。

`alpha_instances_exact` は任意の n/F/G について `AlphaEquivalent F G` を前提とし、任意の固定 rows と target T で、

```text
(∃ parameters, F.instantiate rows parameters ≈ T)
  ↔ (∃ parameters, G.instantiate rows parameters ≈ T)
```

を証明する。一般の再parameter化を許す全 instance 同値からの逆向きを証明した定理ではない。

### 6.3 `CommonCanonicalNames.normalize_exact` / `normalize_first_occurrence_order`

任意 n と二つの Form F/G について、`AlphaEquivalent F G ↔ normalize F = normalize G` が成立する。
任意 n と Form F について、

```text
(used (normalize F)).map Fin.val = List.range (used (normalize F)).length
```

が成立する。`used` は Form を左から読んだ異なる変数の最初の出現列である。
同じ変数の再出現は同じ ID を保持し、未使用 slot から表示名を生まない。
`normalize_idempotent` は任意 F で冪等性、`normalize_instances_exact` は任意 F/固定 rows/target に対する
要求同値な具体化の存在の保存・反映を証明する。

型パラメータの具体化には任意 Common.Ty を許す一方、interface の構文自体は上記の有限文法である。
mixed-head lattice、一般 record/default/mask、複数 tag の行、nominal/role 義務、regular interface、
弱い変数、行の α 同値、slot 数を問わない非単射の消去・共起/併合、異なる slot 数の比較は未完。
参照用の全探索であり、既存 infer/display/export の呼出経路は変更していない。

## 7. 閉じていない補題

以下は未実装契約の名前であり、既存 theorem として引用しない。

### 7.1 `saturate_common_rigid_exact`

任意の実生成 packed clause の共有 graph G と、その rigid 比較列 E について、
有限の symbolic branch 列 `saturate G E` を計算する。任意の独立 rows/values に対し、
G の constructor 方程式の下で E が成立することと、計算した branch のどれかが追加する
child/row/mask/presence 制約が成立することの iff が必要となる。

source の未知 slot の field/optional profile、presence、外側 mask を同じ共有 ID のまま表現する。
具体化した Common.Ty に今回の inspector を呼ぶだけでは、推論時に固定した有限 scheme にならない。

### 7.2 `saturation_closed` と全 parameter soundness

projection、whole default の分解、lower/upper の伝播が追加する状態を、構成した有限 universe に収める必要がある。
すべての実生成 graph について worklist が停止し、終了時に全 rigid 比較が分解済みであることを示す。
この閉性から、求解済み branch の**すべての**行・型 parameter 代入で残比較が成立することを証明する。
成功、closed cache、fuel を公開 principal theorem の前提に置いて代用しない。

### 7.3 `solve_all_instances_exact`

任意の実生成 atom 列 a、任意の独立行割当て rows、任意の compiled node 割当て values について、

```text
(compile a).Models rows values
  ↔ ∃ S ∈ solveAll (compile a), ∃ rowParameters, ∃ valueParameters,
      S.instantiateRows rowParameters = rows
      ∧ ∀ i, S.instantiateValues rowParameters valueParameters i ≈ values i
```

が必要である。さらに任意の返された S と**任意の** parameters が元 Models を与えることも必要。
parameters に `ResidualHolds`、`Models`、support、fuel、solver 成功等の条件を残さない。
現在の graph exactness と source principal theorem は、この欠けた箇所を明示している。

### 7.4 公開入口と決定46

7.3 を実生成 clause の有限和へ接続して初めて、任意の対象閉式 e・任意の結果 c について、

```text
Typing [] e c ↔ ∃ S ∈ Core.infer e, ∃ parameters, S.instantiate parameters ≤ c
```

という残余のない定理、`.rejected ↔ 型付け不能`、対象断片での `.unsupported` 不出現が閉じる。
現時点ではこの統合入口を追加していない。

任意の旧 supported source e と任意の旧結果 target について、旧 instance が新 solved instance になること、
およびその旧結果 target の埋込みに対する新 instance から同じ結果行を持つ要求同値な旧 instance が
回収されることも、この新入口については未完。反映を任意の新 exact/default 型へ無条件に拡大しない。
既存の旧 Typing/実旧 instance から Common の独立 Typing への保存は維持している。

### 7.5 完全な interface 標準形

任意の有限 public interface I/J について、仕様上の等価性 iff 同じ canonical encoding を示すには、
§6 の文法外の構成子と行式、一般の再parameter化、変数の正負位置・共起・弱さ、regular graph、
nominal/role 義務、実 inference/export/display への接続が必要である。
同じ n の型パラメータ全単射による α 同値だけで、全 interface の等価性を定義し直さない。

## 8. 検証

最終統合ゲートは両方成功し、終了コードはともに0。
検証したコードと import/Audit を含む公開 commit は `316e899b6d4fa6793b165335940e2dc3180ca08a`。
この後の更新は README と設計・引継ぎ文書のみである。Lean は既定の4.35.0を使用した。

```sh
cd lean
lake build --wfail
lake env lean --trust=0 Audit.lean
```

build 末尾:

```text
✔ [457/464] Built Yulang.CommonRecordInspection (1.2s)
✔ [458/464] Built Yulang.CommonBoundCoalescing (1.7s)
✔ [459/464] Built Yulang.CommonCanonicalAlpha (1.0s)
✔ [460/464] Built Yulang.CommonCanonicalNames (830ms)
✔ [461/464] Built Yulang.CommonPresenceVariableBounds (1.2s)
✔ [462/464] Built Yulang.CommonPresenceCoalescedSource (676ms)
✔ [463/464] Built Yulang (1.0s)
Build completed successfully (464 jobs).
```

Audit の全 declaration 検査結果:

```text
Axiom allowlist passed for 42161 declarations from Yulang modules
```

Audit 末尾:

```text
'Yulang.CommonPresenceCoalescedSource.Scheme.residuals_rigid' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonPresenceCoalescedSource.clause_parameter_retraction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonPresenceCoalescedSource.clause_instantiation_models' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonPresenceCoalescedSource.residual_source_principal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonPresenceCoalescedSource.residual_core_principal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Audit は公開 theorem の出力だけでなく、import した全 Yulang module の全 declaration を走査し、
許可する依存公理を `propext`、`Classical.choice`、`Quot.sound` に限定する。
新しい公理、`sorry`、`native_decide` は追加していない。
`git diff --check` も成功。今回の追加では既存 theorem の statement、spec、テスト期待値を変更していない。

## 9. 新しい仕様の問い

**追加は0件。** 今回残ったものは共有 symbolic graph の構成・閉性・証明の問題であり、
ユーザーに見える Yulang コードで違いを書ける新しい仕様分岐は見つからなかった。
内部表現の選択肢と採用理由は設計メモへ記し、`notes/questions/` の言語仕様の問いとして増やしていない。
