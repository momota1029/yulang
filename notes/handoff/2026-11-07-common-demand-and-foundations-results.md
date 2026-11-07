# Common 推論の要求駆動計算と B2/B3/B5 の基礎 — 結果と未閉契約

日付: 2026-11-07。対象ブランチ: `integration/m1-common`。

## 1. 結論と作業順

前回 [core-common-coverage-results.md §7](2026-11-07-core-common-coverage-results.md#7-閉じていない補題) の目標を維持して続行した。
**全 B、全旧 source 反映 A1、全公開 interface A2 は未完。** 今回も前提を増やした同名定理で置き換えていない。
元の未閉契約のうち `CommonSignedRows.common_effect_row_interpretation_exact` を閉じた。
nominal head / ground compatibility、実 pattern の Common 環境・lookup・matcher、有限宣言 request 生成の独立部分も証明した。

C は関数定義と定理まで進んだ。任意の同じ有限制約状態での要求 bound が参照計算と一致し、
全検査後の実 scheme 列が `solveAll` と一致する。現 `Core.infer` の principal / 全自由 parameter / rejection もそのまま保つ。
**要求した部分だけを飽和させる scheduler と、関数/SCC の実行前検査は未実装。C2 全体を完了とはしない。**

最初に `origin/yulang3` の `79dac6cff39d576e1cfdf25a5273230838156a34` を取り込み、直後の build / Audit を通した。
通常の fetch refspec が対象 integration branch だけだったため、yulang3 は明示 refspec で更新してから merge した。
途中も同じ手順で取り込みと検証を行った。変更はこの integration branch にだけ公開した。

作業順は B5 の独立基礎、B2 の環境橋、B3 の row 解釈、C を並行とした。
nominal の全 carrier を待たずに環境拡張と signed-row 解釈を閉じられること、C の bound 計算置換が
現在の source 文法と公開 theorem を変更しないことが理由である。B1 の全 list/nominal 生成は B5 の本体が必要なので未着手。
A1/A2 は元の全 statement に対する不足を調べ、狭い別文法の追加を全目標の達成として数えなかった。

## 2. 到達状況

| 項目 | 状態 | 今回の到達 | 次に必要なもの |
| --- | --- | --- | --- |
| B5 nominal invariance / ground cast | 部分 | 任意 Common 値型・行引数の head invariance、共有 slot の有限比較、外側 root の旧順序保存、明示 ground 文法の実 compatibility | nominal を任意 constructor / regular graph の内部へ置く carrier・inspector・solver と保存定理、pure executable plan、construction site |
| B2 pattern environment | 部分 | 単相で順序を保つ環境拡張、Q4 default 生成、optional/default 入力の有限生成、実 lookup と実構造 matcher の型保存 | 実構文からの shared allocator と生成完全性、default の実行・行との橋、presence metadata、全 ordered case |
| B1 list / nominal data / float | 未着手 | 新たな共通 source 生成は追加していない | B5 本体、全 field/site と nil/cons、float carrier の保存拡張 |
| A1 全旧 supported source | 部分（今回は不足の調査） | 既存 iff で元目標と同値となる共通→旧 contextual typing 反映を特定 | 共有 unknown、constructor 方程式、負位置、行、固定旧出力の共同回収 |
| A2 全 finite public interface | 部分（今回は不足の調査） | 既存 canonicalizer の境界と反例を整理 | 全共有 family の計算可能な code、一般行式・regular graph・義務、実 readback/export/EOF/display |
| B3 effect | 部分 | 元 row 解釈契約、任意 row の可逆 transport、有限宣言表と局所型変数を持つ request 一段の生成 | 再帰的 effect source / scheme、全称 handler、visible effect/permission、全 Models を回収する solver |
| B4 role | 部分（停止案の障害を証明） | 実宣言 checker が受理する規則から、要求同値でも再訪しない regular goal 列を構成 | regular head matching と停止手続き、実 evidence/dictionary、associated equations、qualified 全 family |
| C1 | 定義と部分定理 | 現 gate の実 clause / snapshot から根を抽出し、一根の lower/upper を計算 | 後から生じる義務の要求単位の再収集、source/SCC への対応 |
| C2 | 部分 | 同じ snapshot の要求同値、全完了後の solveAll / Core.infer の計算同値 | 局所飽和と実行前検査の end-to-end 定理 |
| C3 | 設計メモまで完了 | 実制約の根、依存変数、将来の六つの実装選択の根、未完境界を記録 | 上記の定義を runtime scheduler へ接続 |

以下の「前提なし」は各記載された型の全入力を量化し、記載外の support / 成功 / closed cache / fuel / 残余条件を要求しないという意味である。
部分文法や独立判断を、全言語の判断に読み替えない。

## 3. B5: 追加した主要定理

詳しい文法・全量化・内部選択は [nominal / ground 設計](../design/2026-11-07-common-nominal-head-ground-foundations.md)。

### 任意 Common 引数と有限比較

`CommonNominalHeads.nominal_head_invariant_exact` は任意 `a b : Head` に対し、前提なしで、
要求受理で定義した `Subtype a b` iff 同じ declaration ID、同じ arity、順序を保った全対応引数の同値を示す。
引数は任意の `Common.Ty` または任意の `Common.Row`。値型の同値は Common 要求同値、行は相互包含である。
`Argument.equivalent_row` は任意二行についてその相互包含 iff 文字どおりの行等号。
`nominal_head_subtype_symmetric` は任意二 head の `Subtype a b` を前提に逆向きを示す。

`CommonNominalConstraints.compile_nominal_comparison_exact` は任意の型 `α`、
任意 `a b : HeadTerm α`、任意 `ρ : α → Comp Common.model` に対し、前提なしで、

```text
(∃ atoms, compile a b = some atoms ∧ PresenceNormalForm.All Common.model ρ atoms)
  ↔ CommonNominalHeads.Subtype (a.eval ρ) (b.eval ρ)
```

を示す。ID / arity / kind の不一致を実際に拒否し、対応引数には既存 type / row inequality を両方向に出す。
任意 assignment の共有を保つが、source generation と全 instance solver はこの theorem に含めない。

### 外側の根の保存

`CommonNominalRoots.common_subtype_exact` と `common_equivalent_exact` は、任意旧 `a b : Common.Ty` に対し、
新しい外側 root への埋込みの順序 / 同値 iff 元の順序 / 同値を示す。追加前提なし。
`nominal_root_invariant_exact` は任意二 nominal head の根に対し、上の ID / arity / 全引数同値と同じ iff。
`common_nominal_exact` は任意旧型 `a` と任意 head `h` に対し、`.common a ≤ .nominal h ↔ a ≤ bottom`。
`nominal_common_exact` は任意 head `h` と任意旧型 `b` に対し、`.nominal h ≤ .common b ↔ top ≤ b`。
`bottom_le` / `le_top` は任意のこの root 型に対する bottom / top の法則である。

これは外側 root の保存である。nominal を arrow/record/regular block の子に入れた carrier や、
その新 model における旧 typing / solver の保存を証明済みとはしない。

### 正規化を実行する ground compatibility

`Scalar` は四つの既存基底型、bottom、top、union、intersection からなる閉有限文法。
`Ground ::= scalar Scalar | nominal Nat (List Scalar)` とする。

`CommonGroundScalarCasts.check_exact` は任意二 `Scalar` について、実 Bool checker が true iff Common subtype。
`scalar_canonical_exact` / `scalar_normalized_quote_exact` は任意二 `Scalar` について、Common 要求同値 iff
計算した canonical code / 正規化後の Casts.Ty quotation が同じことを示す。前提なし。

`CommonGroundNominalCasts.normalized_ground_compatibility_exact` / `normalized_ground_check_exact` は
任意二 `Ground` について、nominal 引数の正規化を実行する `lower` を通した実 `fitsCommonGround` の関係 / Bool と、
正規化前の ground 意味の `CommonNominalRoots.Subtype` が iff になることを示す。外部 compatibility oracle は取らない。
`arguments_normalized_exact` は任意二つの scalar 引数列に対し、全対応引数の意味同値 iff 正規化した code 列の等号。
`Examples.reordered_union_arguments` / `invariant_argument_not_widened` は union の順序同一視と nominal 共変 widening の拒否を kernel で計算する。

対象外は nested nominal、row 引数、nominal を内部に持つ構造型、regular nominal graph、自由型変数。
この adapter を任意の未正規化 Casts.Ty に対する Common solver として使わない。

## 4. B2: 環境・有限生成・実 matcher

全量化した statement と matcher の前提は [pattern 設計](../design/2026-11-07-common-pattern-environment.md)。

### 環境と default 入力

任意の型 `α`、任意 `ρ : α → Comp Common.model`、任意の名前付き共有型参照列 `bindings`、
symbolic 環境 `sΓ` と semantic 環境 `Γ` を取り、唯一の環境前提 `EnvRel Common.model ρ sΓ Γ` を置く。

- `CommonPatternEnvironment.monomorphic_prefix_environment_exact` は、元順序の symbolic prefix と、
  評価した型を `mono (pure type)` にした semantic prefix をそれぞれ先頭へ連結しても、全 index / 全 computation の EnvRel が成り立つことを示す。
- `cumulative_default_generation_exact` は、さらに任意 `fallback : Inference.Expr` と symbolic result `out` に対し、
  この累積 symbolic 環境での実 generate の Holds iff 同じ累積 semantic 環境での独立 Typing を示す。
- `CommonPatternDefaults.default_input_generation_exact` は、同じ任意 `α,ρ,sΓ,Γ` と EnvRel、任意 label / subject type term / fallback / out に対し、
  二つの slot を使う実有限生成 iff 独立 DefaultInputTyping を示す。独立判断は、ある optional payload と fallback computation が存在して、
  optional 観測、fallback Typing、`(payload ∪ fallback.value, fallback.row) ≤ out` が成り立つこと。

`CommonPatternDefaults.optional_constraints_exact` は環境前提なしで、任意 `α,ρ,label,source,payload` に対し、
有限二枝 `top ≤ payload ∧ source ≤ widthRecord` または `source ≤ exactEmpty ∪ required(label,payload)` の Holds iff OptionalPayload。
top payload で必要な depth 0 の width 観測を落とさない。

### 実値の反映

以下の `ValueTyping` は既存の独立 `Core.CommonData.ValueTyping Common.model`、`pure` は空の即時行である。

| theorem（接頭辞 `CommonPatternLookup`） | 全量化と前提・結論 |
| --- | --- |
| `typing_change_result` | 任意 value / source / target。ValueTyping value source と source.value ≤ target.value から ValueTyping value target。target の行は任意 |
| `required_lookup` | 任意 record fields / source / label / payload。record の ValueTyping と source.value ≤ required(label,payload) から、実 first-wins lookup がある値を返し、その値が pure payload に型付く |
| `optional_lookup` | 同じ任意入力と任意 found value。record の ValueTyping、OptionalPayload、実 lookup = some value から、その値が pure payload に型付く |
| `records_of_width` | 任意 value / source。ValueTyping と source.value ≤ widthRecord から、value が実 record であること |
| `pair_components` | 任意 value / source / first / last。ValueTyping と source.value ≤ pair(first,last) から、実二要素とそれぞれの pure first / pure last Typing を回収 |
| `literal_of_base` | 任意 value / source / base。ValueTyping と source.value ≤ base から、実 literal とその同じ基底型を回収。内容を消さない |
| `variant_payload` | 任意 value / source / tag / payload。ValueTyping と source.value ≤ variant(tag,payload) から、同じ実 tag と pure payload の子を回収 |

全 Common subject / payload 型、任意の result rows を許し、record の重複 label も除外しない。
現在の具体値判断は float/list/nominal を含まない。この文法境界を型の任意性と混同しない。

### 実構造 matcher の型保存

`CommonPatternTyping.Typing` は wildcard / bind / literal / intRange / pair / recordEnd / field / defaultField /
single variant / or / as / narrow の独立 Common 規則である。
`Typing.binding_names` は任意の default typing relation、元型環境、pattern、input、bindings とこの導出に対し、
`pattern.names = bindings.map fst` を示す。

`CommonPatternTyping.typing_matches` は任意の型 `D,E,R`、`floatCheck : Empty → Empty → Bool`、
`defaultEval : Bindings Empty → D → Logged E R Value`、独立 `DefaultTyped`、任意の上記 Typing 導出について成り立つ。
前提 `DefaultSound` は、任意の型環境・default code・宣言型と DefaultTyped 導出、さらにその環境に型付く任意の実束縛列に対し、
defaultEval が成功し、その値が宣言型に ValueTyping されるという全称契約である。
この前提の下で、任意の型付いた元実環境と任意の input 型を持つ実 subject を
**既存 `ScopedCasePatterns.run`** で照合した結果は、miss か、宣言した順序と型を持つ束縛列の成功になる。
照合成功を前提にしない。record rest には元 record を渡し、default は先行 bindings を含む累積環境で評価する。

DefaultSound は生成器や effect row から導いたものではなく、一般の型付けだけから全 default の停止・成功を結論しない。全言語の接続では実 return / 許された error / trace 行を扱う部分正当性の判断が必要になる。default の error / 非停止 / trace 行、
source presence annotation、merged variant row、全 pattern の生成完全性と coverage は未完である。
runtime value 集合の等価を Common の型同値と定義上同一視していない。

## 5. B3: signed row と有限 request

### 元の row 解釈契約

[signed row 設計](../design/2026-11-07-common-signed-row-foundations.md) が二 carrier の差を記録する。
`Directed.Row n Nat` は有限 occurrence list、`Common.Row` は任意 occurrence の集合。
`embedRow` は key と全 `n` 座標を保持する実像であり、末尾ゼロを削らない。

`CommonSignedRows.common_effect_row_interpretation_exact` は任意 `n : Nat`、任意 `r s : Directed.Row n Nat`、
任意 `scope : Fin n`、`permission : Nat → Bool`、`handled : List Nat` に対し、前提なしで、

```text
(r ≤signed s ↔ embedRow r ≤Common embedRow s)
∧ embedRow (protect scope permission <$> r) = commonProtect scope.val permission (embedRow r)
∧ embedRow (release scope permission <$> r) = commonRelease scope.val permission (embedRow r)
∧ embedRow (residual handled r) = commonResidual handled (embedRow r)
```

を示す。`rowExpr_interpretation_exact` / `rowExpr_le_exact` は任意 `α,n`、
任意 `α → Directed.Row n Nat`、任意の有限 row 式（一式 / 二式）で、評価の等号 / 包含の iff に拡張する。

`transport_inverse` / `commonRelease_protect` / `commonProtect_release` は任意 `scope : Nat`、permission、
任意 Common row（前者はさらに任意 `delta : Int`）で逆作用の等号を示す。有限性・固定長を仮定しない。
`nonzero_retained` は任意 handled / Common row / 元 member occurrence / その座標に属する非ゼロ整数に対し、
residual 後の membership を示す。負座標も残る。

### 有限 operation 宣言表からの実生成

[request 設計](../design/2026-11-07-common-effect-request-generation.md) に全表現と未検証事項を明記した。
`Declaration α` は有限 local 数、key、extra keys、有限 input/output `TyTerm (α ⊕ Fin locals)` を持つ。

`CommonEffectRequestGeneration.generate_request_exact` は任意 scope 数、ambient index 型 `α`、
symbolic / semantic 環境 `sΓ/Γ`、割当て `ρ` と `EnvRel Common.model ρ sΓ Γ`、
任意有限 declaration、任意 presence payload / symbolic out に対し、実有限 Constraint の Holds iff 独立 RequestTyping。
request は同じ ambient / Γ / out を固定して、local Common 型列と payload row を存在量化する。
同じ local 列を input/output で共有し、payloadRow ∪ ownHead ∪ extraHeads を out.row 以下に要求する。

`generate_declared_request_exact` は同じ任意入力と EnvRel、任意 finite table / operation position で実 lookup を含む iff。
範囲外では両側とも偽で、成功 lookup を前提にしない。
`checked_request_exact` は同じ全量化で、実 kind check と生成の Holds iff
table 全体の wellKinded = true ∧ 独立 DeclaredRequestTyping を示す。
type-local slot の行位置使用を検査する。key coherence / visibility / family 引数 / 全宣言 Valid を検査したとはしない。

payload は現 `Inference.Expr` 全体。入れ子 request/handler や effect scheme は含まない。
`forallTypes` の有限構文はあるが全称 handler の生成はまだない。
任意 assignment の生成 iff は、solved scheme の全自由 parameter 定理の代わりではない。

## 6. B4 の停止案を除外する定理

[role / canonical 境界](../design/2026-11-07-common-role-canonical-boundaries.md) に原契約と不足を記録した。
`CommonRoleRegularObstructions` は内部の pair `F` と variant `G` で、
`R(F(G(G a), b)) requires R(F(a, G b))` という実 `Roles.Impl` を構成する。

- `declaration_sizes` / `declaration_accepted` / `declaration_wellFormed` は前提なしで、head/child の実サイズ 5/4、
  既存 `CheckedRoles.checkImpl = true`、既存 WellFormed を示す。
- `loop_unfold` は一 node / 一 back edge の実 Common regular 型 `A` に対し、前提なしで `A ≈ G A`。
- `chain_step` は任意 `n : Nat` に対し、前提なしで、実 head/child pattern の独立解釈関係において
  `F(A,Gⁿ int)` から `F(A,Gⁿ⁺¹ int)` への instance step があること。
- `chain_equivalent_iff` は任意 `n,m` に対し、二段階の Common 要求同値 iff n=m。
  `chain_fresh` は任意 n と任意のそれ以前の列の member に対し、n 段階と要求同値でないこと。
- `no_natural_descent_measure` は前提なしで、全この regular InstanceStep 上で真に減る `Common.Ty → Nat` が存在しないこと。

単なる有限木 size の差替え、または要求同値まで見る visited goal cache だけで停止を示す案は使えない。
B4 自体の偽や決定不能は示していない。source でこの確定 goal を生成するコードも未確定なので仕様質問にはしていない。

## 7. 閉じていない補題 — 前回 §7 の量化を保持

### 7.1 A1: `legacy_generated_shared_witnesses`

```text
任意 e : Inference.Expr,
  SourcePrincipalInference.supported e = true →
任意 c : old Comp,
  PresenceGeneration.Typing Common.model [] e (Common.embedComp c) →
∃ clause ∈ normalise (principal [] e),
∃ values : Fin (clause.locals + 1) → old Comp,
  values (Fin.last clause.locals) = c ∧
  All Common.model (CommonLegacyTyping.assignment values) clause.pack
```

未完。既存 `embedded_witnesses_iff_typing` により、同じ量化・前提から旧 contextual Typing を回収することが正確な不足。
共有 constructor 方程式・未知の負位置・行・指定出力を一つの旧 regular 割当てで同時に実現する構成がない。
元と同じ clause や全内部 witness の保存までは要求されない。
独立 envelope / 一様 two-sided erasure の既存反例は A1 自体の反例ではない。
詳細は [共有 witness の不足](../design/2026-11-07-common-legacy-shared-witness-gap.md)。

### 7.2 A2: `public_interface_canonical_exact`

任意の全有限 public interface I/J について、既存公開 instance 意味の等価性 iff 計算可能な canonical code 等号。
一般 domain / constructor 結果 / mixed head / record/default/mask / 一般行式と行 parameter /
任意の正負共有と再parameter化 / weak-captured metadata / regular graph / nominal-role 義務を含む元文法のまま未完。
一般化数の一致や全単射を前提にしない。実 scheme readback、export/EOF、display の橋も不足。
既存 scalar / 同深さ curried / 固定行 / 空義務の code と今回の ground adapter は代用にならない。

### 7.3 B1: `common_data_list_exact`

任意の実署名・検証済み list/nominal 宣言、任意元環境・data/nil/cons 式・結果について、
独立共通 Typing iff 実有限生成制約の model。全 field/site、共有 invariant parameter、deferred pure cast を保持し、
全返却 scheme の全自由 parameter 健全性と全モデル回収まで接続する元目標は未着手。
float carrier と共通基底型の意味・旧定理保存も不足。nominal を structural variant として代用しない。

### 7.4 B2: `common_pattern_environment_exact` / `generate_common_case_exact`

前者は、任意の対象 pattern（default 式を含む）、任意元環境、任意 subject 型・実照合値・照合結果束縛に対し、
binder 順序 / 共有 / presence を保つ Common 環境の有限制約 iff 独立 pattern judgment。
Q4 累積環境と単相 binder を維持する元目標のまま未完。
今回実 matcher への型保存は進んだが、実 pattern から型参照列を生成する allocator、
任意独立導出の共有 witness 回収、presence metadata、default の実行結果・失敗・行を扱う橋が足りない。一般の型付けから全 default の停止・成功を導く義務に置き換えず、既存の成功契約付き補題を使える場合と、effect を許す部分正当性の判断を区別する。

後者は、任意 finite arms / subject / guard / body / 結果に対し、first-match / 条件付き default /
guard / 失敗行を含む独立 Common case Typing iff 実有限制約と、その全 Models の任意 parameter solved family 化。
全 ordered case は未着手。nominal/list は B5、effectful default/guard は B3 との接続が残る。

### 7.5 B3: 全有限 effect 生成と全 instance solver

`common_effect_row_interpretation_exact` は今回閉じた。

`generate_common_effect_finite_exact` は任意有限検証済み operation 宣言、関連する新旧環境、
任意式 / 出力 / 割当てについて、独立 Common effect Typing iff 実有限 Formula の充足という元目標のまま未完。
再帰的 effect source / scheme、source 宣言検証、visible effect と permission、handler の
`∃ outer input/result, ∀ local type assignment, ∃ arm result` の有限生成が必要。
外側環境・最終結果を local 型ごとに変えない。shallow continuation は減算前の action row を保つ。

`solve_common_effect_all_instances_exact` は任意の実生成問題と任意独立 rows / 全 node values について、
Models iff 実返却 scheme の無制約 parameters による同じ rows / 要求同値な全 values の回収、
さらに任意返却 scheme・任意 parameters の Models を要求する。未完。
signed transform の循環、全称 handler、残余条件を parameter に残さない求解が不足。

### 7.6 B4: `common_role_registry_exact` / `generate_common_qualified_finite_exact`

任意有限 verified declaration / visible impl 集合と独立 WellFormed、任意型・行が確定した有限 goal description に対し、
実有限 resolver の選択 / 拒否 / 曖昧性 iff 独立 evidence と実 dictionary の対応、という元契約は未完。
全 regular goal への意味を保つ head matching と停止、nested where の同じ visible 集合、associated equation の保存が必要。
今回の無限列の障害を除外するなら、source 生成器の性質として証明する。有限木限定を新前提にしない。

qualified 側も任意検証済み method 宣言・式・結果で method ID / ordinary equations / role goals /
weak-captured-generalized を保つ独立 Typing iff 実有限制約、および全自由 parameter family が不足。
Satisfies を parameter の追加条件にしない。

### 7.7 B5: 全 carrier、pure cast plan、construction sites

`common_nominal_invariant_exact` は任意 ID / arity / 新 carrier の型・行引数での invariance iff と、
旧 Common 順序・typing・solver の保存拡張を要求する。head/root の iff は閉じたが、
任意 constructor 内部と regular graph の nominal、全 inspector / source generation / all-instance solver は未完。

ground compatibility は §3 の明示文法と計算した正規化像で exact。全 regular 型との adapter は未完。
`common_cast_plan_exact_and_pure` は任意有限検証済み cast registry / source / target / 元式 / 環境 / row に対し、
実 keep-search-failure と型付き executable plan を接続し、pure immediate row と変換済み引数で呼ぶ arrow request tree を保つ元契約。
検証済み source body から plan の型・行を導く橋が不足。外部 Plan / CastContract を受け取るだけでは代用しない。

`common_construction_sites_exact` は任意検証済み constructor 宣言と全元 site 式で、固定 field / 共有 invariant parameter /
必要 pure cast / 元順序 / 一度だけの評価を保つ独立 Typing iff finite generation と全 Models の solved family 化。
module/EOF で weak parameter が確定する接続も未完。

## 8. C: 定義・定理・要求の根

[refinement 設計 §10–15](../design/2026-11-07-common-inference-refinement.md#10-今回の決定-遅延するのは計算の時点) に記録した。
現在の入口は旧 14 構成子に literal / strictApp / leaf を加えた 17 構成子と、既存の限定された data / caseE。
Signature.empty の現 gate のままであり、全 32 Core 構成子へ対応を広げていない。

### 固定 snapshot の要求同値

`DemandBoundPropagation.ancestors_exact` は任意 n / Bound / 有限 problem / source-target node に対し、
逆 worklist の訪問 iff 元 flow の source→target 到達。
`lowerBounds_exact` / `upperBounds_exact` / `request_exact` は同じ任意 problem と任意 node / 方向付き根で、
要求した bound 列が参照列と順序・重複まで等しいことを示す。成功・閉性の前提なし。
`lower_exact` / `upper_exact` はさらに任意 `Bound → Common.Ty` の解釈について join/meet 後の型も等しいこと。

`CommonDemandSolver.request_exact` は任意実 pool / edge snapshot / root にこの等号を接続する。
`finished_request_exact` は任意 pool / 初期 edges、実 `finishWorklist` が返した任意 state、任意 root に対し、
その state の要求一致と pending rigid comparison がないことを示す。返却 membership が前提なのは後半の終了性である。

### 全検査後の一致と公開三契約

`CommonDemandSolver.finishWorklist_exact` は任意 pool / 初期 edges で返却 state 列が参照 worklist と等しいこと。
`finishAll_exact` は任意 Compiled graph（origin 不正も含む）で、

```lean
finishAll compiled = CommonBoundRefSolver.solveAll compiled
```

を示す。新関数は旧 solveAll の呼出し別名ではなく、新 bound collector、実 worklist、行検査と scheme 構成を実行する。
`finishAll_rejected_iff` は任意同じ入力で空列判定の一致。
`all_parameter_sound` は任意実 atom 列、任意返却 scheme、任意 row / type parameters で元 Models。前提は返却 membership のみ。

`finishCore_exact` は任意 `e : Core.Required.Term` で `finishCore e = Core.infer e`。
`M := Core.CommonSyntax.model Common.model` とし、任意の同じ e と任意 Common computation c で、

```text
finishCore_principal:
  Core.Typing M [] e c ↔ ∃ S ∈ finishCore e, ∃ p, S.instantiate p ≤ c
finishCore_instantiates:
  任意 S ∈ finishCore e と任意 p に対して Core.Typing M [] e (S.instantiate p)
finishCore_rejected_iff:
  finishCore e = rejected ↔ ¬∃c, Core.Typing M [] e c
```

support / success / closed cache / fuel / 残余条件は前提にない。旧公開 theorem と `Core.PresenceOnly` 以下の statement は変更していない。

### 実装した要求根と、問う変数

| 根 | 問う範囲 |
| --- | --- |
| 実制約の `upper node bound` | node へ flow で到達する全元変数の lower seeds。bound 内部の子・row ID は reference のまま保持 |
| 実制約の固定比較 `check lower upper` | 二つの bound reference。variable-flow 探索は不要だが、constructor 内部の子と行には依存する |
| 元 row 比較 | 両側の有限 RowTerm に現れる row ID 全部 |
| 一変数の upper 問合せ | 根から順方向に flow で到達する変数の upper seeds |

`CommonDemandRoots.upper_variables_exact` は任意 template / root node / query node / bound で訪問 iff flow 到達。
`all_roots_exact` / `snapshot_roots_exact` は任意 template または任意実 pool/edges について、全根への問い合わせ列 = 元 rigidComparisons。
`rowRootVariables_exact` は任意 row 比較と任意二 row assignments に対し、列挙した全 ID で一致するという前提から比較の真偽一致。
`finish_clauses_exact` は任意 Core e で、現 gate が作る実 clause 列の全処理と finishCoreSchemes が等しいこと。

生成元には app/strictApp、branch、pair projection、field、record/default、lambda/let、各 structural constructor、
単一 bind case/leaf がある。branch は今回通らない側も削らない。
corePlans は初期 clause の根を列挙する。inspection で後から生じる子・行義務の要求単位 scheduler はまだない。

### 将来追加する実装選択の六つの根

| 根 | 実行前に確定する範囲 |
| --- | --- |
| method 解決 | receiver 型/行、SCC 最終 snapshot、可視候補、固定 reference |
| role dictionary | goal の全型/行引数、associated equations、根の呼出し側の可視 impl、入れ子 where |
| cast | 境界 source/target、共有 invariant 引数、検証済み registry、元 construction site |
| handler / hygiene | action row、permission、scope/key/符号付き座標、外側 capture、operation-local 全称型 |
| junction | 条件 row とその依存、挿入する handler |
| `xs[i]` | container/index 型、Index dictionary、associated result、error effect |

これらは現在の公開 gate の外を含み、実装済みとして数えない。

### 残る C2 の境界

`CommonDemandBoundary` は実 atoms `[int ≤ α, bool ≤ str]` で、局所 lower が空でない
(`requested_lower_nonempty`) が新旧全 solver は空列 (`completed_solver_rejects` / `reference_solver_rejects`) と kernel 証明する。
`no_completed_node_instance` はこの graph の任意 node / 任意 target に最終 scheme instance がないこと。
したがって未検査の独立矛盾を残した局所情報を、全体の accepted family の node 射影と無条件に同一視しない。

不足は、任意実生成 clause / root に対する後続 rigid 分解・負位置・optional/default・行・選言枝を含む
局所飽和の完全性 `demand_saturation_locality`、完全な依存記録が不変なら再利用結果を保つ cache の定理、
任意の実行関数/SCC の全必要検査を実行前に済ませる `executed_scc_checked_before_run`。
現実装は cache と runtime scheduler を持たず、公開 parameter に条件を加えていない。
性能・起動時間・memory の改善は測定も主張もしていない。

## 9. 検証・公開・質問

最終の `origin/yulang3` の明示 fetch / merge は `Already up to date.`。
対象 commit は冒頭と同じ `79dac6cff39d576e1cfdf25a5273230838156a34`。
直後に次を実行し、どちらも終了コード 0 で通過した。

```sh
cd lean
lake build --wfail
lake env lean --trust=0 Audit.lean
```

```text
Build completed successfully (590 jobs).
Axiom allowlist passed for 49011 declarations from Yulang modules
'Yulang.CommonEffectRequestGeneration.generate_request_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonEffectRequestGeneration.generate_declared_request_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonEffectRequestGeneration.checked_request_exact' depends on axioms: [propext, Quot.sound]
```

各証明の取り込み時にもこの二つの検証を行い、検証済み tree を小さな commit 単位で公開した。
追加の明示 Audit 登録は **85 theorem**。Audit 本体は新規の補助定義を含む全 Yulang 宣言を検査し、
許可依存は従来どおり `propext` / `Classical.choice` / `Quot.sound` の三つだけである。
新しい Lean 行に `sorry` / `admit` / 追加 `axiom` / `native_decide` はない。
旧 `CoreCommonInference` / `CoreCommonSyntax` / `CommonSolvedCoreSyntax` / `CommonSolvedSource` /
`CommonBoundRefSolver` の本体を変更していないことも差分で確認した。

公開した最後の Lean 変更は `f10d53c5a90f1e1b486bc84da08e9954de42b52f`（有限 request 生成）。
その後の commit は設計メモ、README とこの引継ぎの更新である。ブランチの最終 HEAD はこの文書を含む commit で確認できる。
公開中に一度ローカル parent と取得済み remote の同期が遅れたが、未公開の一 commit のみを、
同一 tree を確認して公開済み parent へ接続し直した。公開済み履歴の書換えや別ブランチへの push は行っていない。

新しい `notes/questions/` は **0 件**。E7 と K1 は未決のまま保つ。
今回の不足は内部表現・証明・生成器の接続であり、利用者が書く Yulang コードで異なる選択肢を確定できない問いを追加していない。

次は B2 の実 pattern から有限 constraints を作る共有 allocator と、その生成完全性を優先する。
今回の環境・実値反映・matcher の片方向を再利用でき、B3/B5 全体を待たず構造部分を進められる。
並行して B5 の nominal regular carrier / inspector と、B3 の同一 source 文法を再帰する生成器へ進む。
A1/A2 の全 statement は難所として明記し、部分文法の追加で完了扱いしない。
