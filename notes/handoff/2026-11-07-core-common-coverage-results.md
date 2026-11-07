# M1 の部分言語拡張と共通 Core 入口の統合結果 (2026-11-07)

状態: **A1/A2 と全構文統合は未完。以下の部分言語については kernel 検査済み。**
対象: `integration/m1-common`。作業開始時に `origin/yulang3` の `a7fb60f1e` を merge した。
その直後の `lake build --wfail` は 554 jobs、Audit は 47,115 declarations で通過した。
既存の proof statement を弱めず、意味のまとまった小単位ごとに build/Audit、commit、push を行った。

今回の設計は [共通 Core 構文](../design/2026-11-07-core-common-coverage.md)、
後続の不足契約は [effect / role / nominal](../design/2026-11-07-common-effect-role-nominal-contracts.md)、
速度算法との接点は [refinement メモ](../design/2026-11-07-common-inference-refinement.md) を参照。

## 1. 何が公開入口に載ったか

`Core.infer` の独立判断を `Core.CommonSyntax.model Common.model` へ拡張した。
旧 presence 14 構成子に加えて、次を任意に入れ子にできる。

- `literal`: `Signature.empty` 上の int/str/bool/unit の全内容。
- `data`: literal/pair/有限 record/variant の再帰的な組合せ。
- `strictApp`: function → argument の順に評価し、pure argument value を適用する。
- `caseE`: ちょうど一つの unguarded `.bind name` arm。
- `leaf`: 透明な wrapper。
- `letE`: binder provenance が `some name` の形も含む。

従来の全 presence theorem は `Core.PresenceOnly` 以下に元の statement のまま残した。
public 名の移動だけで旧 presence の事実を消していない。

この入力は今も **`Core.Required.Term = Core.Expr Signature.empty`**。
一般の Float/Op/Key/Scope/Atom carrier を量化した全 Core 推論ではない。
実際の `Core.Expr` は **32 構成子**で、今回の閉じた文法はそのうち 17 構成子と、
`data`/`caseE` の明示した部分である。list/nominal を含む data、他の pattern、
guard、複数 arm、effects、roles、casts、constructions、nil/cons はまだ public 判断の外。

`.rejected` はこの宣言済みの共通判断で結果が存在しないことと同値。
他モデルで型付く式まで「Yulang 全体で型付け不能」としたわけではない。
この分類は `finish` を用いるため `.unsupported` は返さない。

## 2. 公開定理と全 parameter の主張

以下、`M := Core.CommonSyntax.model Common.model`、`Comp := Core.PresenceGeneration.Comp Common.model`。
`≤` は値の Common subtype と行包含の組、`≈` は Common の要求同値を表す。

### `Core.infer_principal` / `Core.infer_instances_exact`

任意の `e : Core.Required.Term`、任意の `c : Comp` について、

```lean
Core.Typing M [] e c ↔
  ∃ S ∈ Core.infer e, ∃ p : S.Parameters, S.instantiate p ≤ c
```

を示す。`infer_instances_exact` は同じ右辺を既存の `Result.Instance c` として読む逆向きの iff。
support、solver 成功、closed cache、fuel、残余条件を前提に置かない。
入口は実際の finite generation/solve/readout を計算し、意味的な命題の別名ではない。

### `Core.infer_instantiates`

任意の `e`、任意の `S : CommonSolvedSource.Scheme`、`S ∈ Core.infer e`、
任意の `p : S.Parameters` について、`Core.Typing M [] e (S.instantiate p)`。
membership 以外の前提はない。parameters は

```lean
(Fin S.rowSlots → Common.Row) × S.solution.Parameters
```

という通常の積で、後半も自由な型・再帰 parameter の関数である。
`Models`、`ResidualHolds`、support、成功証拠の subtype を隠していない。

### `Core.infer_rejected_iff` / `Core.infer_ne_unsupported`

任意の `e : Core.Required.Term` について、

```lean
Core.infer e = .rejected ↔ ¬ ∃ c, Core.Typing M [] e c
Core.infer e ≠ .unsupported
```

を示す。いずれも追加前提なし。ただし `M` は §1 の明示した部分言語である。
`infer_rejected_iff_nil` は同じ任意の `e` で rejected iff 実 scheme 列が空、
`infer_schemes` は実 list への文字どおりの射影等号。

これらの list 層の theorem は `CommonSolvedCoreSyntax.principal`、
`all_parameter_sound`、`empty_iff_untypable`。こちらも同じ全量化・無残余の契約を持つ。

### `Core.infer_embed` / `infer_presence` / `infer_presence_typing_preserved`

- 任意の旧 `e : Inference.Expr` に対して、新 `Core.infer (Core.Required.embed e)` は
  `finish (CommonSolvedSource.inferSource e)` と文字どおり等しい。以前と同じ statement。
- 任意の `e : Core.Required.Term` で `Core.InferenceSyntax.supported e = true` なら、
  `Core.infer e = Core.PresenceOnly.infer e`。これは保存補題の構文条件であり、上の principal の前提ではない。
- 任意の `e,c` と旧 `Core.Typing (PresenceGeneration.CoreRules.model Common.model) [] e c` に対し、
  新 `Core.Typing M [] e c` が成立する。旧型付けから coverage を内部で得る。

list 層の対応は `CommonSolvedCoreSyntax.infer_embed` / `presence_schemes` /
`presence_typing_preserved`。旧 `Core.PresenceOnly.infer_*` の八つの statement と証明は移動前と同じ。
`CommonSolvedLegacyPreservation.legacy_core_parameters` は証明中の rewrite のみ変更した。

## 3. 独立 constructor 規則と lowering の定理

### `Core.CommonSyntax.lowering_exact`

任意の `e : Core.Required.Term` で `covered e = true`、任意の新環境 `Γ`、
任意の旧 presence 環境 `Δ`、`EnvRel Common.model Γ Δ`、任意の `c : Comp` に対し、

```lean
Core.CommonSyntax.Typing Common.model Γ e c ↔
  Core.PresenceGeneration.Typing Common.model Δ (Core.CommonSyntax.lower e) c
```

を示す。`EnvRel` は任意 lexical index と任意 computation に対する binding instance の iff。
captured poly RHS を保ち、computed-let の pure mono binding と行合流も保つ。
補助 `typing_covered` は任意の model / 環境 / 式 / 結果の新 Typing から coverage を得る。
`lower_isValue` は任意の covered term の新旧 value predicate の等号。
`covered_embed` / `lower_embed` / `isValue_embed` は任意の旧式に対する保存。
`covered_case_iff` は任意 subject/arms に対し、coverage が真 iff
arms が単一 bind/guard-none/body で subject/body が covered、という正確な構文特徴付け。

### `Core.CommonData.typing_lower_exact` / `typing_lower_iff`

任意の presence model `m`、任意の structural value `v` で `covered v = true`、
任意の lexical environment `Γ`、任意の `c : Comp m` について、独立 `ValueTyping m v c` iff
`PresenceGeneration.Typing m Γ (valueLower v) c`。
`typing_lower_iff` は任意の `v` に対し、独立 value typing iff
`covered v = true ∧` 同じ lowered typing とし、coverage 前提を結論の側に明示する。
`typing_lowered` / `typing_covered` / `valueLower_isValue` はそれぞれ任意 value typing の lowering、
coverage、および任意 covered value の syntactic value 性を示す。
`literalBase_exact` は任意 `Literal Empty` の legacy base と選んだ base の一致。

### `CommonCoreStrictApplication.forceApplication_typing_exact`

任意の captured presence 環境 `Γ`、任意の旧式 `f,x`、任意の `c : Comp` について、
pair に一度捕捉して両射影を適用する `forceApplication f x` の Typing iff
独立の `StrictTyping Γ f x c`。
後者は、ある `a,b,actual : Comp` と `ef : Common.Row` が存在し、
`f : (a → b,ef)`、`x : actual`、`pure actual.value ≤ a`、
`(b.value, ef ∪ actual.row ∪ b.row) ≤ c` が同時に成り立つという constructor rule。
元の `Γ` の poly bindings の別々の instance を許すが、capture 自体を取り替えない。

`principal` / `all_parameters_typed` / `empty_iff_untypable` は任意の閉 `f,x,c` に対し、
同じ独立 strict judgment を実 `CommonSolvedSource.inferSource (forceApplication f x)` の全自由 family に接続する。
健全性の前提は実 membership だけ。

### `CommonCoreStrictRuntime.eval_forceApplication`

任意の有限 scope 数 `n`、`Key` と `Atom`、**`DecidableEq Key`**、任意の shape 環境 `Γ`、
任意の function/argument shape `a,b`、任意の resolved expression
`function : Expr n Key Atom Γ (.arrow a b)` と `argument : Expr n Key Atom Γ a`、
任意の runtime environment `Env (Tree n Key Atom) Γ` について、
この pair-capture macro の評価は、function を評価し、次に argument を評価し、
pure argument value を function に適用する **request tree 全体**と等しい。
`eval_agrees_with_two_lets` は既存の two-let strict macro との等号。
`source_erasure` / `operational_erasure` は同じ Core constructor pattern への消去等号。
`infer_forceApplication` は同じ `DecidableEq Key` と任意の上記 operands、任意型環境、
任意の input/output/actual computation 型、任意 function row に対し、function の推論結果が
その arrow と row、argument の推論結果が actual、`CLe (CTy.pure actual.value) input` なら、
function/argument/result の全 row を含む同じ最終結果を計算する。
これは resolved checker の補題であり、公開 principal に成功前提を加えるものではない。

### `CommonCoreNamedCase.forceValue_typing_exact` / `lowering_exact`

任意の captured 環境 `Γ`、任意 subject と任意 `c` で、
`fst (subject, unit)` の Typing iff subject の Typing。
さらに任意 body を加えた `caseName subject body` の Typing iff 独立 `NamedCaseTyping Γ subject body c`。
後者はある `a,b : Comp` が存在し、subject が `a`、`mono (pure a.value) :: Γ` で body が `b`、
`(b.value,a.row ∪ b.row) ≤ c` となること。
`forceValue_isValue` は任意 subject について false なので、subject が値でも一般化しない。
`principal` / `all_parameter_sound` / `rejected_iff` は任意の閉 subject/body/result でこの判断と
実 finite solved list を接続する。parameters は無条件。

## 4. A1: constructor 部分言語の共有 witness 回収

`CommonLegacyWitnessPositive.FiniteAgrees` は、任意の有限観測 rank、旧 environment、旧 observation に対し、
元 Common 有限型で埋込み旧 observation が成立 iff 旧有限型で元 observation が成立、という独立関係。
`Agrees` はこれを任意の regular 観測 depth で要求する。

`FiniteAgrees.embedded/exactEmpty/union/inter/pair/variant/record/arrow/upper_reflected` と
regular 版 `Agrees.embedded/base/exactEmpty/union/inter/pair/variant/record/arrow/upper_reflected` を追加した。
union/inter/pair は任意二組の agreement、variant/record は任意 label と子/tail の agreement を前提とする。
arrow は **任意の旧入力型の埋込み**、任意二つの row、output agreement の下で保存する。
`upper_reflected` は任意 source/legacy agreement と任意の旧 target に対し、
Common source ≤ embed target なら旧 legacy ≤ target を導く。未知の負位置を勝手に旧型へ投影しない。

### `CommonLegacyWitnessSource.typing_exact`

`ClosedConstructors e` は lit/emptyRecord/pair/variant/record/branch/lam だけからなる再帰的文法。
var がないので lambda の body は引数を使わない。一般の lambda/application/let/projection/field/default は含まない。

任意の `e : Inference.Expr`、`ClosedConstructors e`、任意の旧 regular 結果 `c`（任意行を含む）で、

```lean
PresenceGeneration.Typing Common.model [] e (Common.embedComp c) ↔
  Inference.Typing contextualModel [] e c
```

を示す。旧 solver の成功は前提にない。
`value_agrees` は任意のこの文法の式から agreement を構成する。
`reconstruct` は任意の新旧環境、任意の Common 結果とその新 Typing に対し、
構文から復元した Common value がその結果以下で、対応する旧 value が旧環境で empty row に型付くことを示す。
旧環境と新環境を関連付ける前提は不要。変数を含まない文法だからである。

### `CommonLegacyWitnessSource.shared_witness_recovery`

任意の `e`、`ClosedConstructors e`、任意旧結果 `c`、
`PresenceGeneration.Typing Common.model [] e (Common.embedComp c)` について、
実 `normalise (principal [] e)` の clause が存在し、**一つの共有旧割当て**
`values : Fin (clause.locals + 1) → old Comp` が存在して、

```lean
values (Fin.last clause.locals) = c ∧
  PresenceNormalForm.All Common.model (CommonLegacyTyping.assignment values) clause.pack
```

を満たす。回収した一つの clause の全 constructor 方程式・比較を一つの旧割当てで満たし、
その出力の旧型と行を `c` に等しく保つ。元の Common 導出が選んだ clause や、
その全内部 row/type witness と同じものを回収する theorem ではない。
独立した node envelope の方程式保存に置き換えていない。

### `CommonLegacyWitnessSource.legacy_instances_reflected`

任意の旧式 `e`、**`ClosedConstructors e`**、旧 `supported e = true`、任意の旧結果 `c` について、

```lean
(Core.infer (Core.Required.embed e)).Instance (Common.embedComp c) →
  ∃ old,
    (SourcePrincipalInference.infer e).Instance Common.rowAlgebra old ∧
    Common.embedOld c.value ≈ Common.embedOld old.value ∧ c.row = old.row
```

を示す。公開名は実際の新入口。target は埋込み旧結果だけであり、任意の新 exact/default 型へ広げない。
**`ClosedConstructors` を除去した依頼 A1 自体は未完**。

## 5. A2: 正負共有を含む閉じた関数部分言語

### 文法と意味

任意の固定型 slot 数 `w`、固定行 slot 数 `r`、共通の argument 数 `k`、
独立した一般化 slot 数 `n,m` を取る。
`CommonCanonicalCurriedTransfer.Scheme w r k n` の各引数は一般化 slot の一つを読み、
同じ slot を複数引数や結果で共有してよい。結果は base/固定 slot/一般化 slot/top/bottom/union/intersection の有限 scalar 式。
各 arrow の incoming/outgoing row は固定の ambient row ID。
obligations は空。`k = 0` も含む。比較する二つの `k` は同じ。

parameters/captured values は任意の Common 型なので、代入する値に regular/mask/default 等の制限はない。
ただし、それらを **scheme の構文として正規化する** theorem ではない。

### `CommonCanonicalCurriedTransfer.instances_spine_exact`

任意の上記 scheme、任意の独立 rows、任意 captured values、任意 required input 型列、
任意 incoming/outgoing row 列、任意 output Common 型について、
その arrow spine が scheme の subsumption 後の instance になる iff
各位置の incoming/outgoing row 包含と、計算した transfer 出力 ≤ output が成立する。
各共有 slot に、その slot を要求する全引数型の有限 union を入れる。使わない slot には bottom を入れる。
`selected_le` は任意の他の admissible parameter への最小性、`transfer_le_output` は同じ全 lower bounds の下の出力比較。
`spine_below_iff` は任意の同深さ二つの arrow spine の subtype を全引数/行/結果比較に完全分解する。
`applyTransfer_eq` は任意 scheme/captured/input で、有限構文置換と上の具体化の等号。

### `CommonCanonicalCurriedFamilies.canonicalEncoding_exact`

任意の `I : Scheme w r k n` と `J : Scheme w r k m` について、

```text
(∀ rows : Fin r → Common.Row,
 ∀ captured : Fin w → Common.Ty,
 ∀ target : Common.Ty,
   (∃ p, instantiate I rows captured p ≤ target)
   ↔ (∃ q, instantiate J rows captured q ≤ target))
↔ canonicalEncoding I = canonicalEncoding J
```

を示す。target は arrow spine に限らず任意。再parameter化候補、全単射、n=m、単一極性は仮定しない。
`family_rows_equal` / `family_transfer_equal` は全 instance family の同値から全行 ID と transfer の同値を回収し、
`familyEquivalent_iff_transfer` はその必要十分性。

一段版 `CommonCanonicalArrowFamilies.familyEquivalent_iff_transfer` / `canonicalEncoding_exact` も同じ性質を持つ。
`Examples.shared_joined_instances` は `∀a. a→a→a` と `∀a b. a→b→(a|b)` の family 同値、
`second_argument_sharing_matters` は前者と `∀a b. a→b→a` の非同値を示す。
各例の全四つの arrow row は同じ一つの固定行 ID を共有する。

### `CommonCanonicalCurriedExports.interface_canonicalEncoding_exact`

任意の `w,r,k,n,m,I,J` について、任意の `RoleConstraints.Theory model`、
任意の ambient computation assignment、任意の target computation に対する
**既存** `(toInterface I).scheme.Holds ...` と `(toInterface J).scheme.Holds ...` の同値 iff 同じ上記 code。
`toSpine_eval` / `toValue_eval` は任意の syntax/環境で実 `TyTerm.eval` との等号。
`binding_instances_exact` / `scheme_instances_exact` は任意 scheme/theory/ambient/target で実 binding/scheme の意味を接続する。
`finishModule_exact` は任意 decoder、有限 impl 列と WellFormed 証拠、任意 partial assignment、任意 closed output に対し、
実 EOF がその output を返す iff 元 support が既知かつ実 `closeAt` がその output に等しい。
一段版 `CommonCanonicalArrowExports` にも同じ公開意味との exact bridge を追加した。
任意 theory を量化するのは、非空 role obligations を解いたという意味ではない。

### `CommonCanonicalCurriedModule.export_canonicalEncoding_exact`

任意 `w,r,k,n,m,I,J`、任意 `decode : model.Ty → Roles.Term`、任意有限 `impls` と `Roles.WellFormed impls` について、

```text
(∀ partialAssignment : (Fin w ⊕ Fin r) → Option (Comp model),
 ∀ callerTheory, ∀ target,
   FinishedInstances I ... partialAssignment callerTheory target
   ↔ FinishedInstances J ... partialAssignment callerTheory target)
↔ exportCanonicalEncoding I = exportCanonicalEncoding J
```

を示す。`FinishedInstances` は実 `QualifiedInference.finishModule` が closed interface を返し、
その実 qualified binding が target を持つ、という既存二操作の合成。
code は `(family code, 元の raw ambient support code)`。partial assignment に known/成功の前提はない。
現在の EOF policy は式に出現した raw support を検査するため、吸収で消える fixed slot も support code では保持する。
`supportCode_exact`、`known_missing_iff`、`known_iff_of_support`、`finished_instances_exact`、
`finished_total_instances_exact`、`finished_top_iff_known` はそれぞれ任意 scheme と明示した任意環境でこの接続を示す。
一段版 `CommonCanonicalArrowModule.export_canonicalEncoding_exact` も同じ全 partial-assignment 契約。
`shared_joined_finished_instances` は上記の異なる arity の例が EOF と公開使用まで一致することを示す。

**全文法の `public_interface_canonical_exact` は未完**。今回の完了は上記の閉部分言語。

## 6. B3 の独立基礎: head 定数付き行 family

入力 `CommonRowHeadFlow.Problem n` は任意の有限 directed flow / pure sink 列と、
有限の `(slot, Common.Occurrence)` 列。独立 `Models problem rows` は flow/pure を満たし、
各指定 occurrence が指定 slot に所属すること。
row parameter は任意の `Fin n → Common.Row` で、無限集合も許す。

### `CommonRowHeadSolver.solve_all_instances_exact`

任意の有限 `n`、任意 `problem : Problem n`、任意独立 `rows : Fin n → Common.Row` に対し、

```lean
Models problem rows ↔
  ∃ S ∈ solve problem, ∃ p : Fin n → Common.Row, S.instantiate p = rows
```

を示す。parameter 条件なし、全 rows の **文字どおりの関数等号**。
`model_retraction` は任意の元 Models に対し、元 rows 自身を p として同じ回収を与える。

### `CommonRowHeadSolver.all_parameters_models` / `rejected_iff`

任意 problem、実返却の任意 scheme、任意 parameters について Models が成立する。
membership 以外の前提はない。
任意 problem について `solve problem = [] ↔ ¬∃rows, Models problem rows`。
`rejected_iff_head_reaches_pure` は任意 problem について、拒否 iff
ある指定 `(source,occurrence)` から flow で到達する target に `.pure target` があること。

`CommonRowHeadFlow.coalesce_models` は内部の有限 check 成功の下で任意 parameter が Models、
`coalesce_retraction` は任意 Models の literal retraction、`no_heads_instantiate` は任意旧 FlatProblem と
任意 parameters で head-empty の新 family が旧 `RowFlowSchemes.coalesce` の具体化と等しいこと。
`check_exact` / `models_check` / `mem_propagated` は有限 check の意味、任意 Models からの成功、
任意 target/occurrence に対する有限 head 列と独立 reachability の iff。
符号付き座標 `[1,-2]` の伝播と、別 slot にある pure sink による拒否も kernel 例で確認した。

これは reference solver の文法拡張であり、高速化ではない。protect/release/residual、
operation-local type の全称、request/handler の generator と公開入口はまだ含めない。

## 7. 閉じていない補題

以下は **未証明の目標**。今回閉じた定理と同名で上書きせず、必要な量化・前提を記す。

### 7.1 A1: 全旧 supported source の shared witness

必要な補題 `legacy_generated_shared_witnesses`:

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

`ClosedConstructors e` を前提に置かない。未知の負位置、共有 slot、constructor 方程式を同時に保つことが不足。
任意 node の envelope は pair 方程式を保たない既存反例があり、代用品にならない。
旧 solver 成功や witness の存在を公開定理の前提に移さない。
これが閉じれば既存の生成翻訳・旧 contextual completeness・今回も維持した `infer_embed` により、
依頼の全 `legacy_instances_reflected`（任意旧 supported e、任意旧 c、同じ結果行）へ接続できる。
任意の新 exact/default target への反映は目標ではない。

### 7.2 A2: 全 finite public interface の canonical exactness

必要な `public_interface_canonical_exact`:

```text
任意の有限な公開 interface I/J について、
  既存の公開 instance 意味における等価性
  ↔ computableCanonicalEncoding I = computableCanonicalEncoding J
```

interface 文法は一般 domain と constructor 結果、mixed head、record/default/mask、一般行式と行 parameter、
任意の正負共起と再parameter化、weak/captured metadata、regular graph、nominal/role obligations を含む必要がある。
同数 parameter の全単射に限定して等価性を定義し直さない。
実 inference scheme の readback、export/EOF、display の同じ意味への接続も不足。
今回の同深さ variable-domain/scalar-result/固定行/空義務の code はこの全 statement の代用ではない。

### 7.3 B1: list / nominal data / float の共通生成

必要な `common_data_list_exact` は、任意の実署名と検証済み list/nominal 宣言、任意の元環境・data/nil/cons 式・結果について、
独立の共通型付け iff 有限生成制約に実モデルがあること。
全 field/site を保持し、同じ list element parameter の invariance と必要な deferred pure cast を同時に保つ。
さらに全返却 scheme の全自由 parameters soundness と元全モデルの回収へ接続する。
nominal 部分を structural variant へ置換しない。Float carrier と Common 基底型の意味の橋も残る。
B5 の nominal/cast 基盤に依存する部分があるため、その独立基盤を先に進められる。

### 7.4 B2: 全 pattern の Common 環境と ordered coverage

必要な `common_pattern_environment_exact` は、任意の対象 pattern（default 式を含む）、任意の元環境、
任意の subject 型・実照合値・照合結果束縛について、元の binder 順序/共有/presence を保った
Common 環境の有限制約と独立 pattern judgment の iff。
default は Q4 の累積環境で型付ける。名前 binder を一般化しない。

必要な `generate_common_case_exact` は、任意の finite arms と任意 subject/guard/body、任意の結果について、
source の first-match 順序・guard・default 評価・失敗行を含む独立 Common case Typing iff 実有限制約。
その全 Models を任意 parameter の solved list に変換し、§2 の公開三契約へ接続する。
今回の単一 bind arm では coverage が自明だが、全 pattern の代用ではない。
structural pattern の環境橋は B3〜B5 全体を待たず進められる。nominal/list pattern は B5、
effectful default/guard は B3 の意味との接続が要る。

### 7.5 B3: effect の有限宣言・signed row・全称 handler

必要な `common_effect_row_interpretation_exact` は、任意有限 scope 数、任意の実 signed rows で、
包含を保存・反映し、protect/release/residual と可換となる実 Common 行解釈。
任意 Common rows に対する solver family と、実 scope vector の有限表現の差を明示する。

必要な `generate_common_effect_finite_exact` は、任意の有限検証済み operation 宣言、任意の関連する新旧環境、
任意の式・出力・割当てについて、独立 Common effect Typing iff 実有限 Formula の充足。
任意関数 contract や Typing 自体を atom にしない。
handler は **∃ outer input/result, ∀ operation-local type assignment, ∃ arm result** の量化順を保つ。
外側の捕捉環境や結果を local type ごとに取り替えない。

必要な `solve_common_effect_all_instances_exact` は任意のその実生成問題・任意独立 rows と全 node values について、
元 Models iff 実返却 scheme と無制約 parameters が同じ rows/要求同値な全 values を回収すること。
任意実返却 scheme と任意 parameters の Models も必要。universal 検査を parameter の条件に残さない。
今回閉じた head+flow+pure family はこのうち定数と方向付き包含の部分だけ。

### 7.6 B4: finite role registry と実 dictionary

必要な `common_role_registry_exact` は任意の有限 verified declaration/visible impl 集合と独立した WellFormed 条件、
任意の型・行が確定した**有限 goal description**に対し、実 finite resolver の選択/拒否/曖昧性 iff
その goal の解釈について既存の evidence と実 dictionary が対応すること。
未確定 goal は次の有限 qualified constraints で扱い、その意味で任意 Common 代入を量化する。
行葉が任意の述語である Common semantic 型を直接受ける Bool resolver を仮定しない。
regular graph の有限表現に対する停止も別途必要で、旧 first-order tree の size 証明だけでは不足する。
recursive where 解決にも同じ visible 集合を使い、associated equations を保つ。
任意 `Theory : Goal → Prop` や任意 decoder だけでは実 solver の契約にならない。

必要な `generate_common_qualified_finite_exact` と全 parameter family は、任意検証済み method 宣言と式・結果について、
method ID、ordinary equations、role goals、weak/captured/generalized の区別を保持し、
独立 Common qualified Typing と実有限制約を両方向につなぐ。
残る `Satisfies` を自由 parameters の前提へ押し込めない。
use-site dictionary/evidence の公開形式と実解決を接続する。既存の `CommonFinite.Demand.role` は
head 観測であり、impl dictionary の解決 theorem ではない。

### 7.7 B5: nominal invariance / ground cast / construction sites

必要な `common_nominal_invariant_exact` は任意の nominal IDs/arity/型引数に対して、
同 nominal の比較 iff IDs と arity が一致し、全対応引数が要求同値であること。
旧 Common の順序・typing・solver は保存拡張する。

必要な `common_ground_cast_compatibility_exact` は明示した有限 ground 文法・正規化像の全 source/target について、
実際に構成した cast compatibility iff 新 Common subtype。任意の外部 compatibility oracle では代用しない。
既存 `Casts.Compatibility.nominalInvariant` は引数の raw syntax equality を使うため、任意の
未正規化 `Casts.Ty` の equality を Common 要求同値と同一視しない。
全 regular 型には意味的 invariance の別 layer と、旧 ground theorem を保存する adapter が必要。
`common_cast_plan_exact_and_pure` は任意の有限検証済み cast registry・source/target・元式・環境・row に対し、
keep/search/failure の実計算と型付き executable plan を接続し、pure immediate row と
arrow wrapper の入力変換後の request tree を保つ。

`common_construction_sites_exact` は任意の検証済み constructor 宣言と元 site 式群について、
全 site/固定 field/共有 invariant parameter/pure cast 制約の有限生成 iff 独立共通 Typing。
元位置と記述順を保ち、各 site を一度だけ評価し、その全 Models を solved family に接続する。
元 site を型のない `.free` ID にする既存 plan embedding だけでは不足。
nil/cons の統合はこの基礎に依存する。nominal carrier と ground cast 検索は B2 全体を待たず進められる。

### 7.8 B6 と全構文の署名

`strictApp` と `leaf` は今回の範囲で完了。
`free` は未束縛名なので closed judgment に任意型を割り当てない。
一般の `Atom` と actual operation/float/scope carrier を持つ `Core.Expr s` 全体について、
有限検証済み署名を入力とする生成・全 parameter solver・公開三契約がなお必要。
`Signature.empty.Atom` が空であることを、一般 atom の統合完了としない。

## 8. 段階の到達状況と次の入口

| 段階 | 到達 | 今回閉じたもの | 次 |
| --- | --- | --- | --- |
| A1 | 部分 | closed constructor grammar の同じ行を持つ旧 instance 回収 | §7.1 の共有負位置 witness |
| A2 | 部分 | 同深さ curried family、実公開 instance、partial EOF の完全 code | 一般 domain / constructor 結果 / 行文法への閉部分言語拡張 |
| B1 | 部分 | literal と structural data の public principal / 全 parameter / rejection | float と B5 に依存する nil/cons/nominal data |
| B2 | 部分 | 単一 unguarded bind case の同じ公開三契約 | **次の source 統合は structural pattern の Common 環境橋から** |
| B3 | 部分 | head+flow+pure row の全 instance / 全 parameter / rejection | signed row operations と有限 operation 宣言の generator |
| B4 | 未着手 | 接点の調査と不足契約の設計のみ | finite registry / Common dictionary bridge |
| B5 | 未着手 | 接点の調査と不足契約の設計のみ | nominal invariant carrier と ground cast bridge（B1 list の依存先） |
| B6 | 部分 | strictApp / leaf 公開統合、free / atom の分類 | 一般署名と atom 意味の接続 |

全 B1〜B6 の完了を宣言しない。A1/A2 の未証明 statement も部分定理で置き換えない。

## 9. 検証

新しい主要 theorem は `Audit.lean` に登録した。全追加モジュールを `Yulang.lean` から import する。
各 proof 単位の commit 前に全体 `lake build --wfail` と `lake env lean --trust=0 Audit.lean` を通した。
`sorry`、追加の公理、`native_decide` は使っていない。

最新のコード checkpoint は remote `8ec8b89acfd8cdced203e88e6293c867669bfa88`。
この checkpoint の全体検査:

```text
✔ [571/572] Built Yulang (625ms)
Build completed successfully (572 jobs).

Axiom allowlist passed for 47937 declarations from Yulang modules
'Yulang.CommonCanonicalCurriedModule.export_canonicalEncoding_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonCanonicalCurriedModule.Examples.shared_joined_finished_instances' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

後続の README・設計・引継ぎ変更後にも同じ全体検査を行い、両コマンドが終了コード 0 で通過した。
再検査も `Build completed successfully (572 jobs).` と
`Axiom allowlist passed for 47937 declarations from Yulang modules`。
追加 Lean 行の `sorry` / `sorryAx` / `native_decide` / `axiom` 検索も 0 件。
`origin/yulang3` は途中でも fetch し、`a7fb60f1e` からの追加がないことを確認した。
`integration/types` と `yulang3` には push していない。

## 10. 新しい問いと速度メモ

新しい `notes/questions/` は **0 件**。
今回の内部 compiler/lemma の選択で未決の言語挙動を決めていない。
E7/K1 はそれが必要になる実 source 統合まで未決のまま。

速度の設計メモ:
[`notes/design/2026-11-07-common-inference-refinement.md`](../design/2026-11-07-common-inference-refinement.md)。
bound 集合の共有と型変数の同一視を区別し、将来の Lean 関数を実参照 solver の全 instance refinement として証明する道筋を記す。
高速化の実装・証明・性能主張は今回行っていない。
