# Yulang3 型推論の形式化

このディレクトリは [`spec/10-inference-core.md`](../spec/10-inference-core.md) の核を Lean で検証する。古い型推論器や proof sprint は復元せず、現行仕様に対応する定義と定理を置く。

Lean は `lean-toolchain` の **4.35.0** に固定する。依存は Lean/Std のみで、Mathlib や外部 solver は使わない。

```sh
cd lean
lake build --wfail
lake env lean --trust=0 Audit.lean
```

## Core (M0)

[`統合計画の M0`](../notes/design/2026-11-06-integrated-inference-plan.md) に対応する。
`Core.Expr` は型・shape 添字を持たない共有構文で、全ローカル参照は de Bruijn 添字である。
operation/key/scope・float 内容・opaque atom の carrier は `Core.Signature` で指定する。
未束縛名は `free`、旧 named let の名前は復元用の hint として保持する。
ordered case の guard/default、単一/複数/部分 handler、nominal 構築 site、内容つき literal、
method 要求、cast site を表現する。旧 computation-argument の `app` と `strictApp` は区別し、
Multi の `.core` は `StrictApplication.compile` を経由する。

`Core.Typing model` はモデルの独立な構成子判断であり、旧型付けの存在で定義した関係ではない。
required-field と presence の carrier・判断は別に保持する（M1 の境界）。
下表の同値は任意の旧式・環境・結果について成立し、推論成功・solver 解・fuel は前提にしない。
定理名の接頭辞は `Yulang.Core` である。

| 接続・定理 | 示したこと | 示さないこと |
| --- | --- | --- |
| `Required.conservative` | 任意の model、捕捉された poly/signature を含む環境、式、computation について旧 `Inference.Typing` ⇔ Core 判断 | required-field への `recordDefault` 規則追加 |
| `Effects.conservative` | 任意の model・row view・署名・環境・式・computation について旧 `RecursiveEffects.Typing` ⇔ Core 判断 | 他断片との混合、operation-local 多相の統合 |
| `Qualified.conservative` | 任意の model・method table・role theory・環境・式・computation について旧判断 ⇔ Core 判断 | method lookup・辞書 elaboration の統合 |
| `Presence.conservative` | 任意の data 型環境・式・意味的結果型について旧判断 ⇔ Core 判断。strict な `recordDefault` を含む | required-field/regular 型との同一視 |
| `Data.conservative` | 任意の名前付き型環境を名前列と型列に分け、旧 `CaseDataTerms.Typing` ⇔ de Bruijn 化した Core 判断。shadowing・未束縛構文も量化の対象 | source の名前解決 pass の証明 |
| `Case.conservative` | 任意の `CaseTree.Expr`・環境・結果型について旧判断 ⇔ Core 判断。arm 順・guard・default・通常/variant coverage を保持 | scoped default への旧 CaseTree の意味変更、effect/cast を含む case 推論 |
| `Scoped.conservative` | 任意の環境・入力型・束縛型列について、具体 data default を持つ旧 scoped pattern 判断 ⇔ Core default で具体化した同じ汎用判断 | この module は pattern AST。全 source の pattern elaboration は含まない |
| `Resolved.operational_core` / `multi_core` | 任意の shape 環境・注釈付き式・結果 computation 型について、旧型付け ⇒ 同じ環境/結果型での Core 消去式の型付け | 両 AST とも同じ元の式への逆向きは不成立。lambda/handler/widen の注釈を消し、Core の subsumption も許す。`annotation_erasure_typed` / `annotated_not_pure`（Multi は `multi_` 接頭辞）で両方の反例を証明 |
| `Construction.conservative` | 任意の parameter 数・compatibility・registry・期待型・construction・plan について旧 `PlanTyping` ⇔ Core site の planner 判断。site 順・元型・parameter 割当てを保持 | 旧 module は式 AST を持たない。site の実式の推論/実行、nominal 値型の推論ではない |
| `Literal.conservative` / `matches_conservative` | 任意の float carrier・literal・kind について kind 分類と Core 判断が一致。任意の float 比較関係の下で matching も双方向に保持 | 旧 module は式型付けを持たない。Kind を言語全体の主型とすることや marker literal との統合ではない |
| `Block.definition_conservative` / `scc_conservative` / `generate_exact` | SCC は式の外。宣言 head と Core body を分離し、任意の旧環境・slot 割当て・宣言列で全 body 検査が同値。実際の同時再帰環境と旧 `generateSCC` の充足にも接続（後者は `EnvRel` 前提）。全注釈の局所値型変数も全称量化 | SCC 発見・求解・closure・一般化の統合、effect/case body の SCC 推論（M3） |
| `required_principal_exact` / `effects_principal_exact` / `qualified_principal_exact` | 既存の `EnvRel`（effect は `SigRel` も）の下で、任意の結果 computation について旧 principal scheme の充足 ⇔ 対応する Core 型付け | 混合 Core 全体の新しい scheme/solver ではない |

M1 の共通 presence 判断に対する実 `Core.infer`、主型性・拒否完全性・対象断片の unsupported 不出現は下記の定理で閉じた。
effects/qualified/case/nominal を含む全断片の相互作用を、この入口で推論する主張ではない。
`cast` は site の構文のみで、統一した挿入/型付け規則は M4 に残す。
literal の内容・presence・nominal の planner 結果を一つの値型 carrier に統合したとは主張しない。
`Core.Expr.isValue` は旧 required/effect 判断用の構文検査であり、新構成子の値制限を決めない。

### M1: 型モデルの接続（部分完了）

`CommonFinite` / `CommonSyntax` / `Common` に、solver や型判断に依存しない具体的な
finite/regular presence carrier を追加した。exactEmpty、whole default、mask、関数と両行を
同じ構文に持つ。要求環境は任意の有限型または regular 型を名前で参照し、負位置でも同じ
環境を使う。型の順序と、strict な runtime data の読取りは分離する。
内部表現と代案は [共通モデルの設計](../notes/design/2026-11-07-m1-common-model.md) に記す。
定理の量化・前提と未完の補題、検証結果は [初回の実装結果](../notes/handoff/2026-11-07-m1-common-results.md) と
[復旧後の実装結果](../notes/handoff/2026-11-07-m1-common-recovery-results.md) と
[有限飽和・公開入口の実装結果](../notes/handoff/2026-11-07-m1-common-saturation-results.md) と
[全自由 scheme・共有 witness・標準形の統合結果](../notes/handoff/2026-11-07-m1-symbolic-results.md) にまとめる。

復旧記録 §7 の現在の残りは次の通りである。下の歴史的な部品定理の表で「示さないこと」と
記す項目は、その定理単独の範囲であり、後続の統合定理で閉じたものを含む。

| 復旧記録の契約 | 現在の証明 | 残り |
| --- | --- | --- |
| 7.1 symbolic rigid 分解 | source/Core の全実生成 clause、独立 rows/values、同じ共有 ID で exact | この契約は完了 |
| 7.2 有限飽和・全 parameter soundness | optional 境界を含む実 worklist の停止・全 rigid 分解と、返却 scheme の任意行・型 parameter による全 Models | この契約は完了。分岐数・総実行時間の多項式上限は主張しない |
| 7.3 全 instance exactness | 全実生成 clause の任意独立 rows/values を、行の等号と全 compiled node の要求同値で回収 | この契約は完了。任意の手書き atom 列には別途明示した構文条件が必要 |
| 7.4 公開入口・決定46 | 残余のない `Core.infer` の主型性、対象断片の拒否 iff / unsupported 不出現、旧 instance ⇒ 新 solved instance | 任意の旧 supported source と埋込み旧結果に対する、新 instance から同じ行の要求同値な旧 instance への反映 |
| 7.5 全 public interface 標準形 | 既存有限 constructor 文法、有限 scalar 型族の任意 arity を許す完全 code | 一般構成子・行式・正負の共有・弱さ・regular graph・nominal/role 義務をまとめた完全 encoding と inference/export/display 接続 |

| 共通 carrier の定理 | 示したこと | 示さないこと |
| --- | --- | --- |
| `Common.common_subtype_exact` / `common_arrow_iff` / `common_pair_iff` / `common_variant_iff` | 任意の共通 regular 型について、順序は全深さ・全 rank・任意の具体型環境・union-free 要求の受理の反転包含。任意の arrow 引数/結果（mask/default/regular block・自由 parameter の代入を含む）を4成分へ完全分解する。具体行の前順序・反対称性も証明 | 全 presence constructor の完全 inspector、全 source の solved infer |
| `CommonFiniteEmbedding.contextual_embedding_exact_at` / `contextual_embedding_exact` | 任意の行関係、旧有限型 S,T、任意 rank で、新環境の型を制限せず旧 contextual 比較との iff。新しい exact/default/mask 型を要求変数に割り当てても成立 | この有限定理単体での regular embedding や source 保守性 |
| `Common.contextual_embedding_exact` / `contextual_equivalence_exact` | 任意の旧 regular 型 S,T を新共通 carrier へ埋め込むと、全深さ・全 rank・全環境の新順序／同値が旧 contextual 順序／同値と一致する。旧 graph の有限観測を文字通り保存する | 新 presence solver の instance に対する旧入口の保存・反映 |
| `CommonSyntax.block_observe_exact` | 任意の有限 block・外部型・全深さで、共有参照を閉じた graph が元の観測と等しい。tail/default source/mask は同深さ、payload は一段下。default の初期 payload も一段下にそろえる | 任意の同深さ tail 循環をこの block 文法へ解消する compiler |
| `Common.exactEmpty_data_exact` / `width_data_exact` / `default_data_image` / `default_inhabited_iff` | 同じ common 構文上の独立 data 読取りで、exact empty と width を意味的に区別し、任意 source/fallback/result に対して whole default が既存 insertDefault の正確な strict image。present でも fallback を消さない | data 包含を producer 順序にすること、要求同値の data 集合への因数分解、関数 runtime の安全性 |
| `CommonFinite.mask_parameter` / `mask_composition` / `mask_required` | 任意の具体有限型・全 rank/環境/要求で独立 mask 解釈と一致し、外側 mask の合成は label の和。隠れた required head は width へ移り、payload の mask と外側 mask は区別される | 二つの既存 solver family の全入力接続 |
| `Common.common_mask_parameter` / `common_mask_composition` / `common_mask_required` | 同じ mask 法則を任意の共通 regular 型と任意の finite/regular 要求環境へ拡張する | record/default の未知 tail を含む全 compiler |
| `Common.exactEmpty_below_width` / `width_not_below_exactEmpty` | exact empty は width 以下であり、逆は成立しない。構文の不一致だけでなく要求意味でも識別する | runtime 集合包含と producer 順序の一致 |
| `Common.default_guarantees_field` / `default_exactEmpty` / `default_present_record` / `common_default_mono` | 任意の label・source・fallback で source が width 以下なら default は required label top 以下。source が exactEmpty の場合は record 構築へ、同名 head を持つ source は自身へ要求同値。全 source/fallback の比較で単調。payload/mask/regular graph を制限しない | 任意 target 比較の有限完全 inspector、present で strict fallback を実行しなくてよいという runtime 法則 |
| `Common.common_record_iff` / `common_singleton_requirement_iff` / `common_shadowed_head_equivalent` | 任意の同名 record 比較は payload 比較と同じ深さの残りの field／非自明 optional 要求へ完全分解する。required target の場合、tail へ同名 field の要求を戻さない。同名の内側 head は要求同値で消せる | tail を whole `Subtype` で比較すること、strict な field 式の評価省略 |
| `Common.common_mask_mono` / `common_mask_type_congr` / `common_equivalent_iff_masked` | 任意の共通型で mask は単調かつ合同。通常の要求同値と、全外側 mask 後の要求同値が一致し、自由 parameter に追加の mask 安定性条件を課さない | この法則だけによる全 source compiler |
| `CommonTailElimination.common_solved_instances_exact` | 任意の有限 positive 同深さ graph（ref/union/inter/mask、任意 Common 型の atom）と任意の独立割当てで、方程式成立 ⇔ ある制約なし Common 型 parameter から計算した解と各 slot が要求同値。成功・fuel・closed を前提にしない | 任意の subtype 不等式や whole-default source 方程式の完全 compiler |
| `CommonRecordTailElimination.compile_models_exact` / `solve_models` / `solved_instances_exact` | 上の graph に実際の record 構築を追加し、任意 payload と同深さ tail 循環を実 polynomial へ完全変換する。任意 parameter は解を与え、任意の独立解も回収する | payload 自体の未知 constructor 方程式、default source の未知参照、全 source principal theorem |
| `CommonPresenceTailElimination.solve_models` / `solve_retract` / `solved_instances_exact` | 任意の有限 graph の実 record/default/mask 方程式を解く。未知参照は同深さ tail と whole-default source に置け、循環も自由。payload/fallback は固定された任意 Common 型。Models ⇔ ある制約なし Common parameter の解と各 slot が要求同値で、どの parameter 割当てもモデルを与える。深さ・rank・外側 mask・観測をすべて量化し、内部反復数は有限座標から導出 | 同じ未知 graph の guarded payload/fallback/arrow 子への参照、任意の型不等式や全 source compiler |
| `CommonPresenceTailLayers.solveLayers_quote` / `solveLayers_map` / `solveLayers_evalAt` | 任意 payload index 型・有限 symbolic graph・Layer parameter・payload 割当て・深さで、実四 mode 反復と引用／rename／有限評価が文字通り可換。guarded 子と同深さ ref は別の参照種として共有 ID を保つ | この構文変換だけによる不等式の完全 inspector |
| `CommonPresenceTailRegular.solveBlock_models` / `solveBlock_retract` / `guarded_solved_instances_exact` | 任意の有限 graph・独立 Common 型割当てで、元の方程式 Models ⇔ ある制約なし parameter から計算した regular block の全 slot が要求同値。同じ未知 slot を guarded payload／fallback／負の arrow 子と同深さ record/default/mask tail の両方へ代入する。任意外部 state も許し、どの parameter もモデルを与える。成功・fuel・Closed を前提にしない | 任意 subtype 不等式からこの graph への完全 compiler、全 source の生成制約の求解 |
| `CommonRowTailInference.joint_instances_exact` / `solve_models` / `solve_retract` | 宣言した有限構文の任意入力・任意の独立行／値割当てで、Models ⇔ ある制約なし行・値 parameter の具体化が元の行と等しく、値が要求同値。別途、どの parameter 割当てもモデルを与える。行の右辺は構文上 var/empty、左辺は任意 join。record/default source の同深さ循環と、同じ slot の guarded payload/fallback/負の arrow 子を含む。symbolic layer 内の両 arrow 行は同じ row ID を共有し、無制約行も自由のまま | 任意の型不等式からこの構文への compiler、inspector が追加する全行辺の source support、全 source の生成入力がこの構文へ完全変換されること |
| `CommonPresenceInspection.common_inspect_exact` / `default_inspect_at_exact` | 任意の共通型・環境・深さ・rank・一つの観測について、実有限 DNF inspector が proper child 観測／負引数比較／行比較／role membership のみへ保存・反映する。default source を再帰展開し元の whole-default 比較を atom に残さない | 任意 target の全観測を一つの有限な subtype branch へ落とす `default_inspect_exact`、atom の全求解 |
| `CommonDefaultRequired.default_required_iff` / `inspect_required_exact` / `default_record_iff` | 任意 label/source/fallback/payload と任意 tail で、required／同名 record target に対する default 比較を、深さを一段ずらす optional-payload 条件と（有限な presence 判定または fallback≤payload）と残りの RecordTailLe へ完全分解する。required 版は実2 branch。source shape・成功前提は不要 | 任意 target への完全 inspector、未知 source slot の optional/presence 条件を制約なし family へ解消する compiler |
| `CommonDefaultBoundary.presence_does_not_erase_default` | 任意 label で、source が width 以下かつ required label top 以下でも、whole default を source へ要求同値で置換できない具体反例。optional payload の制約も残す必要がある | 正常な構文上の present head に対する `default_present_record` の否定 |
| `PresenceNormalForm.presence_normalise_exact` / `principal_clauses_exact` / `Clause.pack_exact` | 任意 model・実 presence Formula・自由割当てで、Holds ⇔ 計算した有限 clause の一つと局所 computation 割当ての存在。値と行を同じ slot として保持し、捕捉環境の EnvRel の下で全 source の独立 Typing と一致 | 原子制約の解消、局所割当てに条件を残さない全自由 parameter family |
| `PresenceNormalForm.closed_core_exact` / `closed_source_exact` | 任意 model・閉じた Core/source 式・任意結果について、型判断 ⇔ finite packed clause と全原子制約を満たす割当て。support checker・推論成功・fuel 前提は不要 | solved infer の principal/rejected/unsupported theorem。右辺の原子制約は未求解 |
| `PresenceSourceConstraintSupport.generated_row_shapes` / `generated_explicit_rows_supported` / `generated_explicit_rows_models_exact` | record/default を含む全 source の実生成式の全 clause で、明示 row atom を実 RowFlowSchemes solver が扱える。任意行代数・任意独立行解に対し、自由 parameter scheme から相互包含で回収する | 新しい全 target 型 inspector が後から追加する行辺まで含む simultaneous support |
| `CommonPresenceInspectionRows.inspect_preserves_rows` / `inspected_rows_supported` | 任意の行述語を満たす outer arrow 行と観測側の行から、inspector が生成する行 atom の両端も同じ述語を満たす。元の行が var/empty なら実 RowFlowSchemes.supported が true。mask/record/default の再帰も含む | 全 target の型比較を有限 branch へ変換する未実装手続きの行保存 |
| `CommonLegacyTyping.formula_preserved` / `presence_typing_preserved` / `legacy_core_instances_preserved` | 具体旧モデルの任意 Formula と割当ての充足を、実 witness と同じ行を保って Common へ移す。任意の閉じた旧 Typing は独立 Common presence Typing に保存される。旧 infer 版は任意の旧 supported 式・任意旧結果・その旧 instance を前提に Core.Typing を得る。Compatible は具体的に証明し呼出側へ要求しない | 新 Core.infer の instance、反映、同じ行での旧 instance 回収 |
| `CommonSyntax.Layer.evalAt_congr` / `evalAt_masked_probe_iff` | 任意の行前順序・payload index 型・深さ・Layer・二つの payload 割当てについて、各 payload が全 rank の有限要求同値なら Layer の評価も同値。負の arrow、default の深さ0、任意外側 mask を含む。上記 block retraction の深さ帰納で使用 | 片方向の payload 単調性、全 target inspector |

復旧後、outer default の完全分解と、実生成 clause から行・構成子方程式の消去を追加した。
上表の「示さないこと」は各定理単独の範囲であり、任意 target の outer inspector は次の追加定理で閉じた。
全 source の残る subtype edge は、後述の `CommonBoundRefSolved` と `Core.infer` で制約なしの自由 family へ接続した。

| 復旧後の定理 | 示したこと | 示さないこと |
| --- | --- | --- |
| `CommonPayloadProjection.optional_type_exact` / `field_type_exact` / `optional_payload_exact` | 任意 source、外側 mask、label、深さ、rank、有限要求環境で、正の深さの field/optional を一段下の実子型の有限格子式へ完全に射影する。参照する regular/負の arrow 子を制限しない。optional の深さ付き義務を通常の子 subtype へ消去 | 未知 source slot の射影を共有 symbolic solver に取り込む定理 |
| `CommonRecordEnvelope.envelope_below_iff` / `CommonRecordTailProfiles.tail_profiles_exact` / `CommonRecordTailFinite.tail_finite_exact` | 任意 Common target の head 制約を実 Bool で判定し、任意 source/target/hidden の同深さ tail 比較を初期 Bool と正の子比較へ変換する。outer の有限 label 表と fresh label 一つで全 label を尽くす | 子比較の再帰的飽和と全入力の求解 |
| `CommonDefaultInspection.default_inspect_exact` | 任意 label/source/fallback/target で、whole default の subtype ⇔ 実有限 inspector が返す branch の子比較がすべて成立。最終 atom は `Common.Ty × Common.Ty` の比較だけで、元の whole-default、OptionalPayload、RecordTailLe、Formula を残さない。任意 regular/mask/mixed head を含む | 固定した推論 scheme の自由 parameter 全体に対する symbolic 分解、全 source solver の停止性・完全性 |
| `CommonRecordInspection.record_inspect_exact` / `required_inspect_exact` | 任意 label/payload/rest/target で、通常 record または required の subtype ⇔ 有限 inspector の子比較がすべて成立。head の要求を取り除いた残りの tail を調べ、任意の mask/default/regular 子を許す | 未知 source slot の shape 分岐と子比較の全求解 |
| `CommonBoundCoalescing.rigid_comparisons_exact` / `expand_satisfies` / `expand_retraction` / `all_instances_exact` | 任意の有限 lower/flow/upper/check 問題と固定した境界型で、変数辺を有限な境界型間比較へ消去する。残る固定比較が成立すれば全 Common 型 parameter が解を与え、任意の独立解を全 slot で要求同値に回収する。循環を許す | 未知 constructor 子に境界型が依存するときの比較の求解、全 source の自由 family |
| `CommonPresenceVariableBounds.eliminate_variable_edges_exact` / `compiled_joint_elimination_exact` / `residuals_rigid` | 任意の実 source pool/edge と行割当てで、変数辺を同じ ID の共有方程式へ置き換えて regular solver で閉じる。行右辺が var/empty の実 atom 列では明示行制約も消去。元モデル ⇔ 行が等しく全値が要求同値な具体化が存在し、残る有限な rigid-rigid 比較が成立。比較の両端が元 pool の非変数 node であることも証明 | 境界型は未知 graph node を読むため、残る比較は parameter に依存する。その symbolic 分解・飽和と制約なし source family |
| `CommonPresenceConstraintGraph.compile_atoms_exact` / `realizes_evaluate` | 任意の実 packed presence atom 列・独立 computation 割当てで、元制約 ⇔ 実共有 graph のモデルと元 slot の等号 readback。任意の意味的 realizer から全 subterm の評価を要求同値で回収。record/default/負の arrow 子と元行 ID を保存 | 比較 edge の消去、全自由 solved family |
| `CommonPresenceClauseFamily.family_instantiates` / `family_retracts` / `eliminate_definitions_exact` | 行右辺が構文上 var/empty の任意 atom 列で、任意自由 parameter が定義方程式・明示行制約を満たす。任意元モデルを、同じ行と要求同値な全値で回収。source の全生成 clause はこの行文法を満たす | 残る subtype edge の任意 parameter での充足 |
| `CommonPresenceSourceFamily.residual_source_principal` / `residual_core_principal` | 任意閉式・任意結果について、独立 Typing ⇔ 実 normalize/pack/graph/行・方程式 solver が返す有限 scheme と row/value parameter があり、明示された residual edge を満たし、その出力が結果以下。support・成功・fuel の公開前提はない | residual を除いた公開 `Core.infer`、拒否 iff、対象断片の unsupported 不出現 |
| `CommonPresenceCoalescedSource.residual_source_principal` / `residual_core_principal` | 上の任意閉式・任意結果の iff を実変数辺消去まで接続。row/type/recursive の3 parameter family を実同時 solver に代入し、残る条件は元 pool の非変数 node 間比較だけ。clause 回収は結果値の要求同値と結果行の等号を保ち、GoodAtoms は生成不変量から内部で供給 | rigid 比較の symbolic saturation と、残余を除いた公開 `Core.infer`・拒否完全性・unsupported 不出現 |

続いて、復旧記録 §7.1 の **代入前に固定する symbolic rigid 分解**を source/Core の両方で閉じた。
§7.2 の有限飽和と全 parameter soundness、§7.3 の全解回収も、実生成 clause について閉じた。
§7.4 のうち、presence モデルの実 `Core.infer`、残余のない principal theorem、拒否 iff、
unsupported 不出現まで接続した。旧 supported source 全体への決定46の反映と、§7.5 の完全な
public interface 標準形は残る。以下の局所定理と、その後の統合定理を区別する。

| Symbolic compiler の定理 | 示したこと | 示さないこと |
| --- | --- | --- |
| `CommonGeneratedRigidInspection.saturate_common_rigid_exact` / `saturate_common_core_rigid_exact` | 任意の実生成 packed clause、独立 rows/values に対し、元 constructor 方程式の下で rigid 比較列が成立する iff 推論時に計算した有限 branch の一つの child/row/profile/presence 制約が成立。生成・束縛・上下限伝播から構文条件を内部で証明し、元共有 ID を保持。compiler は型代入・solver 成功・fuel を受け取らない | この first pass 単独では全 parameter 求解を含まない。拡張した全飽和と求解は下記 `CommonBoundRefSolved` で完了 |
| `CommonGeneratedRigidDescent.residual_omits_original` / `residual_child_decreases` / `residual_profile_decreases` | 任意有限 pool/edge の実 rigid 残余について、元比較を同じ child 比較に包み直さない。返却 branch の全 child 比較は元共有参照を使い、由来の比較より構文 weight 和が厳密に減る。profile target も proper child | 同深さ tail 循環や変数上下限伝播を含む全体の減少性 |
| `PresenceGeneratedChildGrammar.generated_child_grammar` / `CommonGeneratedChildClosure.generated_reinspection_grammar` | 全 source/Core の生成・scheme 置換・binder packing を通し、子位置の再帰的文法を証明。負の arrow 引数を逆向きに比較し、子辺を追加して再 coalesce しても文法が保存される。変数へ代入する Common 型は任意 | 新しい optional 境界を加えた文法の閉性 |
| `CommonOrdinaryEdgeClosure.ordinary_edge_closure_closed` / `ordinary_edge_closure_bound` / `generated_closure_exact` | 元 pool の N² 個の比較候補を構成し、変数上下限伝播と child 辺追加を、非停止 round ごとの厳密な辺数増加で有限固定点まで計算。全生成 clause の元方程式の下で元辺と閉包辺の充足が同値。公開 fuel/closed 前提なし | row/profile/presence の解消、閉包から任意 recursive parameter の全比較成立を導くこと |
| `CommonSymbolicRecordProfiles.compile_exact` / `CommonSymbolicSourceProfiles.compileNode_exact` | 任意の独立 row/node/child 割当てで、固定した symbolic 式の七項目の意味が元構文と一致。実 pool と全 regular realizer へ接続し、未知 field/optional/presence、初期層、外側 mask を別々に保持 | projection を元 node と無関係な自由 parameter にすること |
| `CommonGeneratedProfileSupport.saturate_support` / `universe_length_le` | 任意 pool/edge と任意の first-pass 返却 branch の全型参照は、代入前に構成する高々 8N(N+1) 個の表に入る。label、mask、guarded child の元 ID を保存 | この表は first pass の支持。optional query を含む全 worklist は下記の有限 BoundRef inventory で閉じた |
| `CommonSymbolicProfileCoherence.compileNode_reconstruction` / `independent_projection_not_sound` | 任意の独立 table が有限支持上で一つの元 values と一致するなら七項目の意味を回収。coherence を落とすと scalar が required を満たす偽解になる反例も証明 | coherence 自体を全自由 parameter で構成する solver |
| `CommonGeneratedRigidRows.generated_rows_supported` / `CommonSymbolicRowConstraints.row_definitions_all_parameters` / `row_definitions_instances_exact` | 全実生成 branch の arrow 行を既存行 solver へ接続。元行と追加行、任意の共有 constructor 方程式を同時に解き、すべての行・型 parameter がこの部分のモデルを与える。任意の独立解を行の等号・全 node の要求同値で回収 | branch の child/profile/presence 条件も全 parameter で成立すること |
| `CommonSymbolicTailView.symbolic_tail_exact` | 任意 H/S/T と任意 slot 割当てで、同深さ tail 比較 iff 二つの異なる record head を持つ有限 `TyTerm` view の通常比較。入力にない未知 label も保存し、rename/subst と可換 | view の再展開を進行と数えた tail 循環の解消 |
| `CommonTopTest.top_iff` / `CommonOptionalBound.optional_payload_branches_exact` / `narrow_instances_exact` | 任意 Common 型の top 同値を有限 outer 構文で判定。任意 label/source/payload の optional 義務を、top/width と exactEmpty-required union への通常比較の二枝へ完全変換。単独 optional 義務には制約なし parameter family と全解回収を構成 | その境界を未知共有 graph 全体へ伝播する完全 solver、元 unmasked 型の独立 masked 値からの回収 |
| `CommonDefaultBounds.default_required_branches_exact` | 任意 label/source/fallback/payload で、whole default の required 比較 iff 通常の型比較だけからなる固定三枝。shape/presence 前提なし、元 source/payload を共有し、深さ0を保持 | 新しい union 形の optional 上界の有限飽和と最終公開入口 |
| `CommonOptionalGraphExtension.exists_extension_exact` / `CommonOptionalPool.exists_extension_exact` / `CommonOptionalPoolQueries.extended_size_bound` | 任意共有 graph/pool と任意有限 query 列の constructor model を optional 境界用 node へ正確に拡張・制限。実 Pool 版は元 ID の数値を保持し、実生成 query の在庫は元 N node に対して高々 5N+3 node | 拡張 pool の全比較を処理する分岐 worklist の閉性 |
| `CommonSameDepthUpperObstruction.solver_recovers_counterexample` | 任意の異なる label a/b と任意 payload P/Q に対し、同 depth の独立方程式の現 solver 解に、元方程式を満たすが上限 required b Q を破る値がある | その独立 graph が実 source の完全な生成 clause であるとの主張 |
| `CommonPresenceClampedBounds.solve_realizes` / `all_parameters_below_bound` / `all_parameters_along_path` / `solve_retract` | 変数右辺全体を propagated upper で clamp する新 variant。任意 parameter で元 constructor 方程式、全 propagated upper、全 variable-flow path を満たす。元方程式と全辺を満たす任意モデルを全 node の要求同値まで回収 | 下限・rigid 比較の無条件な全 parameter 成立 |
| `CommonClampedClosureSoundness.conditional_soundness` / `solve_sound_of_nonChild` | 任意 pool/edges の recursive endpoint grammar・ordinary closure・clamped graph model・row/profile/flag 条件の下で全辺が成立。rigid 比較の成立を前提にせず、有限観測 depth と source weight で帰納 | non-child 条件の消去、optional 上界の追加後にも成り立つ拡張版 |
| `PresenceGeneratedWidth.generated_width_atoms` / `CommonGeneratedWidth.generated_pool_width` / `CommonGeneratedBoundWidth.optional_exact_of_poolWidth` | 全実生成 record/default の tail/source に同一 clause の width atom が付随することを、全生成・置換・packing で保存。元 model から局所 width を得て、固定 optional inspector の意味と元 node の比較を接続 | この定理単独で、全辺 model を仮定せず任意 solver parameter から width を導くこと |
| `CommonSymbolicBoundInspection.inspect_required_exact` / `inspect_optional_exact` / `CommonGeneratedBoundInspection.inspect_exact` | required/default/optional の固定分岐を、元共有参照・有限 required/optional 境界・行比較・literal flag だけへ変換。optional には明示した局所 width が必要。profile と動的 Bool を出力しない | 新境界を含む全 worklist と同深さ tail の全 parameter soundness |
| `CommonGeneratedBoundSupport.inspect_supported` / `optional_query_supported` | 任意元 pool の通常 target と選択済み optional query の全分岐は、同じ有限 query inventory 内の bound reference だけを使う。型代入・model・endpoint shape・成功を前提にしない | 追加 pool 全体の再 inspection と全 worklist の閉包 |
| `CommonGeneratedClampedWidth.generated_all_parameters_pool_width` / `generated_core_all_parameters_pool_width` | 任意実生成 clause と、元 rigid 分解で静的に残った任意 branch について、任意 rows/type/recursive parameters の clamped solve は全 record tail/default source の width を満たす。branch.Holds・全辺 model・solver 成功を前提にしない | 追加 pool への transport と他の全 branch 条件の同時消去 |
| `CommonOptionalPoolWidth.pool_width_iff` / `CommonOptionalPoolClampedWidth.generated_all_parameters_pool_width` | 任意 query 列・任意 extended values で拡張前後の PoolWidth が同値。任意実生成 clause の width seed を保つ任意拡張 edge 列に対し、width target の静的失敗がなければ、全 extended parameter で PoolWidth が成立 | width の静的条件も内部で供給する実 worklist 接続 |
| `CommonOptionalBoundEncoding.encodeOutput_exact` / `CommonBoundRefCoalescing.rigid_encode` | 任意支持された symbolic branch を実拡張 pool の ID に変換し、任意 constructor realizer で意味を保存・反映。変数分類、lower/upper 伝播、rigid 比較列は符号化と literal equality で可換。元 node ID の数値を保持 | 拡張した全比較の全 parameter soundness |
| `FiniteBranchingWorklist.run_closed` / `run_bound` / `run_models_exact_selected` | 任意有限 universe と支持された inspector/rigid discovery の分岐 worklist が、各枝で universe 長以下の処理により停止。最後の各 rigid 比較の選択 branch と全追加制約を保持。独立な解釈と明示的な分解 exactness の下でモデルを保存・反映 | この汎用定理だけで実生成の拡張文法・分解 exactness を供給すること、閉包から無条件の全自由解を得ること |
| `CommonFiniteOptionalInspection.default_branches_at_sound` / `CommonFiniteBoundInspection.required_at_sound` / `optional_at_sound` | 任意 depth/rows/values と実返却 branch に対し、有限観測の子比較から親比較を導く。`BranchAtSource` は全 child の guarded 比較と、non-rigid source では全 child の同深さ比較も前提とする。局所 default 三分岐では payload/fallback と tail の深さを分ける。soundness 方向には PoolWidth を仮定しない | 全 worklist の source 減少と、clamped 任意 parameter への統合 |
| `CommonBoundRefInspection.inspect_supported_refs` / `inspect_polarity` / `inspect_exact` | 元 lower/top source と、元 upper・有限 required/optional query target を同じ inventory で反復分解。全返却 child の向きの文法を保存し、任意 Realizes/PoolWidth で元 subtype と同値。literal false と width→required/optional の失敗枝を静的に除去 | worklist 全体から全自由 parameter family への統合 |
| `CommonBoundInspectionDescent.node_current_sources_smaller` / `CommonClampedSelectedSoundness.conditional_soundness` | 元非変数 node の同深さ child source が proper child/top/width として厳密に小さくなることを証明。任意 finite selection の ordinary/childClosed/currentDecreases と実有限 inspection、clamped model、row/literal 条件の下で全辺を導く | その selection と全補助条件を実 worklist から内部構成すること |

#### 有限飽和から公開入口まで

`CommonBoundRefWorklist` は、元 node と選択済み required/optional 境界を同じ有限 inventory に収める。
未知 slot への代入後に inspector を作り直さず、元の共有 ID と row ID を保持する。
N は元 pool の node 数であり、`(5N+3)²` は**一つの branch の処理 trace**の上限である。
全分岐数、返却 scheme 数、全実行時間の多項式上限ではない。

| 統合定理 | 示したこと | 示さないこと |
| --- | --- | --- |
| `CommonBoundRefWorklist.run_finished` / `run_closed` / `run_bound` / `run_grammar` | 任意 pool・初期辺で実有限 worklist が停止し、返した任意 state の未処理 rigid 比較がなく、処理履歴は重複せず inventory 内。初期辺が生成文法なら新しい child/required/optional 辺も同じ文法に入る | 任意の手書き型文法の分解 exactness、全 alternatives の多項式個数 |
| `CommonBoundRefWorklist.generated_run_models_exact` / `generated_core_run_models_exact` | 任意の source/Core 式の任意生成 clause、任意独立 rows/values について、元 constructor Realizes の下で、元型比較列の成立 iff 実 run のいずれかの全辺・補助制約が成立。生成 grammar/width を内部で供給 | この部品単独での元明示行制約の求解、任意自由 parameter の soundness |
| `CommonBoundRefClosedSoundness.returned_solve_soundness` | 任意実 run の返却 state で、記録した分解から child closure・有限観測・source weight 減少を内部構成し、補助 row/literal 条件の下で clamped solver の全比較を導く | この部品単独での補助 row 条件の消去。次の統合定理が消去する |
| `CommonBoundRefSolved.saturation_closed` | 任意 atom 列とその実 run が返した任意 state で、未処理比較なし・全 rigid 比較の Closed・processed の重複なし・trace と processed の同長・trace 長 ≤ `(5N+3)²`。caller の成功・closed cache・fuel 前提なし | 任意手書き atom 列の completeness、総実行時間の上限 |
| `CommonBoundRefSolved.all_parameters_models` | 任意 atom 列、`solveAll` が返した任意 scheme、任意独立行 parameters と任意型/recursive parameters で、元 `compile` の全 constructor 方程式・行制約・型比較を満たす。parameter の型は通常の関数の組であり `ResidualHolds`/`Models`/support/成功証拠を含まない | 手書き atom 列で scheme が必ず存在すること |
| `CommonBoundRefSolved.solve_all_instances_exact` / `model_is_instance` | child/width/row の三つの明示した構文条件を満たす任意 atom 列と任意独立 rows/全 node values で、Models ⇔ 返却 scheme と任意型の parameters が存在し、行が文字どおり等しく全元 node が要求同値 | 三つの構文条件を満たさない手書き atom 列の completeness |
| `CommonBoundRefSolved.generated_solve_all_instances_exact` / `generated_core_solve_all_instances_exact` | 任意 source/Core 式、任意実生成 clause、任意独立 rows/全 compiled values について、上記 iff を三つの構文前提なしに証明。生成 membership から必要条件を内部供給し、全元 ID の値と同じ行を回収 | 対象の source/Core generator の外にある言語機能の推論 |
| `CommonBoundRefAllParameters.saturation_closed` / `generated_all_parameters_models` / `generated_core_all_parameters_models` | 任意の実生成 clause、任意の返却 state、任意の行・型・再帰 parameter について、同時 row/clamped family が元 graph の constructor 方程式・全比較辺・全行制約を満たす。閉性・有限 inspector・row/literal 条件を内部供給。型 parameter は mask/regular を含む任意 Common.Ty | 全 public interface の標準化、一般の手書き atom 列に対する完全性 |
| `CommonBoundRefSolver.all_parameter_sound` / `generated_models_exact` / `generated_core_models_exact` | 実計算 `solveAll (compile atoms)` の各返却 scheme と任意 parameter は元 Models を与える（健全性には atom 文法の前提も不要）。任意の実生成 clause と独立 rows/values では、元 Models iff ある返却 scheme の自由具体化が同じ rows と全元 node の要求同値を回収する。scheme は有限構文と元 ID の readout、parameter は普通の積だけを持つ | 任意に手作りした Compiled と無関係な origin metadata の組に対する保証、一般 atom 文法の全解回収 |
| `CommonPresenceSolvedSource.source_principal` / `core_principal` / `source_all_parameters` | 任意閉 source/Core 式 e・任意結果 c で、独立 Typing ⇔ 実 clause 列と `solveAll` から計算した有限 scheme の instance が c 以下。返却任意 scheme の任意 parameters も独立 Typing を与える。残余条件なし | 旧入口からの反映、表示/export の標準形 |
| `CommonSolvedSource.source_principal` / `core_principal` / `source_instantiates` / `core_instantiates` | 公開経路の任意閉 source/Core 式・任意結果で同じ残余なしの iff。任意返却 scheme の任意行・型 parameters が独立 Typing を与え、実生成 clause の任意モデルから同じ出力行と要求同値な出力値を回収 | parser からの全 source elaboration、旧 instance の一般反映、export/display の完全標準形 |
| `Core.infer_principal` / `infer_instances_exact` / `infer_instantiates` | 任意 `Core.Required.Term` e・任意 Common computation c に対し、共通 presence の独立 `Core.Typing [] e c` ⇔ `∃ S ∈ Core.infer e, ∃ parameters, S.instantiate parameters ≤ c`。任意返却 scheme・任意 parameters についても型付く。`Core.infer` は有限生成/求解の実計算 | effects/qualified/case/nominal を混ぜた全 Core 判断への拡張、`Formula.Holds` による入口の別名化 |
| `Core.infer_rejected_iff` / `infer_ne_unsupported` | 任意 `Core.Required.Term` e について rejected ⇔ 共通 presence 判断で型付く結果が存在せず、unsupported は返らない。support・成功・fuel の前提なし。対象構文外ではこの判断に規則がないため rejected となる | 他の effect/qualified/case モデルについての型付け不能との同一視 |
| `CommonSolvedLegacyPreservation.legacy_core_parameters` / `legacy_instances_preserved` | 任意旧 supported source e・任意旧 computation c・その実旧 infer instance について、新 `Core.infer` が返した scheme と無制約 parameters が存在し、具体化の値は旧値の埋込みと要求同値、結果行は文字どおり c の行と等しい | 新 instance から同じ行の要求同値な旧 instance を回収する逆向き |
| `CommonLegacyReflection.fixed_bounds_models_exact` / `fixed_bounds_output_exact` | 任意有限 slot 数、任意の旧 regular 境界型、任意の共有 flow を含む固定上下限制約について、任意 Common witness の存在 ⇔ 旧型 witness の存在。任意の埋込み旧出力 target への比較も保つ。exact/default/mask を含む元 witness を制限しない | 未知子を読む constructor 方程式の保存。この補間は実 infer のアルゴリズムではない |
| `CommonLegacyEmptyReflection.exact_empty_upper_old_iff` / `empty_record_typing_exact` / `empty_record_legacy_instances_reflected` | 任意旧 regular target に対する exact empty の上限比較は旧 width の上限比較と一致。任意旧結果・任意行で空 record の新型付けを旧 contextual 型付けへ反映し、同じ結果行の要求同値な旧 instance を回収 | exactEmpty と width の一般同値、任意 source の共有 existential witness の回収 |
| `CommonLegacyReflection.arrow_upper_reflected` / `arrow_lower_reflected` / `envelope_does_not_preserve_pair_equation` | 任意 Common 子・旧型境界・四つの行で、上側 arrow 比較は旧出力 test、下側は旧入力 test の所属から反映。他の下限には所属不要。独立 node ごとの envelope が pair 方程式を保たない反例も証明 | この局所補間だけで相互再帰 constructor 方程式全体を保つこと、決定46自体の否定 |
| `CommonLegacyGenerationTranslation.legacy_generated_clause_exact` | 任意旧 supported source の任意実生成 presence clause を実際の旧 generator の clause へ変換し、locals/共有 ID/row term/pack を保持。任意共有旧割当てで新 atom と旧 contextual atom の充足が同値。変換成功は内部で証明 | 任意 Common witness から旧共有 witness を選ぶこと |
| `CommonLegacyEmbeddedWitnesses.embedded_witnesses_iff_typing` / `contextual_typing_preserved` | 任意 required-only source・任意旧結果で、実生成 presence clause と出力がその旧結果に等しい共有旧割当ての存在 iff 旧 contextual Typing。旧 contextual Typing の Common への保存も証明。旧 solver support は不要 | 任意 Common witness からこの旧割当ての存在を導く反映 |

この `Core.infer` の型判断は `PresenceGeneration.CoreRules.model Common.model` である。
対象の record 構築・whole recordDefault・lambda/application・束縛を同じ carrier で扱う。
他の Core モデルをこの presence モデルと同一視せず、従来の入口と定理は変更していない。
`Compiled.origin` は元の有限 pool/edge/row 構文を保持する metadata であり、`Models` の意味には使わない。
`solveAll` はこの構文から有限 inventory を構成し、具体化した型を inspector に渡して分岐を選ばない。
並行して検証した `CommonBoundRefSolved` / `CommonPresenceSolvedSource` の経路も保持し、
構文外を unsupported とする別入口は `Core.SyntaxGatedCommonInference.infer` として区別する。
公開の `Core.infer` は `CommonBoundRefSolver` / `CommonSolvedSource` の経路を使う。

回答済み Q5 に対応する新しい具体要求モデルを `ProducerContextual` / `ProducerContextualRegular` に追加した。
型変数は任意の意味型が満たすすべての観測を表し、arrow の引数要求も同じ環境の型を名前で参照する。
要求の構文に union はない。role は許可された constructor head の有限表で観測し、
`int | str` と `any` を区別する。辞書や条件付き impl の全意味はこの head 観測には含めない。
全 constructor depth・負文脈 rank・環境・要求を量化し、solver の fuel や有限サンプルは用いない。

| 新モデルの定理 | 示したこと | 示さないこと |
| --- | --- | --- |
| `ProducerContextual.producerLe_refl` / `producerLe_trans` / `structural_subtype_preserved` と regular 版 | 任意の行関係で前順序。行の推移律の下で任意の旧構造部分型を保存する。role の保存則を公理として仮定しない | subtyping の完全な checker、条件付き role の全解釈 |
| `ProducerContextual.pair_union_group` / `record_union_group` / `variant_union` と regular 版 | 任意の行関係と全成分で同じ constructor の union をまとめる要求同値。pair/variant は成分比較への完全分解、record は単調性と合同性も示す | 異なる tag の tag row、exact/default の意味、全表示標準形の一意性 |
| `ProducerContextual.producerLe_arrow_iff` / `ProducerContextualRegular.producerLe_arrow_reference_iff` / `producerLe_arrow_iff` | 任意の有限型、任意の graph と state、引用した任意の regular 型について、行が前順序なら arrow 比較 ⇔ 引数反変・入力行反変・結果共変・出力行共変の4条件。closed `Negative` 制限・分離の仮定・成功・fuel は不要 | carrier の producer 構文自体には var/mask constructor がなく、要求側の変数/mask と任意の代入後の型を扱う。新 presence signature の自由 parameter/mask family をこの carrier へ評価する接続 |
| `ProducerContextual.Examples.mixed_union_not_equivalent_top` / regular 版 / `mixed_arrow_not_equivalent_top_arrow` | 任意の行関係で int/str だけを許可する具体 role 要求が混合 union と top を分離し、任意引数の arrow 文脈でもこの区別を保持 | 条件付き impl・辞書探索の意味との一致 |
| `Core.ProducerContextualInstances.legacy_instances_preserved` / `legacy_instances_reflected` / `legacy_instances_exact_modulo` | 任意の行代数・実際の旧 `Result`・結果値と行で、同じ scheme の直接評価による新 instance は旧 instance を保存し、同じ結果行を持つ要求同値な旧 instance へ反映する | presence の新 solver family との同一視 |
| `Core.ProducerContextualInstances.source_instances_exact_modulo` / `source_instances_sound` | 任意の行代数・行反対称性・旧 supported 式・結果で、新 instance ⇔ ある要求同値な旧値型と同じ行での旧 `Typing`。新 instance から新 concrete model の独立 `Typing` も得る。逆向きは下の `ContextualRequiredInference` で接続 | recordDefault を含む presence の新入口 |
| `ProducerContextualNormalForm.merge_equivalent` / `normalize_equivalent` / `normalize_accept_iff` / `normalize_not_complete` | 既存の実 grouping pass が新 contextual 順序でも全要求を保存・反映。全有限型の normalize は行の前順序を仮定し、負位置・role・要求変数・mask を含む。同値な `int \| str` と `str \| int` が異なる出力になる具体反例も証明 | 完全な interface 標準形。この pass の結果の不一致から型の非同値を判定すること |
| `ProducerContextualRecord.producerLe_record_iff` / `fieldLe_record_iff` / `Regular.record_reference_iff` / `Regular.record_iff` | 任意の行関係・任意の同一 label の record について、比較 ⇔ payload の比較と、その label を除く tail の field 観測の比較。relative mask の下では head が隠れていると payload 比較も不要。任意の graph・引用した regular 型の全深さにも成立し、tail の深さを減らさない | whole tail の `ProducerLe` に置換すること、非guardedな node tail と presence 全体の新 carrier |
| `ProducerContextualRecord.singleton_requirement_iff` / `Regular.singleton_requirement_iff` / `shadowed_head_equivalent` と regular 版 | 任意の同一 label の singleton required target では payload 比較だけが残り、tail への field 要求は空。同名の内側 head は任意の payload/tail で消しても要求同値 | hidden field 式の評価を省くこと、exact empty への `{}` の読み替え |

要求側の `Demand.mask` は隠す label の field 観測を record-kind 観測に写す。
上記 arrow iff はその全要求を含むが、これを producer の concrete mask family の構成とは数えない。
regular graph の payload は既存 `Layer` の guarded 参照であり、同深さの tail 循環は下の別の核で扱う。
旧 `{}` は任意の record の上界のままである。

新しい順序を、実際の `NestedValueSolver` と `TypeConstraintInference` に接続した。
graph の文法は変数・base・bottom/top・pair・行を持つ arrow・有限の proper record spine・variant。
この表の全入力とはこの宣言済み文法のすべての入力であり、presence の exact/optional/default/mask node
を黙って同じ graph に含めてはいない。行関係には反射律・推移律を、実行する行検査には意味との iff を使う。

| 定理 | 示したこと | 示さないこと |
| --- | --- | --- |
| `ContextualConstructorInspection.inspect_sound` / `ContextualNestedModels.inspect_sound` | 任意の実 rigid node・任意の独立 contextual 割当てで、constructor 比較から実 inspector が生成する全子制約・行制約を導く。regular 版は任意の graph の全深さを扱う | optional/exact/default の inspector、旧 all-mask presence cache の反例の解消 |
| `ContextualNestedModels.saturate_models_iff` / `solve_none_iff` | 任意の有限 graph・入力辺列で、実飽和の前後は同じ任意 regular model を持ち、実 solve の拒否 ⇔ contextual model が存在しない。成功・解・Closed・fuel は前提でない | 同深さの presence tail/mask node を含む不等式 solver |
| `ContextualNestedModels.solve_instantiates_model` / `solve_closed_capacity` | 任意の実受理結果について、任意の外部 regular graph と自由 parameter layer からの実 coalescer が入力のモデルを与える。受理結果から constructor/variable `Closed`・整合性・cache 長 ≤ slot数² を得る | presence 全体の Closed。全 contextual 解の retraction は下の `ContextualCoalescing` で別途接続 |
| `ContextualBranchSolver.solve_models_exact` / `accepted_closed_capacity` / `solve_nil_iff` | 任意の graph・truth/falsity/edge/論理積/論理和の有限式で実分岐列挙と飽和を実行し、任意の独立モデル ⇔ ある実受理枝の cache のモデル。各枝から Closed と slot数² 上界を得て、空結果 ⇔ モデル不存在。成功・解・fuel 不要 | presence signature からこの分岐文法への lowering、枝数の多項式上界 |
| `ContextualTypeConstraintGraph.compile_assignment_exact` / `compile_output_instances_exact` | 行の前順序の下で、任意の実 compiler 返却 graph・任意の元共有変数割当てを保持し、元型制約の充足／上方出力 instance と同じ具体 regular carrier 上の contextual graph model が同値 | compiler の既存構文境界を越える open-tail/default 入力 |
| `ContextualTypeConstraintGraph.solve_solution` / `solve_none_iff` / `compile_solve_none_iff` / `infer_rejected_iff` | 実 solver の全自由 parameter の解を具体 carrier へ移す。任意の rows・型制約入力について、既存 `TypeConstraintInference.infer` の拒否 ⇔ supported かつ contextual 順序で充足する割当てなし。推論成功・解・cache・fuel 不要 | compiler の構文境界を越える入力、統合 `Core.infer` の主型性 |
| `ContextualValueBounds.expand_equivalent` / `ContextualCoalescing.coalesceGraph_retraction` / `models_exact` | 任意の新 contextual 解を共有 parameter に選び、実際の既存 `ValueBoundSchemes.expand` と `RegularValueCoalescing.coalesceGraph` が全 node・全深さ・全負文脈 rank で回収する。独立 graph model ⇔ 実 solve の受理結果とある制約なし parameter による要求同値。旧構造解であること・solver 成功・fuel を全入力定理の前提にしない | exact/optional/default/mask-tail を持つ共通 presence carrier |
| `ContextualRegularInference.models_exact` / `instances_exact` / `ContextualBranchInstances.models_exact` / `instances_exact` / `solve_nil_iff` | 任意の rigid graph・入力制約または有限分岐式・元割当て／任意出力 target について、独立の具体 regular model／上方出力 instance ⇔ 実受理枝と自由 parameter による実 `RegularInferenceModel.solution` の要求同値／target 以下。空結果 ⇔ 同じ carrier のモデル不存在。成功・Closed・解・fuel 前提なし | presence 専用 constructor の分解・lowering、完全な型同値 checker |
| `ContextualTypeConstraintInference.infer_correct` / `infer_models_exact` / `infer_instances_exact` / `infer_rejected_iff` | 既存 fixed-row `infer`・scheme・具体化を alias としてそのまま再利用。行が前順序で rowCheck が正確なら、任意 supported 型制約・元割当て／target で実結果の自由 parameter family と元制約の充足／instance が一致。全入力の status も新意味に対して正確 | 型 compiler の既存 supported 境界を越える入力 |
| `ContextualJointConstraintInference.infer_correct` / `infer_models_exact` / `infer_instances_exact` / `infer_rejected_iff` | 任意の反対称な行 join 代数と任意 supported paired 制約について、実 symbolic joint solver の全自由な行・値 parameter family と、新 contextual model での元の全行・値割当て／出力 instance が一致。推論に意味的 rowCheck・行割当て・解・fuel を渡さない。行を default しない | presence の exact/default/open-tail の simultaneous solver、全 source から supported を導く拡張 |
| `ContextualSourcePrincipalInference.infer_instances_exact` / `infer_rejected_iff` / `Core.ContextualRequiredInference.principal_exact` | 任意の反対称な行 join 代数・旧 supported source/Core式・任意結果に対し、新しい独立 Typing ⇔ 実 infer が返す alternative と自由な行/値 parameter の実具体化 ≤ 結果。rejected ⇔ supported かつ型付け不能。実 collect/infer/evaluator は旧 algorithm の alias | 全 record 構築・recordDefault を構文だけで support する統合入口 |
| `Core.ContextualRequiredInference.recordFree_principal` / `recordFree_rejected_iff` / `recordFree_ne_unsupported` と source 版 | 任意の反対称な行 join 代数と RecordFree 式・任意結果で、主型 iff・拒否 iff 型付け不能・unsupported 不出現。RecordFree は lambda/application/branch/let/pair/projection/variant/field/literal/旧 empty record を含み、推論成功・solver の解・support checker 成功・fuel を前提にしない | record 構築・recordDefault を含む source 全体の同じ定理 |
| `Core.ContextualRequiredInference.producerInstance_iff` / `legacy_source_typing_exact` / `legacy_core_typing_exact` / `source_typing_exact_modulo` / `core_typing_exact_modulo` | 任意の旧 Result/target で前の直接 scheme 解釈と新 Instance は定義上同じ。任意の反対称な行 join 代数・旧 supported 式・任意結果について、新独立 Typing ⇔ 同じ行のある旧 Typing と要求同値。旧 family への逆向き完全性を閉じる | exactEmpty/default を含む共通 carrier への embedding と、その presence solver との保守性 |
| `ContextualBranchCost.branches_length_le` / `branch_length_le` / `branches_total_edges_le` / `solve_length_le` / `accepted_total_cache_edges_le` | 任意の分岐式 F、either node 数 D、edge leaf 数 E、slot 数 n で、実 DNF 枝数≤2^D、各枝長≤E、総入力辺数≤2^D*E、実受理枝数≤2^D、総 cache 長≤2^D*n²。行検査の意味的正確性も不要 | 全 solver の実行時間、枝数の多項式性 |
| `ContextualBranchCost.duplicateTruth_counts` | 任意の自然数 k で、k 個の `truth ∨ truth` の積は edge leaf を持たないのに、実枝リストの長さが正確に 2^k。現在の重複列挙の指数膨張を示す | 重複排除・DAG共有を導入した実装の費用 |

以下は以前の有限 rigid 観測の候補の証明であり、Q5 対応の新モデルと区別する。
決定46・47の要求順序の候補を `ProducerRanked` / `ProducerRankedRegular` に実装した。
`ProducerDemand.Demand` は union を持たず、intersection、rigid な pair/field/tag、型変数、
mask、関数の引数・返り値・両行の要求を持つ。変数の割当ては任意の有限観測列である。
この変数解釈では `int | str` と `any` も同値になる。
[Q5 の回答](../notes/questions/2026-11-07-demand-model-contracts.md) は両者を区別し、
要求変数を有限 rigid 観測に制限せず role 制約も観測するため、これは最終モデルの候補から外れる。
以下の既存定理はこの明示した具体的な要求文法・解釈に対する結果として保持する。
arrow-domain probe の `Negative` は閉じた型で、
その内部には変数/mask を持たず、任意の引数を分離できることは未証明である。
`ProducerLe S T` は全要求環境・全要求で `T` の受理から `S` の受理が従う関係で、
関数の負位置を観測する全有限 rank も量化する。regular 版はさらに全展開深さを量化する。
どちらも solver fuel や有限サンプルによる近似ではない。
負位置の引数比較も同じ要求順序で行い、arrow を空の data 投影に置き換えない。
mask を payload の下に置ける文法は、[Q4](../notes/questions/2026-11-07-demand-model-contracts.md)
の明示した仮の前提に基づく。既存 masked data 観測の定義は変更しない。

| 定理 | 示したこと | 示さないこと |
| --- | --- | --- |
| `ProducerRanked.producerLe_refl` / `producerLe_trans` | 任意の行関係・有限型について要求順序は前順序。regular 版も任意の graph・行関係で成立 | 要求比較を決定する実行可能な checker |
| `ProducerRanked.structural_subtype_preserved` / `ProducerRankedRegular.structural_subtype_preserved` | 行関係の推移律の下で、任意の旧有限型／任意の graph 上の旧 regular 型の構造的部分型を要求順序へ保存 | 旧順序への文字通りの反映 |
| `ProducerRanked.pair_union_group` / `record_union_group` / `variant_union` と regular 版の同名定理 | 任意の行関係・全成分型で、pair・同じ label の record・同じ tag の variant の union と成分ごとの union をまとめた型が要求同値。record は payload と tail の両方をまとめる | 異なる label/tag の統合、presence の whole default image |
| `ProducerRanked.producerLe_pair_iff` / `producerLe_variant_iff` と regular 版の同名定理 | 任意の行関係・全成分型で、pair／同じ tag の比較は成分の新順序による比較と同値 | arrow の逆向き分解、absence/exact record の分解 |
| `ProducerRanked.producerLe_arrow` / `producerEq_arrow` と regular 版の同名定理 | 行推移律の下で引数の新順序による反変・返り値の共変・両行の比較を保存。同値置換には行反射律も仮定し、任意の引数/返り値型で成立 | union-free な引数要求だけから任意の引数比較を回収する分離補題 |
| `ProducerRankedArrowInversion.arrow_result_inversion` / `arrow_input_row_inversion` / `arrow_output_row_inversion` / `arrow_negative_argument_iff` | 任意の有限 arrow 比較から結果型比較を回収し、行反射律の下で両行比較も回収。target 引数が閉じた `Negative` 型の埋込みなら、行反射律・推移律だけで引数反変も含む4成分の比較との同値を証明 | 任意の変数/mask/regular graph を含む target 引数への分離・完全分解 |
| `ProducerRankedRegular.modelMap` / `legacy_instances_preserved` | 行推移律だけで旧 regular model から実際の恒等 constructor map を構成。任意の行代数・行反対称性・旧 supported 式・旧結果について旧 instance から新 ranked regular model の独立な `Typing` を得る | exactEmpty/required/default を持つ presence 拡張への具体 map、新独立型判断からの完全性 |
| `Core.ProducerRankedInstances.legacy_instances_preserved` / `legacy_instances_reflected` / `legacy_instances_exact_modulo` | 任意の行代数・任意の実際の旧推論 `Result`・任意の結果型で、返却された同じ scheme と全自由 parameter を新順序で直接評価すると、旧 instance を保存し、新 instance は同じ結果行を持つある旧 instance と要求同値。型付けや旧 instance の存在を新 instance の定義に使わない | 新 solver の返却 family の完全性 |
| `Core.ProducerRankedInstances.source_instances_exact_modulo` / `source_instances_sound` | 任意の行代数・行反対称性・旧 supported 式・旧結果で、新順序での scheme instance ⇔ ある要求同値な値型と同じ結果行での旧独立 `Typing`。各新 instance は新 regular model の独立 `Typing` も与える | 任意の新独立 `Typing` ⇒ この scheme family の instance、presence を含む全 source の保守性 |
| `Core.ProducerRankedInstances.DistributionExample.distributed_instance` | 任意の行代数・行反対称性について、旧反例の同じ supported 式・同じ実際の推論結果で、分配後の型は新 instance だが旧 instance ではない。`factorised_equivalent_distributed` は任意の行関係で同値を証明 | 旧反例の削除や旧 theorem の弱化 |
| `ProducerNormalForm.merge_equivalent` / `normalize_equivalent` / `normalize_accept_iff` | 実行可能な成分まとめ関数は任意の有限型で要求同値を保つ。全型の再帰処理は行反射律・推移律を仮定し、関数の負位置、全 rank・環境・要求も含む。指定例を `(int, int \| str)` に計算する | arbitrary union の整列・平坦化、変数の改名、完全で一意な表示標準形、regular graph の正規化 |
| `ProducerDemandExpressiveness.distinct_bases_union_equivalent_top` / `mixed_union_accept_iff` | 任意の行関係・相異なる base 2つの union はこの候補で top と同値。int/str の例では任意の rank・有限観測列を値に持つ環境・要求の受理が一致する | 言語全体でこの同一視を採用する判断。Q5 の変数解釈の選択とは区別する |

補助の `ProducerDemand` / `ProducerRegular` にある初期の順序は、arrow 引数だけ旧構造順序で
比較するため、新同値の arrow 合同性を保証しない。ranked 版はこの初期候補を改めた歴史的な段階であり、
現在の具体的な solver/source 接続先は本節冒頭の contextual 版である。
`Core.ProducerLegacyInstances` はこの実際の scheme 解釈の一般補題であり、反映の witness を
「具体化した値型 `a` と要求された結果 `c` の union `a | c`」として構成する。

同深さの循環を解く核として `PositiveEquationElimination` を加えた。
未知変数・任意の外部 atom・bottom/top・union/inter からなる任意の有限正方程式を扱う。
全座標を含む列の長さ `N` だけ `x ↦ x ∨ F(x)`、続いて `x ↦ x ∧ F(x)` を展開し、
再帰方程式を持たない有限式を実際に返す。`N` は有限 lattice の高さの上界であり、呼出側の search fuel ではない。

| 定理（接頭辞 `PositiveEquationElimination`） | 示したこと | 示さないこと |
| --- | --- | --- |
| `solve_sound` / `solve_retract` / `solved_instances_exact` | 任意の有限座標全列・任意の正方程式・任意の atom 命題割当てで、全自由 parameter から計算した式が不動点になり、任意の独立不動点を同じ parameter で回収する。任意の割当て `v` で `F(v)=v` ⇔ ある parameter の計算結果が `v`。成功・解の存在・guardedness・fuel を前提にしない | 任意の producer subtyping 制約、負の自己参照、関数・行・whole default を含む具体 presence solver |
| `project_natural` | 任意の座標列・非単射も許す座標写像・写像と可換な二つの step・任意の parameter について、実際の有限消去と座標写像が可換 | 具体的な mask 状態系とその可換性の構成 |

`PresenceTailElimination` はこの核を具体的な layer と mask に適用する。
`Body` は任意の既存 presence layer を atom とし、同深さの tail ref、union/inter、有限 mask を持つ。
`Body.record` は required head と、その label の要求を取り除いた tail の intersection として組み立てる。
source 由来や guardedness を持たない任意の tail ref 循環を許す。

| 定理（接頭辞 `PresenceTailElimination`） | 示したこと | 示さないこと |
| --- | --- | --- |
| `coordinates_complete` / `coordinates_length` / `solveFamily_coherent` / `solve_mask` | 任意の slot 数・有限 label 語彙で全 `(slot, mask)` を列挙し、容量は `slots * 2^labels`。任意の入力 graph・自由な具体 parameter layer で、結果 layer を mask した構文が対応座標の解と文字通り一致する | 任意の異なる Nat label 語彙への intern/移送、producer の要求順序との接続 |
| `solve_satisfies` / `solve_retract` / `solved_instances_exact` | 任意の有限 positive tail graph で、全自由 parameter layer が独立方程式を満たす解になり、全独立の具体 layer 解を同値を除いて回収する。意味の同値は全 payload 述語割当て・全外側 mask・全 data 値を量化する。成功・解・source 由来・fuel を前提にしない | この layer 定理単体での regular graph 化（次の表で接続）、関数・行・exactEmpty/whole default、任意の constructor 不等式の拒否完全性 |

有限 mask family は一つの実 layer の mask から構成され、自由 parameter を深さごとの任意述語で代用しない。
入力で宣言した mask label 語彙は `Fin labels` であり、語彙外の label も外側 mask の全称量化には含まれる。

`PresenceTailRegular` は同じ実消去を行った後で、payload 参照を regular graph に閉じる。
tail 参照では観測深さを減らさず、payload 参照でだけ減らす。`Body.record` は field 要求側の演算であり、
関数値や whole record-default image を含む producer constructor のモデルとは区別する。

| 定理（接頭辞 `PresenceTailRegular`） | 示したこと | 示さないこと |
| --- | --- | --- |
| `solveGraph_realizes` / `parameter_embedding` / `parameter_mask_embedding` | 任意の有限 positive tail/payload graph・任意の外部 regular graph・全自由 parameter layer で、実際に構成する regular graph が独立 `Realizes` を満たす。任意の深さ・外側 Nat mask・内部有限 mask・slot・data 値を量化し、source 由来・非循環性・成功・fuel を仮定しない | contextual producer 順序、負位置、関数・行・exactEmpty/whole default と同じ carrier への統合 |
| `solveGraph_retract` / `solved_instances_exact` | 任意の入力 graph と任意の独立 regular 解について、その root layer を自由 parameter として入れると全深さ・全外側 mask・全 slot・全 data 値で元の解を回収する。独立 `Realizes` ⇔ ある自由 parameter の実構成結果とこの意味で同値 | 任意の presence constructor 不等式をこの正方程式へ移す保存・反映、統合 `Core.infer` の solved scheme |

`CoreRequiredDemands` は有限の required demand が一致する断片を明示する。
`Required` は optional/lacks を除き、union/intersection・pair・variant・任意の payload 参照を許す。
`encode_exact` は任意の payload 述語割当て・mask・data 値について、presence demand を
legacy layer へ戻して再翻訳した意味が元の意味と同値であることを示す。
`finite_exact` は任意の有限 legacy payload 型割当てについて、独立な
`DataTypeSemantics.Holds` との保存・反映を与える。
`translate_required` により全旧 layer の data 投影がこの断片に入り、`required_mask` により
shadow 操作でも閉じる。旧 `{}` は引き続き全 record の上界であり、exact empty ではない。

`CorePresenceAlternatives.normalise` は有限 layer を相関を保つ選言標準形へ移す。
`normalise_exact` は任意の payload 述語・mask・data 値で所属を保存・反映し、
`mask_exact` は各枝全体への mask 適用を独立意味と一致させる。
これは presence 述語上の分配であり、旧構造的部分型に分配則を追加しない。
工程3の有限表現であり、この標準化自体は矛盾検出・飽和・regular 解の抽出を行わない。

`PresenceBoundCoalescing` は工程3のうち、有限個の変数間の flow と固定された
presence 上下界の消去を扱う。任意の payload 述語・mask の下で相関を保ち、
自由 parameter を有限個の値へ制限しない。

| 定理（接頭辞 `PresenceBoundCoalescing`） | 示したこと | 示さないこと |
| --- | --- | --- |
| `expand_satisfies` / `coalesce_satisfies` | 任意の有限 flat 制約集合で、伝播した下界が全制約を満たすなら、任意の自由述語 parameter（後者は layer parameter）から構成した解が全制約を満たす。layer 版は任意の payload 割当て・mask を量化 | constructor/open-tail の分解と整合性の自動証明、関数・行を含む regular graph の解 |
| `expand_retraction` / `expand_retraction_eq` / `coalesce_retraction` | 同じ flat 制約の任意の独立な解を共有 parameter に戻すと、全元 slot の述語を回収。述語版は外延的に等しく、後続の観測に正位置性を要求しない | 循環 graph の同時構成・負位置を含む regular 型の回収 |
| `consistent_iff_satisfiable` | 任意の固定境界解釈と、その包含を正確に決定する checker の下で、有限整合性検査の受理 ⇔ 独立な解の存在。fuel・solver 成功を仮定しない | 任意の述語境界に対する包含 checker の構成、presence graph 全体の拒否完全性 |

`PresenceFiniteBounds` / `PresenceFlatSolver` は、固定 bound の文法を
`bottom | top | records | present label | absent label | union | inter` に限定し、
比較 checker も含めた全域 solver を構成する。入力型 `Problem n` はこの bound の上下界・
固定比較・変数間の flow の任意の有限列であり、型付け・成功・fuel による support 条件はない。
返却 scheme は固定下界の有限 union と、共有 parameter を固定上界の有限 intersection で
制限した項の有限 union からなり、残余制約や解の witness を含まない。

| 定理 | 示したこと | 示さないこと |
| --- | --- | --- |
| `PresenceFiniteBounds.checkLe_exact` | 任意の二つの bound で、実行可能な有限 profile 比較が true ⇔ 任意の runtime data 値についての述語包含。payload や未知 field を有限サンプルに制限しない | payload 型を含む bound、任意の述語の包含決定 |
| `PresenceFlatSolver.solve_models_exact` / `solve_instances_exact` | 任意の `n`・入力問題・独立な全 slot 述語割当てで、制約の充足 ⇔ 実際に返る scheme の自由 parameter 具体化との等値。任意の出力 slot・結果述語への subsumption についても全 instance が一致 | recursive payload・open tail・関数・行、source 式からこの入力文法への翻訳 |
| `PresenceFlatSolver.solve_rejected_iff` / `solve_complete` | 任意の入力問題で拒否 ⇔ 独立な解なし。成功した場合はすべての自由述語 parameter が解になり、任意の独立解をそのまま parameter にすると回収。比較 oracle・成功・解の存在・fuel を前提にしない | この flat 断片外の求解。結果型は `rejected` と `solved` のみだが、source の unsupported 排除を意味しない |
| `PresenceMaskedBounds.checkMaskedLe_exact` / `denote_mask` | 任意の二 bound で、有限の実行比較が true ⇔ **任意の hidden-label 列**の mask 後の包含。bound の mask は既存 layer の mask と意味が一致し、未知 label・重複・順序も量化に含む | 任意の regular graph の全 mask 部分型の決定 |
| `PresenceMaskedFlatSolver.solve_models_exact` / `solve_instances_exact` / `solve_rejected_iff` / `solve_complete` | 同じ任意の flat 入力について、全 mask の独立解を、一つの有限 scheme の全自由 parameter family と正確に対応させる。全 mask での subsumption・拒否完全性・全 parameter の健全性・全 slot の回収まで、成功・oracle・fuel の前提なしで成立 | 任意の predicate family の regular 型による表現、再帰的な構成子・open tail・関数・行との結合 |

masked 版の自由 parameter は `Fin n → List Nat → (Value → Prop)` の任意の family である。
mask の順序・重複への不変性も仮定していないため、これを具体的な regular 型 carrier と
同一視しない。有限列挙は固定 bound の比較だけに使い、自由 parameter は列挙しない。
単一 field の矛盾、flow 経由の矛盾、二 field の相関を残す成功例を実際の solver で証明した。
`present 7 ∩ absent 7 ≤ bottom` が unmasked 版では成功し masked 版では拒否される例もあり、
mask 前の空集合への縮約で観測を失わないことを検査する。

`PresenceRegularCoalescing` は同じ構成を guarded な presence graph へ持ち上げる。
有限 graph の各 node は自由変数または既存の `PresenceLayers.Layer` であり、payload の参照は
pair/variant/field を通る。parameter の root layer を同じ観測深さに埋め込み、共有した参照を保つ。

| 定理（接頭辞 `PresenceRegularCoalescing`） | 示したこと | 示さないこと |
| --- | --- | --- |
| `coalesceGraph_satisfies_cache` / `coalesceGraph_satisfies` | 任意の有限 graph・入力/cache・`Closed` 証明について、任意の外部 parameter graph と全自由 parameter layer から構成した graph が、独立な constructor 等式と全 cache/入力辺を全観測深さで満たす。解の存在を仮定しない | constructor を含む全入力からの `Closed` cache の生成、完全な inspector、非guardedな open tail、関数・行 |
| `coalesceGraph_retract_at` / `coalesceGraph_retraction` | 任意の独立な **cache の解**を parameter として戻すと、全元 slot の全有限観測を回収し、data 部分型の両方向を得る | 任意の constructor 飽和での入力解の保存（flow のみは下記で証明）、旧 structural 部分型・関数の負位置での回収 |
| `coalesceGraph_mask_retraction` | 任意の共通の出力 layer と mask の下で、回収した子観測を置換しても所属は変わらない | 生成 slot 自身の root と元解の root をそれぞれ mask して比較する、より強い回収 |

`Closed` は入力辺の包含、変数を介した辺の伝播、rigid 同士の比較に対する有限の
`Derives` 証明からなる。`Derives.sound` は任意の子述語割当てについて健全性を示すが、
その規則の完全性を主張しない。上記は以下の四つの regular/source 契約全体の完了ではない。

`PresenceMaskedCoalescing` は root の比較と constructor 等式を、**すべての mask**で要求する
別の観測モデルを定義する。payload の子は既存の意味通り unmasked で観測する。
既存の unmasked 定義は変更せず、これを言語の最終モデルとして採用したとも扱わない。

| 定理（接頭辞 `PresenceMaskedCoalescing`） | 示したこと | 示さないこと |
| --- | --- | --- |
| `coalesceGraph_satisfies_cache` / `coalesceGraph_satisfies` | 任意の有限 guarded presence graph・入力/cache・同じ `Closed` 証明について、任意の外部 graph と全自由 parameter layer から構成した graph が、全 root mask・全深さで constructor 等式と cache/入力辺を満たす解になる | 完全な飽和、非guardedな open tail、関数・行、旧 instance の保守性 |
| `coalesceGraph_retract_at` / `coalesceGraph_retraction` / `coalesceGraph_root_mask_retraction` | 任意の独立な **mask つき cache の解**について、全 slot・全深さ・全 mask の観測を回収。実際の生成 root と元の root をそれぞれ mask した意味も一致し、新しい比較の両方向を得る | unmasked な解だけから同じ結論を得ること、任意の constructor 飽和での入力解の保存（flow のみは下記で証明） |

この強い解の前提は必要である。`Core.PresenceMaskObstructions.no_extensional_mask` は、
非空 mask を、unmasked な data 述語だけの関数として実装できないことを示す。
`required l never` と `bottom` は mask 前に同じ空集合だが、`l` の mask 後は前者だけが
`records` になる。`Counterexample.masked_root_retraction_fails` は、実際の二 node graph
`x ≤ bottom` に対し、`Closed` と unmasked な独立解があっても root-mask 回収が失敗する
具体例を示す。これを強いモデルへの暗黙の前提変換で隠さない。

`PresenceFlowSaturation` は入力辺と変数を介した推移律を、既存の有限 Horn 飽和で全域に計算する。
`n * n` は全 node 対の個数であり、呼出側が与える fuel や path 長の切捨てではない。

| 定理（接頭辞 `PresenceFlowSaturation`） | 示したこと | 示さないこと |
| --- | --- | --- |
| `saturate_exact` / `saturate_capacity` | 任意の有限 graph・入力辺・node 対について、計算した cache への所属 ⇔ 入力と変数経由の推移律からの独立な導出。cache の要素数は `n * n` 以下 | constructor の分解・矛盾検出・分岐付き飽和 |
| `saturate_models_iff` / `saturate_masked_models_iff` | constructor を含む任意の graph・入力辺・独立な外部 graph/slot 割当てで、計算した flow cache の解 ⇔ 入力の解。後者は全 mask について成立 | constructor の逆向き分解を加えた別の飽和の完全性 |
| `coalesce_saturated_retraction` | 任意の graph・入力辺と、その独立な mask つき **入力の解**について、実際に計算した cache で coalesce すると全元 slot を全深さ・全 mask で双方向に回収。cache の解や `Closed` を別途仮定しない | constructor を含む全入力で、任意の自由 parameter が解になること |
| `variable_coalesce_satisfies` / `variable_satisfiable` / `variable_models_exact` | 全 node が変数である任意の graph・任意の入力辺で、全自由 parameter から構成した graph が解になり、任意の独立解と計算した解 family が全深さ・全 mask で正確に対応。成功・解の存在・cache・fuel を前提にしない | rigid bound や constructor のある入力。この変数のみの断片は全問題が充足可能で、constructor の拒否完全性を含まない |

`PresenceConstructorBounds` は全 node が変数という制限を外し、pair・variant・
required/optional/lacks・union/intersection を含む任意の有限 guarded graph を扱う。
入力辺がすべて変数を終点とする、またはすべて変数を始点とする `OneSided` が構文的な条件である。
循環・共有 payload は許すが、rigid 下界と rigid 上界を結ぶ混合制約は含めない。

| 定理 | 示したこと | 示さないこと |
| --- | --- | --- |
| `PresenceConstructorBounds.saturate_closed` / `coalesce_satisfies` / `satisfiable` | 任意の `OneSided` 入力の実際の flow cache が `Closed`。任意の自由 regular parameter graph/全 slot layer で coalesce が全 constructor 等式・全入力辺を全深さ・全外側 mask で満たす。成功・cache・解・fuel を仮定しない | 両側 rigid bound の矛盾検出、分岐付き飽和、関数・行・open tail |
| `PresenceConstructorBounds.models_exact` | 同じ任意の入力と任意の独立 regular slot 割当てで、入力充足 ⇔ ある自由 parameter 具体化と全 slot が全深さ・全 mask で双方向に比較できる | 任意の二方向 constructor 問題の完全性 |
| `PresenceConstructorObstructions.MaskedPayload.no_closed_cache_preserves_model` / `no_exact_closed_alternatives` | 具体的な充足可能4-node入力について、現行 `Closed` の任意の cache がある独立解を失う。したがって同じ graph 上の任意の有限 `Closed` cache 列は全入力解を正確に被覆できない | 改訂した観測付き obligation、要求順序上の新 solver、graph を変更する solver の不可能性 |

最後の反例は `required 7 bottom` と `bottom` を、mask なしの子として同じに観測する
variant の親比較である。子に mask `[7]` を適用すると前者だけが records を許す。
現行 cache の辺は子にも全 mask 比較を要求するため、親から子への通常の辺分解は完全ではない。
この境界は [`要求モデルの追加の問い`](../notes/questions/2026-11-07-demand-model-contracts.md) に記す。

`PresenceConstructorDecomposition` は既存の data 観測に対して、各深さでの constructor 比較を
有限 alternative に正確に分解する。子の obligation は unmasked と明記し、親の全 mask 比較から
子の全 mask 比較を誤って導かない。これは新しい要求順序の solver ではない。

| 定理（接頭辞 `PresenceConstructorDecomposition`） | 示したこと | 示さないこと |
| --- | --- | --- |
| `pairAlternatives_exact` / `variantAlternatives_exact` / `requiredAlternatives_exact` / `optionalAlternatives_exact` | 任意の子述語割当て・全 label/tag で、実際に計算する有限 alternatives の充足 ⇔ 親の全外側 mask 比較。pair は左のいずれかの子が空、または二成分比較という3枝。tag 不一致、label 不一致も含む | regular graph の全深さで固定した枝を選ぶ solver、旧 `Closed` を得る全入力飽和 |
| `pair_at_depth_iff` / `pair_all_depths_iff` | 任意の graph・子参照・深さで局所分解が正確。全深さ版の結論は「各深さに対してある枝」である | 量化順を「ある一つの枝が全深さで成立」へ交換すること |
| `ChangingDepth.parent_all_depths` / `local_alternatives_at_every_depth` / `no_uniform_alternative` | 具体的な有限・非循環 graph で親比較は全深さで成立するが、3つの局所 alternative のどれも全深さを一様には満たさない | 観測深さを扱う別の obligation 表現や新しい要求順序上での solver の不可能性 |

`PresenceOpenTailTransport` / `PresenceOpenTailLowering` は、既存の
`OpenRecordConstraintGraph` の全 node 文法について、tail と payload の観測深さを分ける。
外側が `d+1` なら payload は `d`、tail と union/intersection の子は `d+1` で読む。
arrow は両 child と両 effect 行を保持する。比較は任意の有限型関係を引数とし、
data 包含への置換を要求しない。

| 定理 | 示したこと | 示さないこと |
| --- | --- | --- |
| `PresenceOpenTailTransport.node_observe_morphism` / `models_morphism` / `masked_models_morphism` | 任意の graph と可換な写像、全 open-node graph、全独立 slot 割当てで、全有限観測・意味的 constructor 等式・全制約の保存と反映。mask 付き比較も成立。単射性・非循環性を仮定しない | 任意の unguarded tail graph の解の構成、raw 構文等号の反映 |
| `PresenceOpenTailLowering.close_observe_exact` / `lowerValue_observe_exact` / `lowerValue_mask_exact` | 有限 source-term pool の全 slot・全元入力型/行割当て・全深さで、実際に構成した共有 regular block と独立 term 評価の観測が等しい。tail を展開しても payload の共有を保持 | solver の残余制約消去、元 term の由来を持たない tail 循環の処理 |
| `PresenceOpenTailLowering.compile_lower_models_exact` / `compile_lower_instances_exact` | 任意の元制約問題・入力型/行割当て・結果型で、実 compiler と有限 block lowering 後の全 constructor 等式/制約/instance が元問題と同値。有限比較の反射律のみを仮定 | 自由 parameter に制約を残さない solved family。新 presence 専用 constructor (`exactEmpty`/`recordDefault`/optional/lacks) はこの旧 node 文法にはない |
| `PresenceOpenTailLowering.compile_lower_raw_retraction` | 任意の実 compiler 出力と、独立に与えた raw constructor 等式の解を、全元 slot・全深さで回収。部分型制約の充足は不要 | raw 等号の前提を意味的同値だけへ置き換えた一般回収 |

`open_tail_at_zero` と `naive_guarded_tail_loses_masked_observation` が、tail まで一段減らす
実装では失う観測を明示する。これで旧 open-tail 制約の表現移送は進んだが、
新 presence model 上の全入力 solver 完全性を閉じたとは扱わない。

`PresenceOpenTailSignature` / `PresenceOpenTailGenerationLowering` は、実際の
`Core.PresenceGeneration.TyTerm` を扱う有限共有 block への変換を追加する。
独立な `exactEmpty`・`required`・whole `recordDefault`、arrow と両行をすべて保持する。
default の source は同一層、fallback は guarded payload とし、source の残りの field を捨てない。
ここで有限解釈 `Model` は任意の明示的な引数であり、要求に基づく具体的な有限 presence モデルの
構成をこの parametric な表現定理で代用しない。

| 定理 | 示したこと | 示さないこと |
| --- | --- | --- |
| `PresenceOpenTailSignature.block_observe_exact` / `arrow_observe` / `recordDefault_observe` | 任意の有限解釈・有限 block・全元状態・全深さで block closure が観測を保存。arrow の両行と全 default source をそのまま渡す | 各演算の意図した具体意味を finite Model の引数だけから導くこと |
| `PresenceOpenTailGenerationLowering.lowerTerm_observe_exact` / `lowerTerm_readout_exact` | 任意の有限解釈・構文で閉じた有限 subterm pool・全独立 regular 型/行割当て・pool 中の任意の実際の presence term・全深さで、構成した block と独立 term 評価が等しい。任意の readout/mask family にも等式を移せる | 具体 mask family の構成、由来のない非guarded tail 循環の求解 |
| `PresenceOpenTailGenerationLowering.recordDefault_observe_exact` / `required_observe_exact` / `exactEmpty_observe_exact` | 同じ全入力について、新しい3構成子の観測を保存。default は一 field の union に縮約せず、全 source と fallback を有限モデルの演算へ渡す | 有限モデル上の whole-image 法則を仮定なしに与えること |
| `PresenceOpenTailGenerationLowering.compile_constraints_exact` / `row_constraints_exact` / `compile_instances_exact` | 任意の有限 presence 型/行問題・有限解釈・元型/行割当て・結果について、実際の block lowering と元問題の充足・制約つき instance が同値。順序法則・solver 成功・解の存在・fuel を仮定しない | 残余制約を持たない自由 parameter family、実際の source infer の拒否完全性 |

`PresenceConstructorDefaultBoundary` は whole image の実装で落とせない条件を分離する。
`recordDefault_never_fallback` / `recordDefault_never_source` は任意の label・他方の述語について
一方が空なら strict な data image が空であることを示す。`recordDefault_inhabited_iff` は、
任意の source/fallback で image が値を持つことと「source が record 値を持ち、fallback も値を持つ」
ことの同値である。`present_exact_image_iff` は任意の exact 有限 record・存在する label・fallback について、
whole image が source 自身に等しい ⇔ fallback に値が存在する、という正確な条件を示す。
既知 present field だけを見て fallback の空性や他 field を捨てる実装にはしない。
別に `pair_bottom_not_equivalent_bottom` は任意の行関係・他成分で現在の ranked 候補が pair の形を
保持することを示す。この data image の事実と要求での同値を同一視したり、一般の
constructor bottom strictness を仕様へ追加したりしたわけではない。

`PresenceProducerDataBoundary.crossed_bottom_pair_equivalent` は任意の行関係と有限型 `A,B` で
`pair(bottom,B) | pair(A,bottom) ≡ pair(A,B)` を示す。`A=B=int` では左の既存 strict data 意味は空、
右は具体的な pair 値を持つ。`no_exact_data_factorization` は、任意の carrier・埋込み・意味写像について、
要求同値な型を埋込みで等値にし、同時に元の strict data 所属を正確に回収することはできないと示す。
これは決定46の「集合論的な部分型を別に持ち込まない」という区別を具体化した境界であり、
独立な runtime interpretation を持つ共通 presence/function model の不可能性ではない。

`CorePresenceGenerationModel` は既存 `Inference.Model` に独立な `exactEmpty`・`required`・
`recordDefault` 演算を加えた interface である。継承した `emptyRecord` は width 上界用で、
空 record 式の精密な型とは同一視しない。`recordDefault` は結果全体の型の演算であり、
選ばれる一 field の union だけに結果を縮めない。具体 regular model は上記の `Common.model` で構成した。

| 定理（接頭辞 `Core.PresenceGeneration`） | 示したこと | 示さないこと |
| --- | --- | --- |
| `generate_models_iff_typing` / `principal_exact` | 任意の拡張モデル・式・値/行割当て・結果について、`EnvRel` で対応する捕捉 scheme 環境の下で生成制約の充足 ⇔ 独立な構成子型判断。lambda/app/branch・値制限付き let の全選択肢・record/default/field を含む | 具体 presence regular model、existential 制約を消去した solved scheme、solver の停止・拒否完全性 |
| `CoreRules.conservative` / `CoreRules.generateCore_exact` / `CoreRules.principalCore_exact` | 拡張 source 判断と独立な拡張 Core 判断の同値、および全 Core 式で生成制約の exactness。構文検査により decoder の既定 literal への漏れを防ぐ | 旧 required 判断との保守性、公開 `infer` の `.rejected` / `.unsupported` の分類 |
| `unbound_default_fallback` / `generate_unbound_default_fallback` | 任意の拡張モデル・source・label・未束縛 index・結果で、閉じた default の未束縛 fallback は型付け不能で生成制約も不充足 | 関数を含む runtime safety、effect の具体的な行 solver |

`Core.PresenceGeneration.LegacyPreservation` は、旧判断から拡張判断への保存を扱う。
`Compatible` の前提は、新しい値部分型の推移律、`exactEmpty ≤ emptyRecord`、
`record l A emptyRecord = required l A` である。旧 `{}` を exact empty に変えない。

| 定理（接頭辞 `Core.PresenceGeneration.LegacyPreservation`） | 示したこと | 示さないこと |
| --- | --- | --- |
| `typing_preserved` / `closed_typing_preserved` | 任意の拡張モデル・`Compatible`・旧環境・式・結果について、継承モデル上の旧型判断を独立 presence 型判断へ保存。捕捉 poly、signature、値制限付き let の両規則を含む | 具体モデルでの `Compatible` の構成、新しい判断からの反映 |
| `closed_typing_mapped` / `legacy_instances_preserved` / `legacy_core_instances_preserved` | 任意の旧モデルから拡張モデルへの実際の `ModelMap` と `Compatible` の下で閉じた旧導出を保存。旧入口版では任意の行代数・行反対称性・旧 supported 式・旧結果について、実際の旧 instance から新しい独立 source/Core 型判断を得る | 具体 regular model 間の map、要求同値を除く反映、新 solver の solved instance への接続 |

`principal` / `principalCore` は existential 制約を保持した constraint scheme であり、
自由 parameter だけから具体化できる solver の返却値ではない。上の exactness は solver 成功・
入力型付け・fuel を仮定せず、モデルに追加の公理や代数法則も要求しない。

Core 上で実行する二つの既存入口への接続も追加した。**統一入口ではない。**
`InferenceSyntax.embed_decode` が入口の構文検査から round trip を保証し、対応外の Core 構文が
`Required.decode` の既定 literal として推論されることを防ぐ。

| 接続・定理（接頭辞 `Core`） | 示したこと | 示さないこと |
| --- | --- | --- |
| `RequiredInference.infer_embed` / `legacy_instances_exact` | 任意の legacy 式で推論結果そのものが旧入口と等しい。全 scheme・全自由 parameter・拒否・unsupported を保存 | presence モデルとの scheme 等価 |
| `RequiredInference.legacy_inferred_exact` | 任意の旧式・旧入口が返した principal・任意の結果型について、その全 instance と Required Core 型付けが同値。行反対称性を仮定 | 新 presence 規則を含む型付けへの反映 |
| `RequiredInference.recordFree_principal` / `recordFree_instances_exact` / `recordFree_rejected_iff` / `recordFree_ne_unsupported` | 任意の `RecordFree` Core 式・任意の regular 値型/行結果について、独立型付け ⇔ 実際の返却 scheme の全 parameter instance からの subsumption。拒否 ⇔ 型付けなし、unsupported を排除。行反対称性のみを代数の追加仮定とする | record 構築・default を含む断片の solver 完全性 |
| `PresenceInference.infer_instances_exact` / `infer_rejected_iff` / `data_ne_unsupported` | 任意の Core 式・任意の data 述語結果について型付け ⇔ 推論した exact Shape の包含。構文的 `Data` で拒否 ⇔ 型付けなし、unsupported を排除 | lambda・branch・regular parameter・effect 行の統合 |

`RequiredInference.RecordFree` は var/lit/lam/app/let/branch/pair/fst/snd/emptyRecord/field/variant を許す。
`PresenceInference.Data` は var/lit/let/pair/fst/snd/emptyRecord/record/recordDefault/field/variant を許す。
いずれも let の hint は `none` で、不正な射影・未束縛添字・不正な record 操作も断片に含める。
型付け可能性・solver 成功・fuel はこれらの構文断片の条件ではない。
Core の M0 model が `Type` に固定されているため、Required Core 定理の行 carrier も `Row : Type` である。

`CoreInferenceExamples` は実際の Core data 入口で present/absent、shadowed payload の消去、
採用されない不正 fallback の拒否を計算し、同じ fallback が既存 data runtime で評価されることも示す。
`unknown_default_principal` / `unknown_default_union` は任意の payload/fallback 述語に対する
開いた default operator の Core **型判断**であり、未知 base を推論した実行例ではない。
effectful fallback の推論例、未知 base を持つ lambda の推論例は未完である。

**M1 は未完了。** 関数・行・exact/optional/default/mask を統合した独立な具体 presence carrier と、
旧 regular carrier からの順序の保存・反映を構成し、record 構築・whole recordDefault・値制限 let を含む
全 presence source の実生成制約を、任意 parameter が型付く有限 solved scheme 列へ接続した。
`Core.infer_principal` と、対象断片の拒否 iff / unsupported 不出現に残余・成功・fuel 前提はない。
残る M1 の義務は、決定46の旧 source への逆向きの instance 回収と、全 public interface の標準形である。

以下の過去の obstruction は維持する。共通 producer 順序と data 包含を取り違えないための境界である。
`Core.PresenceLegacyObstructions` は実際の旧 supported 式について次を証明する。
`int × (int | str)` は旧 instance になるが、`(int × int) | (int × str)` はどの結果行でもならず、
data 包含では前者から後者へ移せる。`no_semantic_legacy_instance_exact` は、full data 包含で
subsumption する新関係と旧全 instance の保存・反映が両立しないことを示す。
新しい構造的 presence 拡張一般を否定する主張ではない。

さらに `PresenceLayerExpressiveness.no_exactEmpty_layer` は任意の payload 割当て・mask の下で、
既存の有限 layer だけでは exact empty を表現できないことを示す。有限個の言及 label の外に
field を追加しても所属が変わらないためであり、全観測深さの共通部分／和集合でも同じ境界が残る。
共通 carrier には追加の exact/closed 情報が必要となる。
これらと mask の問題の選択肢・仮の前提・正確な残りの義務は
[`M1 の問い`](../notes/questions/2026-11-06-m1-model-contracts.md) に分離した。

統合メモ5節の旧工程契約に対する現在の対応は次の通りである。
以下の `presence_*` は工程契約の名前であり、その名前の Lean theorem を追加したという意味ではない。

- `presence_coalesce_satisfies` / `presence_coalesce_retraction` / `presence_solve_complete`:
  実生成 source/Core の全 graph について `CommonBoundRefSolved` で閉じた。
  返却任意 scheme の全行・型 parameter は全制約を満たし、任意独立解は同じ行と全 node の要求同値で回収される。
  停止と閉性は実 worklist から導き、closed cache や外部 fuel を caller に要求しない。
  宣言した child/width/row 文法の外にある任意手書き graph の completeness は主張しない。
- `presence_generate_exact`: `Core.PresenceGeneration.generate_models_iff_typing` と `PresenceNormalForm` の
  既存の独立判断への exactness を、`CommonPresenceSolvedSource` / `Core.infer_principal` が実求解へ接続した。
  最終 instance の parameters に atom の充足条件は残らない。
- `presence_legacy_instances_exact`（決定46による新契約）: 共通モデルと埋込みを定義した上で、任意の旧 supported 式・任意の旧結果型について、旧 instance ⇒ 新 instance を示し、新 instance からはある旧 instance と要求で同値であることを示す。全 instance の文字通りの一致は要求しない。
  `ProducerContextualInstances` は、実際の旧 scheme を新しい具体 regular 順序で再解釈する境界ではこの両方向を閉じた。
  `ContextualRequiredInference.legacy_source_typing_exact` / `source_typing_exact_modulo` により、任意の行代数・行反対称性・
  旧 supported `e`・結果 `c` について、新 model の独立 `Typing [] e c` から同じ scheme の新 instance と、
  同じ行を持つ要求同値な旧 Typing を回収する逆向きも閉じた。
  共通モデルへの regular 型埋込みは保存・反映を証明した。旧 supported source の旧 instance から実新入口への保存は
  `CommonSolvedLegacyPreservation.legacy_instances_preserved` で閉じた。未完なのは新 presence solver/独立型判断からの逆向きである。
  `CommonLegacyTyping.compatible` は具体モデルの互換性を証明し、旧型付けと実旧 instance の新独立型判断への保存も閉じた。
  `CommonLegacyReflection` は任意旧 regular 固定境界と共有 flow の witness を回収し、
  `CommonLegacyEmptyReflection` は任意の埋込み旧結果における空 record の規則を反映する。
  任意 source の未知子を含む constructor 方程式を同時に満たす旧 witness の回収は未完である。
  反映は元依頼の旧結果型の埋込みの範囲で量化し、新たな exact 型へ無条件に拡大しない。

旧 `ProducerRanked` 候補では、任意の rank `k` と型 `S,T` について
`(∀ N : Negative, ProducerLeAt k N.embed S → ProducerLeAt k N.embed T) → ProducerLeAt k S T`
という閉要求による分離補題が未証明である。必要な行の法則を明示してこの主張を示すか、
成り立たない場合は要求文法を拡張する必要がある。`S` 自体が `Negative` の埋込みなら
自身を要求に使えるため、上記の限定された arrow inversion はこの一般分離を仮定せず成立する。
新 `ProducerContextual` は要求変数の解釈を変更し、この旧候補の分離補題を仮定せず任意引数の分解を証明した。
exact/optional/default の具体的 acceptance と合同性、独立 strict data image、同深さ record/default/mask の
自由 family と、実生成された全 constructor 不等式・全 presence source への接続は上の共通モデルで構成した。
runtime data 解釈に関数値は含めず、関数／行は独立した要求意味で観測する。

旧 `Layer.record` の tail は有限 layer、open-record graph の tail は node 参照であり、
単純な置換は観測深さを減らす位置を変える（spec 10.32.5）。さらに旧 regular 部分型は構造的関係で、
presence の data 述語包含との同値はない。これらを既存 data 観測の橋だけで埋めることはできない。
具体的な共通モデル、guarded 子と同深さ record/default-tail を共有する regular block の解構成／retraction、
宣言した共有 symbolic 行の simultaneous family は追加した。
任意 target に対する record/default の outer inspector、実生成比較の symbolic compiler と
有限飽和・全 presence source の自由 family・実 `Core.infer` は上表で閉じた。
既存 `collect_instances_exact` の変更、既存 theorem・test expectation の変更、仕様の仮決定は行っていない。
未実装部分の正確な量化と前提は [残契約の設計メモ](../notes/design/2026-11-07-m1-remaining-contracts.md) に記す。

### M1 interface 標準形の有限断片

旧 `ProducerContextualNormalForm.normalize_not_complete` は旧 pass の正しい反例として残す。
新 pass は base の union を `bool`, `int`, `str`, `unit` の辞書順へ整列し、変数はその前に共有 ID 順で置く。
`int | str` と `str | int` の出力を一致させ、`int | str` と `any` は区別する。

| 定理 | 示したこと | 示さないこと |
| --- | --- | --- |
| `ProducerCanonicalClauses.canonicalEncoding_exact` / `normalize_exact` | 任意の行関係・base/bottom/top/union/intersection の二つの閉式で、contextual 要求同値 ⇔ 同じ最小 clause encoding ⇔ 同じ実 normalize 出力。保存と冪等性も証明 | 構成子や binder を含む全 interface |
| `ProducerCanonicalOpenClauses.canonicalEncoding_exact` / `clause_variables_first` / `clauses_sorted` | 任意の共有 slot 数 n・二つの scalar 格子式で、同じ ID の任意有限 contextual 型割当てに対する要求同値 ⇔ 同じ整列 clause code。変数が先、具体型は辞書順。吸収・重複除去も同じ実正規化で扱う | parameter の再番号付け、存在的 instance 集合の一致 |
| `CommonCanonicalOpen.common_scalar_profile_exact` / `canonicalEncoding_exact` / `normalize_exact` | 同じ scalar code を、同じ共有 ID の全 Common.Ty 割当てについて保存・反映する。割当ては任意の regular/mask/default/arrow 型でよい。実 PresenceGeneration.TyTerm の評価とも接続する | 任意 interface family の再parameter化を許す同値 |
| `CommonCanonicalShapes.canonicalEncoding_exact` / `normalize_exact` / `collect_equivalent` | 任意 n、固定した共通 Shape と行 slot 割当て、二つの Term について、同じ ID の全 Common.Ty 割当てで要求同値 ⇔ 同じ code ⇔ 同じ normalize。Shape は nested pair、単一 required field、tag、scalar 引数と同じ行 ID の arrow を含み、正の union は成分ごとにまとめる。arrow の引数は intersection にまとめる | 異なる Shape／行 ID 間の比較、混合 head、一般 record/default/mask の正規化、nominal/role 義務、binder α 正規化、regular graph の一意化 |

`CommonCanonicalShapes.Code` は Shape の情報を省略する。復旧後の `CommonCanonicalInterface.Code` は
構成子・label・arrow の行 ID を含め、この制限を有限 constructor 構文について除いた。

| 復旧後の標準形定理 | 示したこと | 示さないこと |
| --- | --- | --- |
| `CommonCanonicalInterface.canonicalEncoding_exact` / `interface_canonicalEncoding_exact` / `normalize_exact` | 任意 n・異なる Shape を許す二つの有限 constructor interface で、全行割当て・同じ共有 ID の全 Common 型割当てに対する要求同値 ⇔ 自己完結 code の一致 ⇔ 正規化構文の一致。構成子・label・共有行 ID の違いを実観測で反映。`int \| str` の順序の反例も新 pass で解消 | mixed-head lattice、一般 record/default/mask、nominal/role、regular interface、parameter の再parameter化 |
| `CommonCanonicalAlpha.canonicalEncoding_exact` / `normalize_exact` / `alpha_instances_exact` | 任意 n・上記 Form 二つで、ある一つの同時全単射の後の全行・全 Common 型割当てでの要求同値 ⇔ 実有限探索で選んだ同じ code。任意固定行・任意 target について、target と要求同値な具体化の存在を両方向で保存 | slot 数にかかわらない正負位置による消去・共起/併合と一般の再parameter化、異なる slot 数の比較、弱い変数、行 ID の名前変更、全 instance 同値からの完全反映 |
| `CommonCanonicalNames.normalize_exact` / `normalize_first_occurrence_order` / `normalize_instances_exact` | 任意 n・上記 Form 二つで、独立な意味的 α 同値 ⇔ 同じ実 normalize 出力。出力 Form 内の異なる変数を最初の出現順に並べた番号は `List.range k`。任意固定行・target に対する要求同値な具体化の存在を保存・反映 | weak variable の metadata、非単射の消去/併合、行の α 同値、実 display renderer への接続 |
| `CommonCanonicalParameters.compact_project_exact` / `compact_expand_exact` / `compact_instances_exact` / `compact_subtype_instances_exact` | 任意 n/Form・任意行割当てで、実使用 k 個への未使用 parameter 除去が全旧/新 parameter の具体化を literal equality で相互回収。要求同値な instance family と subsumption 後の family を保存・反映し、k≤n、全新 slot の使用も証明。normalize 後の版では吸収で消えた slot も除去 | 使用中 slot の一般併合、弱い変数の metadata、全文法への標準形の完全性 |
| `CommonCanonicalParameters.reparameterization_instances_exact` / `reparameterization_subtype_instances_exact` / `Examples.union_parameters_merge` | 任意の異なる arity を許す二つの Form と有限 scalar substitution 二つについて、両方向の pointwise 要求同値から全 instance family の一致を導く。置換は全単射を要求しない。使用中の二変数の union と一変数の family が一致する例も証明 | 一般再parameter化の計算・存在の完全判定、任意 public interface の canonical encoding |
| `CommonCanonicalIntervals.instances_interval` / `familyEquivalent_iff_endpoints` / `canonicalEncoding_exact` | 任意の固定 slot 数 k・独立に異なる一般化 slot 数 n/m・全 scalar union/intersection 式二つについて、固定 slot へは同じ任意 Common 割当てを保持する。任意 target が要求同値な instance となる iff 全一般化 slot を bottom/top に置いた二端点の間にあり、全 target の instance 集合一致 iff 二端点の有限 code が一致。再parameter化の候補・全単射・同 arity は前提にしない | constructor をまたぐ共有、正負の共起、行式、regular/nominal/role を含む全 interface。固定 slot は weak/captured の同一性を保つが weak 表示 metadata は実装しない |
| `CommonCanonicalIntervals.subtype_instances_lower` / `subtypeCanonicalEncoding_exact` | 同じ全 scalar 文法で任意固定割当て・任意 target に対し、ある任意 parameter の instance が target 以下 iff bottom 代入の下端が target 以下。その全 target family の一致を一つの有限 code で完全判定し、正位置だけの一般化変数を共有を保ったまま同時消去する | exact instance の上端の消去、負位置を含む interface への無条件な適用 |
| `CommonCanonicalPositive.subtype_instances_lower` / `canonicalEncoding_exact` | 任意固定 slot 数 k・任意一般化 arity n/m・任意二つの有限 Form について、一般化された全出現が正であるという構文条件の下、全 rows・全固定 Common 割当て・全 target の subtype-instance 集合一致 iff 同じ lower Form の完全 code。pair/required/variant/arrow result を含み、固定 slot は正負に共有してよい。行 ID を保つ | 一般化 slot が負にも出現する Form、exact constructor instance の区間化、行式・regular/nominal/role・全 export/display |
| `CommonCanonicalPolarity.simplify_instances_exact` / `normalize_instances_exact` | 任意 Form・任意 frozen 指定・任意固定 Common 割当て・任意 rows/target で、非 frozen の正だけの slot を bottom、負だけを top にする一回の簡約が subtype-instance 集合を保存・反映。正負共有と frozen の値は同じ ID のまま保持 | exact instance 集合の保存、arity の縮小、frozen の自動導出、role 義務を含む変換、完全 canonical encoding。normalize は固定点ではない |
| `CommonCanonicalScalarFamilies.exact_instances_iff_bounds` / `exactCanonicalEncoding_exact` / `canonicalEncoding_exact` | 任意 weak slot 数 k・独立に異なる一般化 arity n/m の scalar 式二つについて、全固定 Common 割当て・全 target に対する exact instance family は二端点、subsumption 後の family は下端の有限 code で完全に比較できる。固定 slot は同じ値を保ち、再parameter化の候補・全単射・同 arity を前提にしない | constructor をまたぐ共有、正負の共起、一般行式、regular/nominal/role を含む全 interface |
| `CommonCanonicalScalarExports.interface_canonicalEncoding_exact` / `scheme_instances_exact` | 任意 weak slot 数 k・異なる一般化 arity n/m の scalar 式二つから作る `obligations = []` の interface について、任意 role theory・ambient computation 割当て・target に対する実 `QualifiedInference.Interface.scheme.Holds` の同値 iff 下端の有限 code 一致。既存公開意味を使い、固定 slot を保持 | 義務付き interface、一般行式の正規化、実 `Core.infer` の全返却 family から export/display への経路 |
| `CommonCanonicalObstructions.same_arity_used_parameters_not_alpha` / `positive_pair_image_not_interval` / `mixed_polarity_sharing_matters` / `captured_slot_cannot_be_generalized` | 同 arity・全 slot 使用でも instance 等価な union/intersection は非 α。共有 pair の exact image は区間ではなく、arrow の正負共有や固定 slot の分類は instance を変える。正の一般化変数だけを共有を保って 2→0 個へ消す正例も証明 | 全 interface の正規化が不可能・決定不能という主張 |
| `CommonCanonicalScalarExports.Examples.positive_role_cannot_be_erased` / `CommonCanonicalPolarityBoundary.normalize_not_idempotent` | 正位置でも role 義務を消せない実公開 interface の反例。一回の polarity normalize は、正負共有した変数の正の出現が格子簡約で消える例により非冪等 | role-aware 正規化や、今後の反復正規化の不可能性 |

polarity pass は Form の定理であり、role 義務を持つ実 qualified Interface への意味保存の接続は未証明である。
role に依存する一般化 slot を変換中に frozen とする場合も、その値を保った上で元の外側の存在量化を残す必要がある。
frozen の指定だけで一般化 slot を weak slot へ変更するものではない。

任意の concrete `Common.Row` は述語であるため、全 concrete 型を直接有限文字列へ計算可能に符号化する
という主張にはしない。完全な interface では有限行式・regular graph・nominal/role 義務までの正規化が残る。

scalar については既存の公開 Interface の意味へ接続したが、これらの正規化を
実 `Core.infer` の全返却 family から export/display へ適用する呼出経路は未接続である。
scalar 実装は n 個の共有 slot と4個の base の全 profile を列挙し、個数は `2^(n+4)` となる。
最小 clause 選別は profile 間を走査するため、総計算量を線形・多項式とは主張しない。
α pass は forward map を列挙し、逆写像を有限 lookup で回収する。候補数の上界 `n^n` を証明したが、
この全探索を実用的な一般化変数の正規化アルゴリズムとは主張しない。
未使用 slot の除去は上の `compact` で構成した。実際の interface 表示へ組み込む前に、共有表現を含む費用評価と
一般再parameter化・全文法への接続が必要である。

### SCC 局所性と module cache・増分更新

以下は実際の selection 関数と、独立した逐次 module build の証明である。
内部表現の選択と未接続の境界は [設計メモ](../notes/design/2026-11-07-m1-solver-and-locality.md) に記録する。

| 定理 | 示したこと | 示さないこと |
| --- | --- | --- |
| `MethodResolutionLocality.resolve_local` / `freeze_local` / `finalize_local` | 任意の二つの SCC 確定 snapshot で、問合せ中の名前が同じで、未知 receiver ならその名前の可視候補集合、既知 receiver なら field の有無と不在時の typed fallback が同じなら、実際の解決・凍結・elaboration 結果が等しい | SCC の receiver 知識を solver が確定する過程、全 source の elaboration |
| `MethodResolutionLocality.scc_order_independent` / `scc_input_locality` / `resolved_site_exact` | 任意の確定 snapshot 表・SCC ごとの site 列・初期回答表で、同じ SCC 集合を処理する任意の順序は全 site の回答を一致させる。処理外の snapshot は自由に変更でき、処理した一意解は既存の独立 `Selects` と同値 | 未確定 snapshot を処理してよいこと。重複は無害だが、上流の constraint 求解の再走査を不要とする主張ではない |
| `ModuleIncremental.dirty_exact` / `rebuild_called_iff` / `rebuild_calls_le` | 任意の有限 topological dependency 表と変更フラグで、計算した dirty 集合は独立な有限依存経路での影響範囲と同じ。実際の rebuild 分岐はその範囲だけ compile を呼び、呼出し数は module/SCC 数 `n` 以下 | dependency graph の抽出・SCC 発見、各 compile 内部のコスト、dirty 判定の総実行時間 |
| `ModuleIncremental.rebuild_exact` / `rebuild_valid_cache` / `rebuild_changed_graph_exact` | 任意の pure compile 関数・新旧 source/key・新旧 dependency 表・変更フラグについて、変更なしとした node の key と依存列が同じなら、正しい旧 cache を使った増分 build の全結果は新しい全体 build と等しい。import の変更も対象で、エラーを含む任意の結果型を量化 | 不完全な key での cache 再利用、node identity/topological 番号の対応付け、実 Yulang module compiler への接続 |
| `ModuleIncremental.module_cache_sound` / `rebuild_normal_forms` | pure compile に渡す source/key と依存 interface 列が等しければ同じ artifact になる。上記の増分一致は任意の決定的な表示・正規化関数の後も保たれる | interface の意味的同値 ⇔ 同じ標準形、完全な標準化関数の構成 |
| `ModuleInterfaceCache.rebuild_exact` / `rebuild_valid_cache` / `rebuild_called_iff` / `called_implies_affected` | source/key と完全な artifact の等号が決定可能なら、任意の pure compile・新旧 source/key・新旧依存表で、実際の入力を比較して cache を再利用する手続きは全体 build と等しい。dirty 集合・成功・解を呼出側から渡さない。compile を呼ぶのは入力が変わった node だけで、変更フラグが clean key の不変性を満たす場合は逆依存範囲の外を呼ばない | semantic interface 同値の判定器、実 compiler の ambient dependency の抽出 |
| `ModuleInterfaceCache.rebuild_calls_le` / `rebuild_calls_nodup` / `Examples.unchanged_interface_stops_recompilation` | 任意の上記入力で compile 呼出しは node 数 `n` 以下かつ重複しない。source が変わっても interface が等しい場合に依存 module の再計算が止まる実例を証明 | 各 compile の時間、全 key/interface の比較費用 |
| `MethodResolutionCost.resolveCount_value` / `resolveCount_bound` / `runCount_bound` | 任意の site で計数付き実装の値が既存 resolver と一致。未知 receiver は可視 role 数 `R` で `1+2R` 以下、既知 receiver は型 node 数 `V` で `1+V` 以下。任意の処理列は各 site 上界の和以下 | map lookup/update の内部費用、ID の bit cost、solver 全体の時間 |
| `MethodResolutionIndex.indexedResolve_exact` / `resolveNamesCount_exact` / `resolveNamesCount_bound` | 任意の有限 catalog・可視 role 列・名前・receiver・fallback で、同じ role/name の宣言が一致するなら index と既存解決の結果が等しい。任意の可視宣言列 `D` 件と名前列 `N` 件の計数付き一括解決は `3D+2N` 以下。上界自体は catalog の関数性も成功も仮定しない | visibility filtering、永続 map の実装費用、未確定 SCC の依存構築 |
| `InferenceSubstitutionCost.formulaSubst_value` / `instantiate_value` / `instantiate_bound` / `instantiate_size_bound` | 任意の scheme と具体化先で計数付き置換の値が実際の `Scheme.instantiate` と等しい。scheme の型・行を含む全 node 数 `N`、binder 深さ `H`、具体化先の型・行 node 数 `K` に対して syntax work は `N*(1+max(2,K)*H)`、従って `N*(1+max(2,K)*N)` 以下。束縛下の型・行の rename も数える | source body の再推論、identifier の bit cost、メモリ allocator、scheme を使う solver 全体の時間 |
| `TypeSimplificationSize.simplifyAll_sizes` / `jointSubstitution_sizes` / `merge_candidate_count` / `sandwich_candidate_count` | 任意の parameter 数 `n` と入力項で、実 `simplifyAll` は値型 node 数と行込み全 node 数の両方を増やさない。merge certificate の一時置換は元の3倍以下。実候補列の長さは merge が `n*n`、scalar sandwich が `4*n` | 線形時間の簡約、完全な一意標準形 |
| `TypeSimplificationCheckCost.symbolicCount_value` / `symbolicCount_bound` / `symbolicCount_size_bound` | 任意の型項二つについて、型・行の等号と record spine の走査も数える実参照 checker が既存 `symbolicCheck` と同じ Bool を返す。行込み node 数の和 `S` に対して費用 ≤ `(S+1)*128^S`。再帰深さは入力から決まり、外部 fuel・成功前提なし | 多項式時間の checker、ID の bit cost・メモリ割当て、canonical interface の完全性 |
| `TypeSimplificationCost.simplifyAllCount_value` / `simplifyAllCount_bound` / `simplifyAllCount_instances_exact` | 任意の `TyTerm (Fin n)` で、計数付き4段階 pipeline は実 `simplifyAll` と同じ型項を返し、費用 ≤ `totalBudget n (tyNodes term)`。候補表のコピー・map/product/append と全候補検査を含む。行前順序の下で任意の行割当て・結果型に対する旧構造的 `Instances` を保存・反映 | 新 contextual instance への意味の移送、有限 parameter inventory `finRange` の library 内 materialization、ID bit cost・allocator、多項式時間や完全 canonical form |
| `ModuleScheduling.run_legal` / `run_build_exact` / `schedule_independent` / `run_once_bound` | 任意の source/key・依存 graph・完全な局所入力を読む純粋 compile について、依存完了後に未処理 node を選ぶ任意合法 schedule は実依存 lookup を成功させ、同じ module 集合なら同じ artifact 表を返す。全体 build と一致し、実 compile 呼出 trace は schedule、各 node 高々1回・n個以内なら呼出≤n。完成した snapshot は入力にしない | source から SCC/dependency を抽出する証明、実型 solver が局所 compile 契約を満たす証明、compile 内部の時間上界 |
| `MethodResolutionScheduling.schedule_independent` / `run_snapshots_and_answers` / `run_selection_exact` / `scheduled_once` | 任意の source/key と完成した依存 artifact 列から Site 群を作る純粋 prepare、任意の同一 node 集合を処理する二つの合法 schedule で、実行中に生成する snapshot・export・receiver/scope/fallback・実 resolve の三状態結果が一致。任意の位置の unique 結果 ⇔ 独立 Selects、compile trace は重複せず node 数以下。固定 snapshot や事前の SameFacts は不要 | concrete solver/名前解決が complete key と依存だけを読む prepare を実装する証明、source から SCC の抽出、条件付き impl 探索全体の費用 |

`EOFNoDefaulting.accepted_export_independent` は同じ型情報・割当ての下で、**両方の EOF 検査が成功した場合**の
公開型の一致である。後続 impl による曖昧化まで無条件に cache から省略できることを意味しない。
依存 interface/key は公開型に加えて residual qualifier、可視 impl と辞書依存、nominal/effect identity、
設定と規格化の version を含める。意味的同値を完全に決める全言語の標準形は依然として未証明である。

### M2: effect 判断の統合（部分完了）

`CoreEffectTyping.lean` の `Core.EffectTyping.Typing` は、共有 `Core.Expr` 上の独立判断である。
`Core.Typing (Core.EffectTyping.model m view contract)` として使う。
lambda/app、値制限付き let（捕捉した多相環境を含む）、branch/pair/variant/required record と、
request/boundary/handler/multiHandler/partialHandler を同じ判断に置いた。
旧判断や evaluator をこの判断の定義に含めない。既存の `Core.Effects` / `Core.Resolved` は変更しない。

**モデルと内部表現:** 任意の `Inference.Model m`、`RowAlgebra` と、それらの空行・和・包含を
整合させる `RowView m algebra` が入力である。モデルの部分型関係に新しい法則を仮定しない。
符号付き重みを扱う具体例では `SignedStructural.model 1 Nat` と `signedAlgebra 1 Nat` を使う。
署名の局所変数は有限個の値型だけを取り、key と追加行はその割当てによらない。
`Contract.coherent` は request 用署名と同じ key の複数 handler 用署名の一致を要求する。
各 handler の incoming mask は `Contract.permission : Core.Expr s → s.Key → Bool` で明示する。
これはモデル入力の選択であり、source から mask を発見する算法ではない。
同じ構文の複数 occurrence に異なる mask を割り当てる表現も、ここにはない。

request では呼出しごとに局所型を存在具体化する。handler では外側環境・action 型・value arm 型・
最終結果を先に固定し、全局所型割当てで operation arm を検査する。
Lean の帰納的定義では arm 内部の結果を割当てから computation への関数として保持する。
継続の出力は元の action computation のままである。
複数 arm の型は value arm を末尾とする union、行は書かれた順の有限和で集約する。
部分 handler は既存の `MultiOperationPayloadHandlers.removedKeys` を直接使い、
guard なしの反駁不能 arm がある key だけを残余から引く。
全 arm に許可検査を課し、照合が失敗する arm も検査対象とする。

`CoreEffectGeneration.generate` は**モデル上の意味的制約（Prop）**を構造再帰で生成する。
比較・許可検査・scheme lookup・量化から構成し、型判断や solver を呼ばない。
値 let には生成済みの scheme 述語を保存する。有限の `RecursiveEffects.Formula` の拡張ではなく、
slot/rename/substitution を持つモデル非依存の制約構文への変換は未完である。
したがって、下の `principal_exact` を有限主型 scheme の構成・solver 完全性と読み替えない。

定理名の接頭辞は `Yulang.Core.EffectTyping`。

| theorem | what is proved | what is NOT proved |
| --- | --- | --- |
| `generate_models_iff_typing` | 任意の model/view/整合署名契約・Core 式・意味的 scheme 環境・捕捉 binding 環境・結果 computation で、lookup の `EnvRel` を前提に、生成した意味的制約 ⇔ 独立型判断。全5 effect constructor と値制限 let の両規則を含む | 複数/部分/多相 handler の有限 `Formula` 生成、solver 成功・完全性、M1 の型モデル統一 |
| `principal_exact` | 任意の同じモデル入力・閉 Core 式・結果 computation で、空環境の意味的生成制約 ⇔ `Core.Typing`。solver/fuel/成功の前提なし | 有限な principal scheme の出力、最小解の計算。未対応 constructor は両辺とも偽であり、全 Core の support 完了ではない |
| `legacy_conservative` | 任意の旧単相 `RecursiveEffects` 署名・式・捕捉環境・結果について、署名が key 別の局所署名に因子化できる前提で、旧判断 ⇔ 新 M2 モデルの Core 判断。mask は全許可、局所変数数は0 | 同じ key に無関係な署名を割り当てる旧入力への無条件な同値、shape 付き multi/payload 判断からの接続 |
| `legacy_generate_models_iff_typing` | 任意の旧有限生成器の入力・model/view/割当て・結果で、旧 `EnvRel` / `SigRel` と上の署名一致を前提に、実際の旧 `RecursiveEffects.generate` の充足 ⇔ 新 M2 判断 | 有限生成器への multi/partial/operation-local 多相の追加 |
| `Examples.two_operations_generated` / `partial_generated` / `partial_forwards` | 二 operation と value arm の閉式の生成解、部分 arm の key を残す生成解、同じ arm 表の既存 runtime による不一致 payload の forwarding | 新 Core evaluator の正しさ。forwarding は既存 payload runtime の実行等式であり、新 Core 型付けからの実行安全性ではない |
| `Examples.forbidden_multi_rejected` / `forbidden_multi_no_solution` / `forbidden_partial_rejected` | 具体的な不許可契約で、任意の結果 computation に対する型付け拒否と multi の生成解不存在。常に失敗する部分 payload テストも許可検査を免れない | source annotation からの mask 導出、実行到達性の推論 |
| `Examples.local_request_generated` / `local_escape_rejected` / `local_escape_no_solution` | caller による int への局所具体化と、任意局所 payload を固定 int 結果へ返す arm の拒否・生成解不存在 | 任意モデル・任意結果上界での payload return 拒否。role 制約付き局所型の辞書・method 接続 |
| `Examples.callback_boundary_roundtrip_generated` / `callback_transport_roundtrip` | 実際の新 Core 判断で callback 本体の符号付き protect/release が相殺する生成解。別に、既存の明示的高階 transport が返された callback を元へ戻す実行等式 | Core.boundary が返り値内の callback を自動で transport する elaboration、両入口の統一 |

**閉じていない補題と停止した項目:**

1. 有限制約生成の拡張には、構文的な多相署名とその評価関係を先に与え、任意の model/view/割当て、
   対応する環境・署名、式・結果 term について
   `Holds (generateFinite … e out) ↔ generate view contract … e (eval out)` を証明する必要がある。
   全称局所 binder と捕捉 scheme の具体化の可換性、有限個の arm の型・行集約まで含める。
   任意の意味的署名関数を有限構文へ変換できるとは仮定しない。
   これは未完成の構成・解釈補題であり、不可能性を主張していない。
2. shape 付き旧 `MultiOperationHandlerTyping.Typing` / payload 判断から**同じ新モデル**への保存には、
   `CTy` と型環境の具体的な解釈、および任意の旧型付けから解釈後の新型付けを得る補題が必要である。
   現在の `Core.Resolved.multi` は `.atom` / `.strictApp` / 注釈の消去を使うが、
   この M2 モデルには atom/strictApp/一般 widening の規則をまだ置いていない。
   既存の `Core.Resolved.multi_core` は別モデルへの一方向保存としてのみ有効である。
   同じ注釈付き旧式への反映は M0 の erasure 反例があるため主張しない。
3. 高階境界には、Core 構文への wrapper 挿入・潜在行の型変換と評価の可換性が必要である。
   既存 callback の実行等式をこの接続の代用にしない。

**対象と仮の入力条件:** role を持たない operation 署名、解決済み key、明示された mask、
既存の純粋な payload テスト/guard を扱う。仕様5.1/決定11の role 証拠は未統合である。
source の pattern 束縛・effectful default/guard・mask 導出・fresh 化、M1 の型モデル統一、
solver 完全性、全言語の主型推論・実行安全性は閉じていない。
言語仕様の未決を新しく採用した箇所はなく、この作業で追加した仕様質問はない。

## Case の照合・順序・presence

`CaseValues` は内容つき literal、pair、record、variant、解決済み nominal identity、有限listを持つ。
`CasePatterns.Pattern` は wildcard、名前、literal、整数範囲、pair、record field/default、
list nil/cons/snoc、variant、nominal、or、as を持つ。record の残りを照合するときは
入力record全体を渡し、list tail には残りの要素だけを渡す。

独立な `CasePatterns.Typing` は照合で得る束縛の値安全性を扱う。
任意の型付け、入力型を満たす値、型付けに健全なdefault evaluatorについて、
`typing_matches` は照合がruntime errorにならず、成功した場合は宣言された束縛型を満たすことを示す。
`mergedVariant` は `VariantsMerged` のlookupが返す**payload全体**に子patternを型付けし、
他tagを持つ入力はmissとする。`mergedNominal` は同じ形で、単一nominal identityの
全constructor行を入力にして各constructorを分岐できる。orの名前集合と裸`..`の禁止は `Typing.aligned` に従う。
同じ名前集合の異なる束縛順をそろえるsource passは未証明である。

`CaseEvaluation` は上から順に照合し、成功したpatternのguardだけを評価し、guardが真の最初のbodyだけを評価する。
訪問列はscrutinee、arm、guard、bodyと葉の評価を保持する。
`runArms_typed` は束縛をguard/bodyへ渡す際の安全性、`runArms_progress` は型付きarm列と
実際に合うunguarded armの存在から、型を満たす結果が返ることを示す。
この定理単独の照合witnessは、次の網羅性の節で検査結果から構成する。

`CaseDataTerms` は具体的なdata葉のAST・評価器・独立型判断を持ち、
`typing_evaluates` からdefault/guard/bodyの健全性契約を導く。
guardは実際のbool値から判定する。構築のrecordDefaultはstrict、pattern defaultは欠如時のみである。
現時点のdata葉には関数、再帰、effect handler、cast、nested caseを含めない。
caseのscrutinee/body・pair・letへの有限な入れ子は、後述の `CaseTree` で追加する。

回答済みQ4を反映する `ScopedCasePatterns.run` は、前の部分で得た束縛を外側環境の前へ置き、
後のdefaultへ渡す。nested patternにも同じ環境を運び、orの失敗枝の束縛は次の枝へ漏らさない。
独立な `ScopedCasePatterns.Typing` も同じ順に型環境を延長する。
任意の型・値環境に健全なdefault evaluatorと独立型判断を前提に、`typing_matches` は
型に適合する任意の環境・入力から、missまたは型の合う束縛を導き、runtime errorを排除する。
`run_constant_defaults` はdefaultが環境を読まない場合に旧matcherと訪問列を含め完全に一致する。
`ScopedCaseEvaluation` はこのmatcherを既存のarm/guard/bodyの順序へつなぐ。
`ScopedCaseCoverage.typing_total_matches` は、独立なscope付き型判断と既存の構造的 `Total` から
実際の照合成功と束縛型を導く。defaultの型が各使用scopeでcoverage domainに含まれる条件を明示する。
`covered_arms_match` / `checked_arms_evaluate` により、旧coverage checkerを変更せずに
scope付きarm列のprogressへ接続する。比較するdomainと型入力は異なってよいが、実値は両方を満たす必要がある。

`CaseDataTerms.default_scoped_sound` は具体data式を各時点の環境で評価してこの契約を充足する。
`ScopedCaseDataProgram.typing_evaluates` は、独立な構文型判断と整合する任意の外側環境から
実際に結果型の値へ返ることを示す。この簡単な入口は少なくとも一つのunguarded armについて
独立な構造判断 `TotalTyping` を要求し、照合成功を前提にしない。
`PatternBindingChecks.check_exact` は名前検査と独立な `NamesValid` を一致させ、
`checked_path_nodup` は検査を通る任意のpatternの任意の構文経路に重複binderがないことを示す。
別のor枝の同名束縛と外側の名前を隠すことは許す。
`checkedEval_rejects_iff` により不正なbinderを持つarmがあればscrutineeの実行前に拒否する。

Q5・Q6は回答済みの規則として維持する。先行missなら後のdefaultを実行せず、
orは最初の照合成功で確定し、その後のguardが偽なら次のarmへ進む。
回答済みQ7の同一経路の重複名拒否は上の静的検査で実装する。
旧 `CaseDataProgram` / `CaseTree` のscope非依存defaultの定理は特殊な場合として残し、
source全体のdefault環境の割当てやeffectfulな葉の翻訳を証明済みとは扱わない。

`CasePresenceValidation` はoptional宣言metadataを許可し、requiredを拒否、unknownを未解決とする。
literal内容を旧marker値へ射影したrecordについて、lookupとrequired/optional要求の一致を示す。
`validated_binding_evaluates` は許可されたoptional metadata、型付きfallback、射影済みの適合入力から、
実際の束縛成功とpayload/fallbackのunion所属を導く。
**意味的なrequired≤optionalだけでは、必須fieldへのdefaultを拒否したことにはならない。**
sourceからmetadataを求めて全patternへ検査を適用するpassは残る。

### 網羅性の独立判断と実際のcase評価

`CaseCoverage` の `Cell` / `Total` / `Handles` / `Covered` は、checkerや評価成功を
前提にしない構造的な判断である。任意のdefault型表・arm列・入力domainについて、
`check_exact` は `check = true ↔ Covered`、閉じたmerged variant行について
`checkVariants_exact` は `checkVariants = true ↔ VariantsCovered` を示す。
`guarded_cons_ignored` によりguard付きarmは網羅性へ寄与しない。
bool、unit、tuple積、listのnil/cons、unionを分割する。これは値の有限サンプル検査ではなく、
任意の整数・文字列・任意長の有限listを含むdomainの全要素についての証明である。

`CaseCoverageSafety.check_matches` は、受理済みdomainの任意の値から、実際に合う
unguarded armを構成する。defaultの健全性は、arm構文に現れるコードだけに要求する。
`CaseDataProgram.typing_evaluates` は任意の具体的なprogram、型環境、default型表、結果型、
その独立な型付けと環境の `BindingsHold` から、評価結果が `.ok (some value)` となり
結果型を満たすことを示す。照合・guard・bodyの評価成功を追加の前提にしない。
`checked_evaluates` / `checked_variants_evaluate` では実行可能な網羅性検査で判断を充足できる。

variantの `residual_lookup` は、処理したtagを丸ごと除き、未処理tagのpayload全体をそのまま残す。
`residual_empty_iff` はこの残余の空性と独立な `VariantsCovered` を一致させる。
このcheckerは、一つのunguarded armでpayload全体を覆えることを十分条件としている。
この旧checkerの受理範囲は変更せず、回答済みQ8は次の拡張で扱う。

`JointCaseCoverage` は同一tagのpayloadを既存の構造的cellに分け、各cellを異なるunguarded armが
覆うことを認める。`checkTag_exact` / `checkRow_exact` は実行検査と独立な `TagCovered` / `RowCovered` を一致させる。
`old_check_preserved` は旧checkerの受理を保ち、bool payloadのfalse/true二armでtag全体を除ける。
`residual_lookup` は除去できないtagのpayload全体を残し、`residual_empty_iff` は空残余と `RowCovered` を同値にする。
guard付きarmとfloat literalは網羅性に数えない。`checked_program_evaluates` は旧scope非依存の
具体caseについて、独立なscrutinee/葉/armの型付けと検査成功・環境整合から成功する型付き結果を導く。
`ScopedJointCaseCoverage.typing_evaluates` はこのjoint被覆とQ4のscopeを同じ具体評価器へ接続する。
前提は独立なscrutinee/arm/data葉の型付け、各scopeのdefault型のdomain包含、名前の静的整合性、
独立な `RowCovered`、および任意の外側環境の型整合性であり、実照合成功を仮定しない。
boolとrecordのpairを持つ一つのtagをfalse/trueの別armで覆い、record内の先行束縛をdefaultが読む例を、
任意のbool・内側の整数・外側の同名整数について型付けと実結果の両方で示す。

**checkerのfalseは未認証であり、sourceの非網羅エラーとは同一視しない。**
例えば整数の `..0` と `1..` は任意の整数を覆うと証明したが、現checkerは受理しない。
recordのbool fieldをfalse/trueの二armに分ける場合、listを長さ0/1/2以上の三armに分ける場合も
現checkerの対象外である。`CaseCoverageBoundaryExamples` はこのrecord/list/整数の三例について、
checkerのfalseと任意の実値への意味上の網羅性を別々に証明する。
一般のRust pattern matrix・区間合併・再帰的な複数armの組合せは残る。
`RunCaseCoverage.lean` はguardとarmの訪問順、present/absentのdefault、nil/cons、
variant残余、二constructorを持つenumからのpayload束縛を実行する。
enumの例は解決済みの値からの分解であり、source構築子のelaborationの証明ではない。

### 有限構文木として入れ子になったcase

`CaseTree.Expr` / `Arms` は、caseをscrutinee・選ばれるbody・pair・letの内部へ再帰的に閉じる。
`CaseTree.typing_evaluates` は任意のfloat比較関数、型環境、有限式、結果型について、
独立な `Typing` と任意の適合する実行時環境から、実評価が `.ok (some value)` を返し結果型を満たすことを示す。
型判断は各caseの独立な `Covered` または `VariantsCovered` と、実際に使うdefaultの構文型付けを要求する。
scrutineeやbodyの成功は相互帰納法から導き、実行時の成功契約を外から仮定しない。
`checked_case_evaluates` / `checked_variants_evaluate` はcheckerの成功をこの判断へ接続し、
`typed_no_unmatched` は型付き式が全arm不一致で終了しないことを示す。

`CaseTreeExamples.nested_written_order` は任意の整数について、scrutinee内とbody内の両方にあるcaseが
その値を束縛・参照して返すことと、訪問列全体を証明する。
guard/default内の式はdata葉のままで、その内部のcase・関数再帰・application・effect・castは残る。
sourceの名前解決・束縛順・default環境を構文木に正しく割り当てる証明も含めない。

## Literal の中身と比較

`LiteralValues.Literal FloatValue` は任意精度の `Int`、decoded `String`、`Bool`、unit の中身を持つ。
整数の閉区間・片側区間の実行可能検査は、任意の上下端と literal に対して
独立な `InRange` 判断と同値である（`intRangeCheck_exact`）。
literal の `matchCheck_exact` は、任意の float 比較関数とその独立関係の正確性を前提に、
全 literal に対して実行比較と帰納的 `Matches` の同値を示す。
`FloatValue = Empty` の整数・文字列・bool・unit では通常の値の等号に一致する。

小数 token は符号・任意精度仮数・十進指数を保持する `DecimalToken` とし、
旧 `ofDecimal` は解釈関数を明示して渡す入口として残す。
回答済みQ2・Q3の具体値は `Binary64.Value` とし、符号1bit・指数11bit・仮数52bitを保存する。
`ofWord_toWord` と `toWord_ofWord` は任意の値と64bit wordの相互変換を示す。
有限値は最小subnormalの単位 `2^-1074` による符号付き整数として厳密に解釈し、
数値比較 `eqCheck_exact` をこの独立な意味と一致させる。
`signed_zeros_match` は正負のzeroが合うこと、`nan_never_matches_left/right` は
任意の相手についてNaNが合わないことを示す。保存値の等号とは区別する。
`LiteralValues.binary64MatchCheck_exact` はこの比較を内容つきliteralの独立判断に接続する。
`Binary64Rounding.roundFinite_correct` は、任意の符号・分子 `n`・正の分母 `d` について、
絶対値が最大有限値以下という前提から、二分探索の結果が全有限binary64候補に対して
厳密な距離 `|n - units(candidate) * d|` を最小にし、異なるrankとの同距離では
fractionの下位bitを偶数にすることを示す。符号はzeroへ丸める場合も保存する。
`n/d` は `2^-1074` 単位の絶対値であり、有限サンプルとの比較ではない。
`Binary64Decimal.magnitudeFraction_exact` は任意の小数tokenを厳密な有理数へ変換する。
`convert_success_iff` は実装の成功を「厳密な絶対値が最大有限値以下」と同値にし、
`convert_correct` は任意の成功結果について上の全候補への丸め契約を導く。
`LiteralValues.binary64OfDecimal_correct` が具体的なfloat literalへ接続する。
この部分converterは範囲外を内部の `outsideFiniteRange` として区別する。
回答済みQ11のsource規則は、最大有限値を超えても丸めが有限なら受理し、無限大へのoverflowを静的errorにする。
`Binary64Overflow.finiteRounding_iff_exists_value` は任意の符号・分子・正分母について、
拡張した指数grid上の全候補に対する最近接偶数丸めが有限値を持つことと、
絶対値が厳密に `2^1024 - 2^970` 未満であることを同値にする。
境界ちょうどは偶数rankの上側sentinelへ丸まり、最大有限値以上かつ境界未満なら最大有限値へ丸まる。
sentinelは数学的な次の2冪であり、無限大に有限の距離を割り当てるものではない。
`round_agrees_with_finite` は旧成功範囲で旧丸めと全称的に一致することを示す。
`Binary64SourceDecimal.convert` はこの境界を全decoded tokenへ接続する。
`convert_success_exact` と `convert_overflow_exact` は、任意tokenについて成功／静的overflowと
独立な全grid最近接偶数の有限結果の存在／不存在を同値にする。
成功時の符号・有限性・非NaNを保ち、`convert_agrees_with_old` は旧converterの任意の成功値をそのまま保持する。
`LiteralValues.binary64SourceOfDecimal` はこの全域入口をfloat literalへ写す。
`RunBinary64.lean` は0.1、2^53付近の両方向のmidpoint、subnormal境界、最大有限値、zero/NaNを実行する。
新しい `RunBinary64Source.lean` とkernel内の回帰定理は、両符号について最大有限値を超えた
`1.7976931348623158e308` の受理、midpoint直前の受理、midpoint一致・直後・`1e309` の拒否を確かめる。
旧runnerと期待値は変更していない。
極端な非零十進指数の資源使用量の最適化とRust f64との対応は残る。
既存 `Inference.Base` に float はなく、`legacyBase` は float に `none` を返す。
旧 base-marker 評価器を具体 literal 評価器へ黙って置き換えていない。
字句解析・escape の正しさ、数値演算、source への翻訳はこの定理群の対象外である。

## Nominal構築・保留cast・listの観測

`CaseDataTerms.Expr.nominal typeId ctorId payload` はpayload式をstrictに評価し、
結果を解決済みのtype/constructor identityで包む。独立な `Typing.nominal` と既存の
`typing_evaluates` がこの構築にも適用される。structのrecord fieldを式から計算する例、
enumのlet/var payload、listのnil/cons構築について、任意の整数の値と訪問列全体を
`NominalDataConstructionExamples` で証明した。宣言のlookup・固定fieldの宣言型・default・castのelaborationは含めない。

`NominalConstructionRuntime` は決定25の既存planに保留された不変parameterの元の構築位置を、
元の順に評価して `PureCasts.Plan` の純粋な変換を挟む。適合する位置では変換を呼ばない。
`accepted_requestTree` は任意のruntime・registry・construction・expectation・受理planについて、
実行のrequest treeが元の引数列を順に読むrequest treeと等しいことを示す。
全response分岐、payload、正負の重みを保持し、返り値そのものの等号はこの定理の結論ではない。
`execute_eof` は全parameterの期待型が未解決の場合に変換せず、元の実値を保つ完全な計算等号を示す。
constructor identity・enum tag・構築位置・引数個数も保持する。

`runValues_typed` は元の値の型付け契約と変換コードの値型保存契約を別に必要とする。
registryのground境界検査から正しい変換コードを合成する証明は未完であり、
`finish` の受理だけからtarget型の構築値が得られるとは主張しない。
`NominalDataAssembly.execute_runtime` はsite実行器の結果を具体 `CaseDataTerms` 構築ASTへ渡すことを
完全な計算等式でつなぐ。`accepted_requestTree` は受理planについて元の全siteの要求を保ち、
`execute_eof` は未解決parameterで元値を変換せずassemblyへ渡す。
`typing_evaluates` はplan受理・元siteの型契約・明示 `CastContract`・独立なassembly型判断から、
返る各分岐でmetadata保存、具体ASTの評価成功、結果型への所属を導く。
適合境界のidentity保存と、許可された非適合境界のpure codeの型保存をcontractとして要求する。
隠れるstruct fieldも要求を残し、実際のstruct/enum/list値を構築する等式を含む。
sourceからsiteとassembly codeを作るpass、固定field/defaultの宣言検査、cast code合成は残る。

`NominalListSpread` は解決済みの有限listについて、通常要素と任意位置のspreadを記述順に評価する。
通常要素の純粋変換は明示的に受け取り、spreadは既に型付けされた内容をそのまま連結する。
`data_typing_evaluates` は独立なsource型判断・環境適合性・変換の値型保存契約から、
各sourceの訪問列を一度ずつ左から右へつなぎ、全要素が指定型に属する実listを得る。
`data_typed_views` は同じ前提から、具体list値・nominal metadataを持つ構築結果・Fold順序・
全自然数位置のcursorと内部Indexが同じ要素列を観測することまで導く。
空spread・連続spread・途中のspreadでも順序と重複を保ち、source失敗後は後続を評価しない。
回答済みQ13・決定45は任意のFold値をsource spread対象とし、forと同じ辞書・effectを使う。
一般の走査と要素型union、非停止を含む実行は下記の解決済みprotocol核へ接続する。
sourceの高階Fold本体からこの核への意味保存と推論全体への統合は残る。
既存listの各要素へ新しい保留cast位置を作るか（Q14）は未回答である。
sourceのsite抽出・変換選択と保留planへの自動接続も残る。

`FoldTraversal` は任意stateの走査protocolをdone・内部step・yield・operation別のrequestで表す。
有限collectionや終了を仮定せず、各requestのsigned occurrence・payload・response別継続を保つ。
`prefix_safe` は任意の局所安全性契約・有効な開始state・有限prefixから、終端stateの不変条件、
全yield要素の型、全requestの行への所属を導く。`progress` は未回答requestも正当な停止位置として区別する。
`repeat_safe`・`repeat_prefix`・`repeat_never_done` は任意個数の安全なyieldと非終了を同時に許す。
`selected_driver_exact` はrigid role検査の成功から得た一意な辞書planが、供給された実装tableの
同じdriverを選ぶことを示す。tableのmethod実装が正しいことは別の契約である。
既存forの純粋cursorとの一歩の一致もあるが、高階でaccumulator多相なsource `Fold.fold` の
method本体からこのprotocolを作ること、そのcallback/effectの意味保存は残る。

`FoldListSpread` はsource評価の開始・内部step・requestと、選択済み辞書の走査を一つのmachineにする。
各partの独立な型判断が通常要素の型、spreadのitem型、source行、走査行を持ち、
`typing_union` が全partの要素型と行のunionを構成する。
`typed_prefix` と `typed_prefix_progress` はsourceと辞書の局所不変条件、純粋変換契約、
独立なpart列の型判断から、任意の有限prefixの型・行保存とtypedな次の観測を導く。
sourceもFoldも有限であることや全体の成功を仮定せず、返る場合の全要素型は `returned_items_typed` が導く。
`traversal_prefix` は途中の任意prefixでも後続sourceを保持し、yield列だけを元順で結果列へ追加する。
`meaning_prefix` は各sourceとFoldが有限に完了した独立な実行判断から、記述順の合成を示す。
これは終了の型定理ではない。`FoldListSpreadFinite.finite_run_correspondence` は任意の
旧 `NominalListSpread.Meaning` の導出から、旧runの結果と新machineの返却値が同じflatten列であること、
旧source traceが同順・同回数の `raw (inl event)` の要求列として観測されることを示す。
この有限実行の対応だけが成功した各sourceと有限走査を使い、一般prefix安全性の前提にはしない。
観測eventと既存errorの埋め込みは抽象signature上のもので、sourceのoperation名を追加しない。
`typed_finite_run_correspondence` は旧独立型判断・SourceSound・純粋変換契約からこの有限対応を導く。
`data_typed_finite_run_correspondence` は任意の具体 `CaseDataTerms` 型判断・環境適合性・変換契約から、
旧evalの成功と全要素型、新machineの同一返却列と同じsource traceを導く。
具体data版ではSourceSoundと実行成功を呼出側から受け取らず、既存の型安全性から充足する。
`FoldListSpreadRoles.Slot` はcontainer/itemのrigid termと、供給されたFold goal encodingに対する
`CheckedRoles.resolve` の成功を持つ。`spread_typing` は任意の型付きprotocol registry・局所SourceLayer・
slot・container型を持つsourceから、slotのitem型とsource行/選択body行のunionを持つ実際のspread型判断を導く。
`engine_uses_selected_dictionary` は同じgoalの任意の独立なDictionaryについて、driverと宣言行が一致することを示す。
registry内のbodyは開始stateと局所 `Safe` の契約を持ち、role受理だけからmethodの意味を仮定していない。
Fold goalのsource encoding、source methodからのregistry生成、実際の `for_in` との意味保存は残る。
`FoldListSpreadDivergence.no_later_source_or_return` は任意の辞書・後続構文・有効state不変条件について、
局所 `Safe` と全有効stateでdoneにならない条件を前提に、任意の有限machine prefixでも
同じ辞書と後続構文が走査中に保たれ、どのlist値も返さないことを示す。
独立に型付けされた `[3, ..repeat 7, 11]` の解決済み例では、repeat段階へ到達した後も
型安全性を保ち、後続の11を始めず返却しない。停止を型安全性の前提にはしない。

`NominalListViews.index_exact` は任意の有限list・自然数位置・要素について、内部lookupの成功と
独立な位置判断 `At` を同値にする。`cursor_index` と `fold_records_order` により、
Indexの内部lookupとFold用cursorが同じ順序の要素を観測する。`loopMachine` は既存loop評価器へ同じcursorを渡す。
回答済みQ9・Q10に対応する `NominalListIndex` は任意精度整数を受け取り、
`integerIndex_some_iff` により成功と `0 ≤ i < length` を同値にする。
負数は末尾相対にせず、`integerIndex_cursor` が非負indexと同じFold cursorの観測を保つ。
`effectIndex` は無効indexを既存の非再開error要求に変え、`wrap_effectIndex` が通常の
error wrapperで成功値または指定された範囲外errorが得られることを示す。
汎用定理は任意の `ErrorEffects.Encoding` と `Int → Error` を引数に取る。
回答済みQ12は `error index_err: out_of_range int` と無効だったindexのpayloadを確定した。
`NominalListIndexError` は任意の外部signatureと直和を取り、PayloadがInt・ResponseがEmptyの
一つの解決済みoperation、`Cases`、正しい `Encoding` を具体化する。
`invalid_index` は任意の無効indexについて、負・空list・上限超過のいずれも同じoperationへ
元のIntをそのままpayloadとして渡すことを示す。`invalid_bind` は後続を実行しない。
`wrap_index` と `catch_index` は通常返却／範囲外armへの完全な計算等式を持ち、
wrap後は空行、catch後は明示されたarmの行で全要求が上から抑えられる。
source文字列・宣言identityからこのfamilyへの対応、role辞書選択・Index本文のelaborationは残る。
`RunLiteralConstruction.lean` で大きな整数・範囲比較と実際のstruct/enum/list構築を実行できる。

## 複数 operation の shallow handler

回答済みQ1に対応する `MultiOperationPayloadHandlers` は、同一keyを複数回書ける
順序付きpayload armを追加する。実際のdispatchは最初に合うarmを選び、行から引くkeyは
guardなしの反駁不能armがあるものだけとする。`missed_retained` と `partial_key_retained` は
照合できない要求、またはその証明を持たないkeyの出現が残余に残ることを示す。
`handle_selected` は捕捉armへ元の継続を渡し、`handle_missed` は元の要求・payload・重みを
外に保ち、再開後に未完のhandlerとvalue armを続ける。`handle_ofOperations` により旧全域表は特別な場合になる。
許可maskは全armのkeyへ検査する。純粋payloadテストと純粋guardの解決済み層であり、
effectfulなpattern default/guard・source束縛のelaborationは示さない。

`Expr.partialHandler` はこのdispatchを既存の構文核へ接続する。
出力行は `residual removedKeys action.row` にvalue bodyと全operation bodyの行を加えたものとなる。
`MultiOperationHandlerTyping.infer_exact` と `typing_evaluates` は入れ子のpartial handlerも含む
同じ量化された主張を保つ。`eval_total_as_partial`、`infer_total_as_partial`、
`typing_total_as_partial` は旧全域表との実行・checker・型判断の一致を示す。
`MultiOperationPayloadInference.infer_exact` は明示incoming maskを全armに検査するwrapperと
独立な型判断を一致させ、`inferred_operationally_valid` は推論成功と整合する外部環境から
評価の全response分岐の安全性を導く。不許可keyは到達不能なpayload armでも拒否される。

`MultiOperationHandlerTyping.Expr.handler` は、相異なる解決済み operation key の有限表、
各 operation body、1つの value body を持つ。ordinary application は左から右へ strict に評価し、
再開する継続には action の元の行を保つ。`MultiOperationHandlerTyping.infer_exact` は
全ての解決済み式・型環境・出力型について、実行可能 checker の成功と独立な `Typing` 判断の同値を示す。
`typing_evaluates` は、その型判断と開いた環境の `EnvValid` から、全 response 分岐の request 上界と
返り値の型を導く。action/arm ごとの実行時上界を追加の前提にしない。
閉式の行が空なら `closed_empty_row_returns` により、対応する型の値へ返る。

`MultiOperationHandlers.checkedIncoming` は incoming action 用の別入口である。
許可 mask にない key の arm があれば拒否し、`checkedIncoming_success_iff` は
全 key の許可と実行結果の等号を成功の必要十分条件にする。
一般の非零の符号付き重みを保つ forwarding と、許可された raw 要求の dispatch を証明した。
通常の checker が source から mask を発見することはまだ示していない。

`MultiOperationIncomingInference.Handler` は明示されたincoming maskを同じtop-level handler構文に付ける。
その `infer` は許可検査の後に既存の構文checkerを呼び、独立な `Typing` との同値を `infer_exact` で示す。
任意の型環境・handler・armについて、不許可keyが一つあれば `denied_arm_rejected` が拒否を導く。
`inferred_operationally_valid` は推論成功と外部環境の型適合性だけから、実構文の評価の `Valid` を導く。
action/armのruntime上界は仮定しない。pureなactionでも不許可armがあれば拒否する実例を含む。
`inferred_opens_incoming_gate` は同じmaskとoperation表のgateが開くことまでの対応である。
構文評価と `enterTree` を施した実行の等号はまだ示しておらず、
fresh座標への構文・closure・潜在行の移送、arm側を境界の外に保つ意味保存は残る。
入れ子のhandlerへのmask割当てもこのtop-level wrapperの範囲外である。

`MultiOperationHandlerExamples.nesting_not_equivalent` は任意の境界座標数について、
operation 0 の元の継続が operation 1 を要求する具体例を分離する。
一つの handler では 0 の捕捉時に両 arm の delimiter が外れ、1 が外へ出る。
singleton handler の入れ子では外側の 1 が残り、同じ arm が 99 を返す。
従って operation ごとの入れ子化は一般に意味を保存しない。

この核の payload/response は既存の一様な `Atom` carrier である。
source の名前解決、payload patternから解決済みarm表と束縛への翻訳、operation-local 多相署名、
source から mask を求めて checker に渡す elaboration は残る。
回答済み [Q1](../notes/questions/2026-11-06-open-questions.md) の残余規則は上のpartial handlerへ反映した。
旧 `Operations` 表のkey一意性は旧核の表現条件であり、新しいpayload arm表には要求しない。

## Presenceと旧required-field推論の橋

[統合の工程案](../notes/design/2026-11-06-presence-inference-integration.md)を追加した。
`PresenceLegacyBridge.translate` は任意の有限legacy型・hidden label列・旧data値について、
旧 `DataTypeSemantics.Holds` と同じ意味を持つpresence述語を構成する（`translate_exact`）。
旧 `{}` は `records` のままであり、exact emptyやfield不在には変えない。
隠れたfieldはunion/intersectionを含むtailの中でも要求を足さず、
任意のShadow部分型導出は翻訳後の包含を保存する（`shadow_subtype_preserved`）。

`closed_typing_translates` は任意の行代数・supportedな閉data式・raw Shadow型判断について、
同じ式の返り値型をpresence判断へ移す。評価成功は仮定しないが、effect行の移送は結論していない。
`legacy_data_plan_translates` は任意の行代数・式・受理されたfinite-data planについて、
一つのpresence推論結果が存在し、そのexact型が、旧planの**任意の自由parameter代入**から得る型の翻訳に含まれることを示す。
parameterの個数は有限だが、代入する有限raw型を有限候補へ制限していない。
このplanは `RigidRecordValueInference` のもので、regularな `SourcePrincipalInference` のschemeではない。

`PresenceLayers.Layer` はrequired・optional・不在を別々に持つ有限の型層であり、
union/intersectionの全構造を残してfield間の相関を保つ。子parameterは任意のdata述語へ割り当てられる。
`Layer.check_exact` は任意の割当てとそれに正確な子membership checkerについて、
任意のlayer・実値の所属判定を独立な意味と一致させる。部分型判定や全述語の決定可能性は主張しない。
`mask_exact` / `meaning_mask` / `record_shadow` は任意のmaskとtailについて隠れた同名fieldの要求を消す。
`independent_fields_lose_correlation` はfield別のoptional化が元の二field間の選択肢を広げる反例である。

`PresenceRegularObservations.check_exact` は任意のgraph・全有限深さ・全state・全data値の観測を判定する。
`observe_morphism` / `subtype_morphism` はgraphと可換な任意のrenameについて保存・反映を示す。
renameの単射性は要求しない。`Blocks.close_observe_exact` / `close_subtype_exact` は
任意の有限同時再帰blockと内部・外部rootについて、閉じる前後の全有限観測を保つ。
`PresenceRegularLegacyBridge.observe_exact` / `layer_exact` / `data_subtype_exact` は旧regular graphの
全有限data観測と新しいpresence観測を一致させ、`legacy_block_observe_exact` が既存common carrierのblockへ接続する。
ここでの包含はdata述語間のもので、旧structural subtypingや関数・行の意味の同値ではない。

`optional_iff_absent_or_required` と `optional_never_iff_absent` は既存述語の意味から無条件に成り立つ。
旧width型からabsenceやexact emptyは導けない反例も保持する。
旧runtimeのliteralはbase markerで、関数型の翻訳はdata上ではneverである。
regular再帰型のdata投影の橋は上で与えた。内容つきliteral・closure・自由row parameter・全source主型推論への一般化は残る。

旧 `SourcePrincipalInference.infer_instances_exact` は任意の行代数と行順序の反対称性の下で、
任意の `supported e = true` の入力について成立する。`RecordFree` はsupportを構文から保証する十分条件であり、
inferの必要条件ではない。optional構文のunsupportedを型エラーへ変える変更は加えていない。

## 決定42–44：評価順とspread-first record

元の `Inference.Expr` に `recordDefault label base fallback` を追加した。
`SourceDataRuntime.eval` は `base`、`fallback` の順に両方を評価してから、
baseのfieldが存在すれば保持し、なければfallbackを末尾へ追加する。
`Fields.lookup_insertDefault_same` は結果の同名fieldを
`(lookup label fields).or (some fallback)` と特徴付け、
`lookup_insertDefault_other` は他のfieldの保持を示す。
baseの評価が失敗すればそこで止まり、baseが非recordの値まで評価された場合は
fallbackを評価した後で `expectedRecord` とする。field選択による式の省略はない。

`SourceDataOrder.Evaluates` は実行関数を参照しない独立な帰納判断である。
子式への進入、左右の成功・失敗、最後の値操作を別規則にし、失敗前の訪問も保持する。
`evaluates_iff_run` はtraced実装との双方向対応、`runtime_iff_evaluates` は元の
`SourceDataRuntime.eval` との双方向対応を示す。`Evaluates.successful_order` は
成功時に構文の全訪問列が書いた順に一致し、`run_trace_prefix` は失敗時もそのprefixだけを
訪問することを示す。`EvaluationTrace` の値を捨てるsequencingの補題は、先に生じた
観測を消さない。このdata評価器自体はeffect operationを実行する評価器ではない。
`SourceDataOrderLaws` はhidden fieldの成功と失敗、present/absentなdefault、既存fieldに
隠されないfallbackの失敗、未使用letの右辺、二回読まれても一回だけ評価されるletを扱う。
`lake env lean --trust=0 --run RunSourceDataOrder.lean` で実際の結果と訪問列を確認できる。

従来の `Inference.Model` / `Typing` / `generate` はrequired-field用の体系で、
optional-fieldやfield不在の型を持たない。この判断での `recordDefault` は未対応であり、
`Expr.requiredFieldsOnly` と `SourcePrincipalInference.infer_optional_unsupported` により
旧solverは入れ子の新構文も `unsupported` とする。これを言語の型エラーとは扱わない。
既存の `{}` は引き続き任意のrecordの上界であり、exact emptyへの読み替えはしない。
以下の旧主型定理・全core graph対応は、このrequired-field判断についての主張である。

### presenceを区別するdata推論の閉じた主定理

`PresenceDataTypes` は実際のdata値上の述語を型、包含を部分型とする。
`required` / `optional` / `lacks` を別の述語として定め、`records`（旧 `{}` の意味）と
`exactEmpty`（ちょうど空の値）を区別する。`records_not_le_lacks` /
`records_not_le_optional_int` は、幅の上界だけから不在や任意のoptional payload型を
推論できないことを反例で示す。旧Shadow部分型関係の定義を変更していない。

`PresenceDataInference.infer` は元の `Inference.Expr` に対するtotalな実行可能入口である。
変数・literal・非再帰let・pairと射影・record・default・field・variantを構文再帰で合成し、
有限の型descriptor `Shape` を返す。評価器は呼ばず、type-level lookup/insertionを使う。
`Typing` は算法も評価器も参照しないconstructor/subsumptionの独立判断である。
`infer_instances_exact` は任意の式 `e` とこのdata意味論の任意の型 `T` に対して
次の同値を証明する。

```text
Typing [] e T ↔ ∃ shape, infer e = solved shape ∧ shape.denote ≤ T
```

callerが推論成功やsolverの解を前もって渡す必要はない。`infer_success_iff` は推論成功と
型付け可能性の同値、`infer_rejected_iff` は対応するdata構文上での拒否と型付け不能の同値を
示す。関数・application・branchは `unsupported` と区別する。
この主型はfieldの不在まで記録する新しいdata意味論の精密な型であり、旧型grammar上の
全core自由parameter主型を求めたという主張ではない。literalは引き続き既存ASTのbase tagである。

`PresenceDataSafety.typing_evaluates` は任意の型適合する実環境で実際の
`SourceDataRuntime.eval` が成功し、その値が指定された型を満たすことを示す。
`inferred_evaluates` は実inferの成功だけから同じ保証を得る。
`default_operator_principal` は実AST `recordDefault l (var 0) (var 1)` について、
任意のbase型 `R`、fallback型 `B`、結果型 `T` を量化し、`R ≤ records` の下で
`Typing [R,B] ... T ↔ recordDefault(l,R,B) ≤ T` を証明する。
したがって未知baseの契約も既知の有限record例に限られない。
`optional_operator_principal` / `optional_operator_union` は `x?: A` のbaseから
必須field `x: A | B` を導く。known-presentでは元のpayload型、known-absentではfallback型を
保持し、他fieldのlookupも保存する。fallback式自体はどの場合も型付け・評価される。

`lake env lean --trust=0 --run RunPresenceDataInference.lean` はpresent/absent、computed base、
非recordの拒否、隠れるfallbackの失敗、unsupportedとrejectedの区別を実行する。

`PresenceDataCompatibility.eval_success_iff_synth` は任意のexact descriptor環境と元Exprに
ついて、別々の算法である型合成と実評価の成功を双方向に一致させ、返り値の等号も証明する。
`infer_rejected_iff_eval_error` は支持されたdata構文について拒否と実行時エラーを同値にする。
新推論器が評価器を呼ぶ定義へ変更したのではなく、独立な構造再帰同士を帰納法で接続した。
`shadow_typing_infers` / `shadow_quotient_typing_infers` / `shadow_principal_infers` は
以前のraw型付け・商型付け・principal formulaの解から、新inferの成功と旧targetの値意味論を
導く。`shadow_plan_infers` は一つの同じ新推論結果の値が**全ての旧parameter instance**を
満たすことを示す。型宇宙・部分型関係・主型の定義を同一視する定理ではない。

決定43の一般的なstrict引数評価と、歴史的な `OperationalTyping` のcomputation引数渡しは
区別する。`OperationalTypingExamples.unusedArgument_eval` は未使用の引数を実行しない
旧模型の定理であり、現在のsurface言語の評価順を証明するものではない。
`StrictApplication.compile` はresolvedな式を再帰的に走査し、関数の評価、引数の評価、
適用という順を二つのcomputed letで表現する。de Bruijn変数のshiftを含めて
`compile_correct` が独立なstrict評価器との実行木全体の等号を証明する。
lambda本体・handler両arm・返された関数・継続・符号付きweightも対象である。
`infer_forceApplication` は結果行が関数の行、引数の行、戻りの行の順で合成されることを示す。
行の包含自体は順序を観測しないため、評価順の保証はこの行上界ではなく実行木の等号による。
`closed_inferred_bound` / `closed_inferred_values` は実checkerの成功からstrictな実行の上界と
返却値の型適合を導き、`unused_argument_bound_iff` は任意の未使用引数の要求を保持する。
`StrictApplicationPrincipal.principal_operationally_valid` は実際にloweringした式の
既存principal formulaの解から同じ実行保証を導く。shape解決、注釈、surfaceの境界挿入や
この一般formulaの求解を完了したという主張ではない。

## errorのwrap・upとsignature付き要求木

`SignatureRequests.Tree` はoperationごとにpayload型とresponse型を持ち、既存の
`Directed.Occurrence` とcapture判定をそのまま使う。`toDirected_ofDirected` /
`ofDirected_toDirected` と `ofDirected_shallowHandle` は、uniform signatureの場合に
旧要求木との双方向同型と実shallow handler全体の等号を示す。

`ErrorEffects.Cases` は宣言のoperationとerror値のconstructorを対応させる。
error operationのresponseは `Empty` へ写せるため、`up_captured` は元の継続を使わずに
変換先のabortive requestを構成する。任意の結果型の値を捏造しない。
`raise_bind` はerrorの後のコードへ進まないこと、`wrap_returns` は全要求が捕捉可能な
当該errorである任意の入力木から実際にresultを返すことを示す。
`wrap_up_exact` は宣言keyの非重複とconstructorの対応だけから、任意の木について
`target.wrap (source.up action)` と直接の `wrapFrom` が一致することを示す。
外部のeffect、保護された要求、負のweightは転送される。
複数の直接の `from` は対応表の合成で扱う。nominal宣言のelaboration、推移的なfrom探索や
複数経路の選択規則はここで決めない。要求木はwell-foundedであり、一般再帰の停止定理ではない。
このhelperの入力は計算の要求木であり、ordinaryなstrict applicationへそのまま写した値引数とは
同一視しない。actionのeffectがhandlerの外で先に起きないようにするsurface展開と、その型・実行の
対応は未接続である。`StrictApplication` とこれらのhelperを個別に証明しただけで、両者を統合した
source elaborationの正しさまで得られたとは扱わない。

## junctionの短絡とmulti-shot実行

`JunctionEffects.run` はsignature付き要求木上で、`or` / `and` の継続をまず `true` で
再開し、必要な場合だけ同じ継続を `false` で再開する。`ret` はBoolを返して脱出する。
`run_is_shallow` は既存shallow handlerとの等号であり、継続を再度包む処理がlibraryの
armに明示的に存在することを示す。kernelの継続を暗黙にdeepへ変更していない。
`disjoin_short_circuit` / `conjoin_short_circuit` は短絡、`run_external` / `run_nonzero` は
外部effect・保護・負のweightの転送を実行木の等号で示す。
`closed_returns` は全要求が捕捉可能なjunctionである任意のwell-foundedな入力木について
Boolへの実終了を導く。`run_any` / `run_all` / `run_all_any` は任意の有限リストと述語に対し、
計算結果が `List.any` / `List.all` およびその入れ子と一致することを示す。
`lake env lean --trust=0 --run RunEffectExpansions.lean` はerrorの変換、短絡で飛ばす枝、
false枝へ進む順序、外部観測と保護された要求を実行する。
effectfulなsurface `if` をこのhelperへ包むelaborationとsource再帰の停止性は別の義務である。

## for・last・next・redoの有限実行

`LoopEffects` はlabelなしのloop展開を、同じsignature付き要求木上の小ステップmachineで
記述する。任意のcursorによる要素選択と外部effectのinterpreterを明示的なparameterに持つ。
独立な `Step` / `Pending` / `Prefix` と実際の `step` / `run` の一致を
`step_progress_iff` / `step_blocked_iff` / `prefix_iff_run` が証明する。
fuelは観測する有限step数であり、型付けの前提や言語の停止仮定ではない。

`run_last` はUnitで終了し、`run_next` は残りcursorへ進み、`run_redo` は同じ要素のbodyを
先頭から再設定する。いずれも操作の古い継続は再開しない。
`external_then_redo` は外部effect後の**現在のstateとevent**を保持したまま再開することを
示す。`run_add_exhausted` は予算を追加して現在のconfigurationから続きを実行した結果が、
初めから合計予算で実行した結果と一致し、過去のtraceをappendで保持することを示す。

`normal_finite_traversal` は明示された有限 `Traverses` とpureな各bodyの下で、長さから
計算した予算 `2 * length + 2` によりUnitへ終了することを証明する。
`redo_forever` は逆に、有限bodyでもすべてのfuelで予算切れとなる例を証明する。
一般のfor/redoの停止性を主張しない。保護されたloop要求や応答のない外部要求は元の
configurationを保って中断する。外部interpreterへsigned occurrenceを渡すが、その
interpreter自身のmask適合、effectfulな `Fold`、label値のsource束縛・method・衛生性と
入れ子loopを含むsource elaborationはこのmodelの外に残る。
`lake env lean --trust=0 --run RunLoopEffects.lean` はstateを更新してredo→next→lastと進む
実例、途中からの再開、abort後の未実行、保護された要求、有限走査と無限redoを確認する。
評価順・presence推論・error/junction・loopの4 runnerもCIへ追加した。

## 決定40：隠れたfieldの型等価

`ShadowSemanticRecords` は決定39の全規則を保持し、任意のtail `R` について
`record(l,A,record(l,B,R)) ≃ record(l,A,R)` の両方向を追加した最小関係である。
`Subtype.minimal` がこの規則範囲を特徴付ける。一般のtail共変性や分配則は加えていない。
`ShadowRecordQuotient.shadow` は、任意の商型のhead・hidden payload・tailについて、
この等式が実際の型の等号になることを示す。`int` と `str` は引き続き異なる。

`ShadowRecordInference` は以前の型付けを保存する。`ShadowRecordQuotientInference`
の `formula_exact`・`closed_typing_exact`・`compiled_typing_exact` は、任意の元core式・
結果型と行について、新しいraw関係、商、実際の全core graph出力を接続する。
`ShadowRecordExamples.source_has_equal_instances` は、10.28.3で分離されていた
同じsource式の二つのopaqueな結果を保持した上で、その商型が等しいと証明する。
unionと`never`で隠れた重複も `shadow_under_union_bottom` が扱う。

旧 `Rigid*` 関係とその否定定理は、決定39時点の比較用として変更せず保持する。
以下で記すopaque結果の別型性はこの旧関係についての事実であり、決定40後の言語の
区別ではない。新関係の有限ground checker・cut elimination・商の等号判定も下記の通り完成した。
未知変数を持つ一般graphの求解と全coreの自由parameter主型推論は未完である。

`ShadowRecordNormalization.normalize_exact` は、計算された正規化結果どうしの旧rigid関係と、
元の型どうしの新関係を双方向に一致させる。`normalize_equivalent` は各正規化結果が元の型と
新関係で等価なことを別に示す。tail全体が同名headを持つrecord atomと旧関係で等価な場合だけ
headを除き、残りtailのconstructor depthが真に減る。unionの枝ごとの消去や分配則を加えていない。

`ShadowRecordChecker.check_true_iff`・`check_false_iff` は任意の有限型に対する実判定の
完全性を示す。前提は正確なBoolean行checker・行preorder・`DecidableEq Row` である。
`cut_elimination` は新関係のcutを計算済みnormal formsの既存cut-free判断へ接続する。
`ShadowRecordQuotientDecisions.equal_true_iff`・`decideEq` は実際の商型等号を判定する。
外部fuel・新関係の意味的oracle・未知の中間型は渡さない。表示用のcanonical文字列や
正則再帰値型のcheckerを構成したという主張ではない。

```sh
lake env lean --trust=0 --run RunShadowRecordCheck.lean
```

## 全coreのrecord要求と正則モデルへの接続

`ShadowRecordDemands.record_mask_exact` は、任意の供給head `A`・tail `R` とrigid要求 `P` について、
`record(l,A,R) ≤ P` を、要求に `l:B` があれば `A ≤ B`、および `R ≤ erase(l,P)` と同値にする。
新しいshadow規則を含む導出全体から必要性を証明し、十分性も実際の規則から導く。
行の法則、供給tailの形、決定可能性は前提にしない。

`SingletonRecordDemands.good_generate` と `SingletonRecordGraph` は、元の全core式で、
生成される要求の明示的なrecord spineが空かsingletonになることを示す。
lambda・application・両let分岐を含み、rename・scheme置換・normalise・pack・prepare・
実際の `compileSource` まで保存する。閉式では環境の不変条件を空環境から証明する。
未知slotに代入できる型をsingletonへ制限するものではない。
任意の外部schemeでは強めた `GoodEnv` が必要で、旧前提だけでは足りないことも反例で証明する。

`maskReference` と `compileSource_erasure_closed` は、残りの要求が元のnodeか既存のempty-tail
nodeへの参照になることを示す。`compileSource_upper_record_tail` はprovenanceだけでなく
actual graph tagがemptyになることまで導く。追加の型変数やmask nodeを確保する必要はない。

`RecordDemandInspection.inspect` はそのnode tagを直接読み、同名fieldならhead比較とtailの
empty要求、別名なら元tailへの同じ要求を返す。未対応pairは拒否せず元の辺を保持する。
`expand_exact`・`expandCompiled_instances_exact` は、同じvalue/row割当てと共有slotを保ったまま
制約集合と全instanceを双方向に一致させる。`SourceRecordDemandInspection.prepareSource` は
実際の全source alternativeへこの一回の分解を適用する。

`ShadowRegularValueTypes` は既存 `Layer`・graph・観測関数を保持し、各有限観測の比較に
決定40の関係を使う。任意の既存Layer tailでshadow等価・合同性・rigid要求への共変性が成立し、
`finite_conservative` は有限treeの比較を保存・反映する。共通carrierの
`ShadowRegularInferenceModel.embed_subtype` も `iff` であり、finite blockの埋込みも正確である。
`SourceRecordDemandInspection.shadow_source_typing_exact` と
`shadow_regular_source_typing_exact` は、分解後の全graph instanceと、それぞれのモデルでの
元Typingを一致させる。両方にgraphの `Models` 条件が残る。

**全core solverへの残る義務は、分解を含む飽和と、open-tail graphから自由parameterの
正則解を構成するcoalescingである。** 既存 `Layer.record` のtailは有限Layerであり、
graph-state参照ではない。一般のtail参照をそのまま既存blockへ写す証明はなく、
全parameterでの充足と任意の元解へのretractionを新しい関係で証明する必要がある。
これはtail-cycleが解を持たないという主張ではない。旧solverの新関係についての完全性や
`RecordFree` の除去は、この接続だけからは導かない。

## 最新record関係でのデータ推論

`ShadowRecordValueInference` と `ShadowRecordValueQuotient` は、既存の
`RigidRecordValueInference.infer`・`Plan`・自由parameter tupleをそのまま使い、
決定40のraw関係と商モデルで全instance主型性・拒否完全性を再証明する。
`infer_complete` は型付け可能な任意の `Data` 式で実際の推論が成功することを、
`infer_instances_exact` は推論したschemeの全instanceと独立な元Typingの一致を示す。
以前の型付けの保存だけでなく、新しい等式で増えた型付けも完全性の対象とする。
`inferred_boundary_instances_equal` は以前のopaqueな両instanceを同じ商型として保持する。
対象はliteral・emptyRecord・pair・variant・record構築と、不正なdata tailである。
一般lambda/application・let・effect式はこの推論入口の対象外である。

`ShadowRecordFunctionScheme`・`ShadowRecordFunctionQuotient` は、以前の
`lam (record l (lit b) (var 0))` の同じdescriptorについて、決定40後の全instance主型性を
再証明する。自由な3個の値型と1個の行を保ち、opaqueな入力tailも含める。
これは当該関数族の推論schemaであり、一般関数の新しいdispatcherではない。

## 元の型付け・推論結果から実際の評価へ

`SourceDataRuntime.eval` は元の `Inference.Expr` と実行環境だけを受け取る。
shapeで添字付けされた式、型付け導出、推論plan、fuelを渡さない。recordは実際の有限field列で、
同名の古いfieldを保存データから消す。headとtailはその消去前に両方評価する。

`SourceDataSafety.typing_evaluates` は、変数・literal・pair/射影・record/field・variant・
非再帰letを含む元の宣言的Typingから、実際の評価成功と返り値の型適合を導く。
単相letと値制限付き多相letの両方を扱う。多相letの右辺は一度だけ評価され、
その同一の保存値が全instanceの意味を満たす。型ごとの再評価には置き換えない。

`ShadowDataSafety.quotient_typing_evaluates` はこれを決定40の商モデルへ接続する。
部分型の値意味保存は `subtype_preserves` で新規則の全ケースまで証明してあり、
実行安全性を外部の仮定にはしない。`principal_evaluates` は元のprincipal formulaの解から
同じ保証を導く。値意味は部分型についてsoundであり、意味的集合包含から部分型へ戻る
完全性は主張しない。

**`ShadowDataSafety.inferred_evaluates` は実際のデータ推論の成功だけから、単一の実行結果を
構成し、全自由商parameterによる型がその同じ値を記述すると証明する。**
`instance_evaluates` は最後のsubsumptionを含む全instanceを扱い、`inferred_no_error` は
評価器の全エラー結果を排除する。

| 入口 | 証明の対象構文 | 結論 |
| --- | --- | --- |
| 実際の `infer` の成功 | literal・emptyRecord・pair・variant・record構築 | 評価成功、全parameter/instanceで同じ返り値が型に適合 |
| 元 `Typing` / principal formulaの解 | 上記に変数・let・field・fst/sndを加えた第一階断片 | 評価成功、宣言された値型に適合 |

literal payloadは既存core ASTと同じbase tagへ抽象化している。lambda/application・branch・
effect・再帰sourceの実行、Rust runtimeとparserからのelaborationは対象外である。
未対応構文を評価器に渡すと明示的に `unsupported` を返す。全言語の実行停止や
preservation/progressまで証明したとは扱わない。

```sh
lake env lean --trust=0 --run RunSourceDataSafety.lean
```

## 決定41：incoming actionのhandler許可

`HandlerPermissions.check` は注釈の許可maskとarmのkey一覧を受け取り、許可されない
armがあれば拒否する。`diagnostics` は該当keyを元の順序・重複を保って返す。
`diagnostic_iff_unreachable` は診断対象であることと、そのkeyの**すべてのincoming
occurrence**が当該handlerに捕まらないことを同値にする。

境界座標は入口内でfreshに構成する。既存の正の保護も負の解除差分も保持され、
古い`−1`と新しい`+1`を同じ座標で相殺することはない。`discard_denied_arms` と
`denied_arm_bodies_irrelevant` は任意のincoming request tree全体について、不許可armの
削除・本体変更が実行結果に影響しないと示す。許可keyかつ既存重み0のrequestは
`permitted_request_dispatches` により実際のoperation armへ進み、shallow継続は元の行動を保つ。

`checkedHandleIncoming` は検査後に既存のshallow handlerを実行する入口で、成功と
非空の診断一覧による拒否が静的条件と一致する。対象はその注釈付きincoming actionであり、
arm内で局所的に発生するeffectに同じmaskを押し付けない。sourceからの注釈抽出や
mixed-origin action全体の許可推論は未接続である。

```sh
lake env lean --trust=0 --run RunHandlerPermissions.lean
```

## 実際に型を求める入口

**全coreの求解は未完。以下の一般solverは決定39以前の参照モデルを使う。データ式については上節の定理が同じ算法を決定40のモデルへ接続する。** 下記の `SourcePrincipalInference.infer` は旧reference modelのままで、`RecordFree` による無条件のsupport保証もその構文範囲のままである。新しい `RigidSemanticRecords` は決定38の合同関係に、要求tailがrigidな場合だけの共変性を加える。任意admissible tailのhead/幅、hidden fieldを比較しないrigid要求の必要十分条件、完全ground checkerとcut elimination、その商と全core graph compilerの接続を閉じた。さらに新商モデルで、閉じたデータ式の自由parameter scheme・全instance主型性・拒否完全性と、引数recordを拡張する関数族の全instance主型性を証明した。opaqueな要求型での同一視の境界と、一般の残余graph制約の求解は区別して下に明記する。

**`SourcePrincipalInference.infer` は、元の閉じた `Inference.Expr` から主型スキームを計算する。** 元のprincipal formulaの生成、存在変数とletの選択肢の正規化、共有graphへの変換、値型と行の求解、正則再帰型スキームの構成を実行する。型graph、途中の型、行の割当て、制約の解、成功cache、fuelを呼出側から渡さない。

record構築を含まない既存の核について、推論が対応範囲外にならないことも証明した。lambda・application・値制限付き多相let・分岐・pair・fst/snd・field access・variant・空record・literal・変数を含む。`recordFree_instances_exact` は、計算結果の自由な型・行parameterによる**全instance**と、元の独立な `Inference.Typing` の全結果を一致させる。`recordFree_rejected_iff` は拒否と型付け不存在の同値で、成功やモデル存在を前提にしない。`recordFree_principal_formula_exact` は元のprincipal formulaそのものへ接続する。

```sh
lake env lean --trust=0 --run RunSourceInference.lean
```

実行例は元の式から、恒等関数、`any` を入力に持つ定数関数のinstance、自己適用、関数適用、多相letと単相引数の違い、構造型、拒否と未対応の区別を確認する。`SourceInferenceExamples` は計算されたschemeの全instanceが、それぞれ `A ! R -> A ! R`、`any ! R -> int ! ∅` の族と一致することを別途証明する。ここで `! R` は説明用のcomputation行の記法であり、surface構文ではない。定数関数でも未使用引数の行 `R` は自由なまま残る。

`SignedSourceInference` は同じ定理を既存の `RecursiveRows.SetRow` に具体化する。自由な行には保護済みの出現、負の差分、無限supportを含められ、行の深さや重みを打ち切らない。行のempty・join・包含は既存モデルと同じで、`rowView` のdecodeは恒等写像である。これはcore式の推論を符号付き行モデルで解釈する定理であり、operation・handler・protect/releaseを持つ全effect式を、この入口で求解したという主張ではない。

戻り値は `unsupported`・`rejected`・`inferred alternatives` を区別する。成功した全let alternativeを保持し、型矛盾と証明されたalternativeだけを除く。一つでも未対応のalternativeがあれば、全体を未対応とする。record構築の境界と全言語へ残る接続は [10.25–10.27](../spec/10-inference-core.md#1025-record-tailの意味論上の境界) にまとめる。sourceは核のASTであり、parserからのelaborationや表示文字列の正しさを含まない。

## 決定38の基礎と保存した証明

`SemanticRecords.Subtype` は、旧構造・束の規則とrecordのhead/tailの相互部分型による置き換えからなる**最小の合同閉包**である。`Subtype.minimal` がこの意味を特徴付ける。これは旧関係をそのまま商にしたものではない。まず合同性を加え、`SemanticRecordQuotient.QTy` がその相互部分型を同一の値型にする。任意のlabelとfield型について、`record(l,A,{})` と `record(l,A,{} | never)` はこの商で実際に等しい。`int` と `str` は等しくならない。

`SemanticRecordInference.old_typing_preserved` は、旧有限モデルの**任意の環境・式・結果計算型**について型付けを保存する。捕捉した多相束縛と明示署名も環境写像で保持する。`SemanticRecordQuotientInference.formula_exact` と `closed_typing_exact` は、行関係の反射性の下で、合同閉包のrawモデルと商モデルの間の元の任意Formulaおよび全閉core式の型付けを双方向に一致させる。`literal_typing_iff` は以前の反例のliteralの全instanceを通常の有限record型と空行の上位型として特徴付ける。`Typing.record` に構文条件は追加していない。

**ground checker:** `SemanticRecordChecker.check` は任意の有限型2個を受け取り、入力のconstructor depthから必要な層数を内部で計算する。row関係の反射性・推移性、`DecidableEq Row`、渡したrow checkerの正確性の下で、`check_true_iff` と `check_false_iff` が最小合同関係の成立・不成立と一致する。`cut_elimination` の構造atomの前提は前層の実際のBoolean比較であり、意味的なatom比較oracleや外部fuelは不要。既存 `StructuralDecisions` の有限束checkerとcut-free判断に接続する。row checkerそのものは引数である。

`SemanticRecordQuotientDecisions` は同じ前提の下でcheckerの代表元不変性を証明し、商型上に実行可能な部分型判定と等号判定を降ろす。`equal_true_iff` の結論は実際の商型等号である。canonicalな表示や代表元の選択は要求しない。

```sh
lake env lean --trust=0 --run RunSemanticRecordCheck.lean
```

**全coreのcompiler:** `RecordConstraintSupport` は元の生成器の全constructorとletの両経路を扱い、左辺のunionを分割して元の型・row割当てを保存する。`OpenRecordConstraintGraph.compileSource` は元の `Expr` から `principal → normalise → prepare → compile` を実行する全域関数である。record nodeはheadとtailの参照を両方持ち、未知tailをproper spineへ置き換えない。未使用inputも含めて元slotを保つ。`compile_assignment_exact`・`compile_retraction`・`compile_instances_exact` は任意の `Inference.Model` でgraphと元制約の全解を一致させる。

`SemanticRecordQuotientInference.compiled_typing_exact` は、任意のrow join algebra、任意の元core式 `e` と商モデル上の結果 `C` について、**実際に `compileSource e` が返したgraph族のinstanceであることと `Typing [] e C` が同値**だと示す。ここに `RecordFree` はない。しかしgraphの `Models` 条件は残っており、自由parameterだけで全解を表す主型schemeの定理ではない。

**決定38時点の境界:** 最小合同閉包は必要な基礎であって、任意のadmissible tailを持つrecordがheadを使え、fieldを忘れて `{}` に幅包含できるという既存の義務をすべて満たすモデルではない。例えばこの関係では `record(l,A,never) ≤ {}` が導けない。この否定は中間関係の境界であり、意図する言語の型エラーではない。当時の確認点だったtail共変性には、決定39でrigid要求に限定する回答が入った。`SemanticRecordVarianceBoundary` は、明示したフィールド存在の局所法則だけから一般共変性が導けない有限代数を示す。payload・実行・inhabited性を含むYulang全仕様からの独立性は主張しない。

決定39はこの確認点に対し、要求tailがrigidな場合だけの共変性を指定した。その証明は次節の新関係で行い、この最小合同閉包の定理・負例は歴史的な参照として保持する。正則再帰型/coalescing、新graphの実際の制約求解、`SourcePrincipalInference` の全instance主型性と拒否完全性への接続は残る。effect式、再帰SCCと全注釈多相再帰、注釈の一般化直前の確定、role・cast・EOFは各層の既存定理のままで、この入口には未統合。表示の標準形・`as`の最終表示・一般の禁止点付きgraph到達も今回の変更に含めない。

## 決定39：rigidな要求への共変性と先勝ち

`RigidSemanticRecords` は旧関係を保存し、`IsRecord S` と `R ≤ S` から `record(l,A,R) ≤ record(l,A,S)` を導く規則だけを追加する。一般の要求tailへの共変性、分配則、bottom strictnessは追加していない。`record_head` と `record_width` は、任意の `R ≤ {}` についてheadの利用と `{}` への幅部分型を導く。特に `record(l,A,never) ≤ {}` が成立する。旧モデルの否定定理や期待値を変更せず、新関係について別の定理を証明している。

`RigidRecordDemands.record_mask_exact` は、任意のrawな供給head `A`・tail `R` とrigidな要求 `P` について、次の必要十分条件を示す。行関係の法則は前提にしない。

```text
record(l,A,R) ≤ P
  ↔ (Pにlがあれば、その最初のfield型Bに対してA≤B)
    ∧ R ≤ erase(l,P)
```

`erase(l,P)` は要求側の同名fieldをすべて除く。`checkDemand` はこの分解を実行し、任意の正確なBoolean row checkerと行preorder、および `DecidableEq Row` の下で、rigidな要求型に対する成功・失敗が宣言的関係と一致する。`checkDemand_hidden_payload` は隠れたpayloadを変更してもBoolean結果が変わらないことを示す。この省略は当該record層についてで、visible payload内の比較は再帰的な型比較に委ねる。

`RigidRecordChecker.check` は非rigidな要求も含む有限ground型の**参照関係**全体を同じrow前提で完全に判定する。`cut_elimination` は計算されたatom比較を持つcut-free判断へ接続する。`RigidRecordQuotientDecisions` は代表元不変性から、商の順序・実際の等号の実行可能な判定を構成する。商上の `Rigid` はproper代表元の存在であり、単なる構文判定ではない。

```sh
lake env lean --trust=0 --run RunRigidRecordCheck.lean
```

`RigidRecordInference` と `RigidRecordQuotientInference` は、旧有限モデルの任意環境の型付け、前回の合同関係とその商の全閉式instance、元Formulaのraw/商同値を保存する。`compiled_typing_exact` は任意のrow join algebra・元core式・結果について、実際の全core graph出力のinstanceと新商モデルの `Typing` を一致させる。これは依然として残余graph制約を持つcompiler定理である。

**opaque要求の境界:** `RigidRecordOpaqueBoundary.hidden_field_rigid_comparison` は、任意のtail `R` と全rigid要求 `P` について、`record(l,A,record(l,B,R))` と `record(l,A,R)` が同じ比較結果を持つことを示す。一方、`R = never`、および `R = {y:int} | {z:str}` の具体例では、両型はadmissibleでも互いに部分型ではない。後者のunionも、proper spineと同値な代表元を持たないことまで証明した。この限定規則だけでは、rigid要求で省略できるhidden fieldを任意の型同士の同一視まで省略できない。これらは関係の境界であって、sourceの拒否や一般solverの不可能性ではない。

`RigidRecordSourceBoundary.source_has_incomparable_instances` は、この二つの型が同じ元core式の型付けに現れることを示す。式は外側から `x:int`、`x:str`、`y:int` の3つのrecord構築であり、`y` のrecordを上のunionへ広げる経路と、内側の `x` のrecord全体を同じunionへ広げる経路を使う。任意のrow join algebraで両結果が元の `Typing` とprincipal formulaのinstanceになり、全rigid要求への比較は一致する。下の実際のschemeも両instanceを保持する。opaque型を同一視する新法則は追加していない。

この別型性は、今回明示した規則のみの最小関係の性質である。4.3のfirst-field-winsと決定38を、nonrigidな推論tailに隠れたfieldの型等価へ適用する範囲は確認事項として残る。「同じ式のinstanceである」ことだけから二型の等価は導けず、また、この最小関係の非比較を仕様全体からの独立性や確定した言語の区別とも扱わない。

前回の `SemanticRecordVarianceBoundary` の有限field存在代数は、今回のrigid要求への共変性を満たす。`RigidRecordVarianceBoundary.local_laws_with_rigid_without_general_covariance` がそれを示し、旧反例の右辺unionはnonrigidなので決定39の反例にならない。payload・実行を持つ言語全体のモデルであるとは主張しない。

## recordを含むデータ式の自由parameter推論

**`RigidRecordValueInference.infer` は元の `Inference.Expr` から有限のschemeを実際に構成する。** `Data` はliteral・emptyRecord・pair・variant・record構築を再帰的に含む構文で、不正なrecord tailも入力範囲に含む。返り値は `unsupported`・`rejected`・`inferred plan` を区別する。`infer_unsupported_iff` は `unsupported` がちょうど `Data` の外であることを示す。型付けの導出・constraint graph・成功cache・意味的な包含checkerは入力にしない。

各recordで自由な値型parameterを2個残す。子のschemeの値型を `H,T` とすると、構築する型は次である。

```text
record(l, H | α, (T | β) & {})
```

tailのplanがrecord形なら `T ≤ {}` がすべての子parameterについて成り立つため、任意の `α,β` が有効なinstanceを作る。逆に元の型付けが構築に使ったhead `A` とtail `R` をparameterに選ぶと、`H ≤ A`、`T ≤ R ≤ {}` から `H | A ≃ A` と `(T | R) & {} ≃ R` が成り立つ。record合同性で元の構築型を回収するので、opaqueな要求tailへの一般共変性を仮定しない。これらの型付け由来の選択は完全性の証明内で行い、推論の呼出側には渡さない。

任意のrow join algebra、任意の `Data e`、任意の結果計算型 `C` について、`RigidRecordValueInference.infer_instances_exact` は、計算されたplanの**自由parameterによる具体化とsubsumptionだけ**が元の `Typing [] e C` と一致することを示す。`infer_principal_formula_exact` は元のprincipal formulaへ接続し、`infer_rejected_iff` は実際の拒否と型付け不存在を同値にする。`Good`・graphの解・parameterに対する残余制約は定理の外部前提にしない。

`RigidRecordValueQuotient` は同じplanを決定39の商モデルで評価する。自由parameterは商型全体を動き、`infer_instances_exact`・`infer_principal_formula_exact`・`infer_rejected_iff` が同じ量化範囲で成立する。`infer_plan_sound` は実際に返されたplanの任意parameter tupleが元の式の型付けを与えることを示す。`inferred_boundary_has_both_instances` は上のopaqueな二つの結果を実際の計算結果が両方保持し、`boundary_quotient_types_distinct` はその二型がこの商でも異なることを示す。

```sh
lake env lean --trust=0 --run RunRigidRecordInference.lean
```

この定理の値型carrierは**有限raw型とその商**である。literal、任意深さのrecord・pair・variantの入れ子、およびscalar/pair/variantをtailに置く不正入力を含む一方、変数・一般lambda/application・let・field access・effect式・正則再帰値型はこの入口の対象外である。既存の `SourcePrincipalInference` と統合した定理ではなく、その `RecordFree` 制限は外していない。

## 引数recordを拡張する関数族

`RigidRecordFunctionScheme.scheme l b` は、元の核式 `lam (record l (lit b) (var 0))` に対する有限の `CompTerm (Fin 4)` を計算する。任意の値型 `α,β,γ` と任意の行 `ρ` に対して、次の型を構成する（`!` は説明用のcomputation行記法）。

```text
I = α & {}
H = b | β
T = (I | γ) & {}
(I ! ρ) -> (record(l,H,T) ! ρ)     外側の行はempty
```

`instantiate_eq_eval` はこの構成と実際のdescriptor評価の一致を示す。任意のrow join algebra・label・base・結果 `C` について、`instances_exact` と `principal_formula_exact` はこのschemeの全instanceを元の式の全型付け・principal formulaと一致させる。3個の値型と1個の行はすべて自由であり、入力からtailへ必要な包含は型の式自身に組み込む。入力行を出力行でも共有し、元の型付けがさらに広い出力行を持つ場合は通常のsubsumptionで保持する。反変入力を独立な `any` に消して、この共有を落とす変更は行わない。

`RigidRecordFunctionQuotient.instances_exact` と `principal_formula_exact` は同じ全instanceの一致を商モデルへ移し、`instantiate_sound` は任意の商parameter tupleに対して元の関数の型付けを与える。これはこの関数族についての完全な主型schemeであり、任意の関数を解析する新しいsource dispatcherや、正則再帰型を含む全core solverではない。

## 個別のsolverと従来の入口

`ValueInference.solve` は既存の核の式を受け取り、変数・リテラル・分岐・let・pair・variantの型を構成する。途中の型や生成制約の解を引数として渡さない。分岐では `ValueBounds.solve` が結果の未知型を解く。評価時のeffectは空で、入力環境の既知値型には符号付きの潜在effectを含められる。

次の実行例は、実際のsolverを呼び、想定と違う結果なら失敗する。

```sh
lake env lean --trust=0 --run RunValueInference.lean
```

混在した分岐の `int | str`、その結果を使うletとpair、不正な条件と未束縛変数の拒否、循環bound、負の潜在effect、無限row、恒等関数の型・行の相関を確かめる。入力はparser後の `Inference.Expr` であり、surface source文字列を処理するcompiler frontendではない。一般のlambda/applicationは `unsupported` として返す。これは `unsat` と異なり、型付けの不在を意味しない。

`closed_principal_solved_exact` は、求めた型 `T` の上位型全体が、元の `Inference.principal` の許すすべての結果と一致することを示す。`closed_principal_unsat_iff` は対応する構文について、solverの拒否と、元のprincipal formulaの解の不在を同値にする。単なる「解を与えれば正しい」という入口から、この断片では解の構成と失敗判定まで進んでいる。

関数については別に、`ValueBoundEliminationExamples.identity_principal_exact` が実際の `principal [] (lam (var 0))` をsolverで構成した型族へ接続する。引数の型 `A` と行 `R` を自由なparameterに残し、内部結果だけを解くと、意味的に `A [R] -> A [R]` になる。一般化する変数をsourceから発見する算法や、任意の関数の推論まで閉じたとは主張しない。詳しい算法・量化子・対象外の範囲は [`spec/10-inference-core.md` 10.18](../spec/10-inference-core.md#1018-未知の値型の求解) にまとめる。

決定36・37に対応し、`any` を核のtop型へ追加した。`ValueUpperBounds.solveGreatest` は上界の交差から最大解を構成し、負の位置の未知型の消去を全インスタンスについて証明する。`ValueBoundSchemes.solve` はさらに、正負が混在する出力でも共有parameterを保つ、制約のない型スキームを構成する。`solve_models_exact` と `principal_exact` は、計算されたスキームの全具体化が元のflat boundの全解を正確に表すことを示す。式と量化子は [10.19](../spec/10-inference-core.md#1019-any上界の双対全解の型スキーム) にまとめる。

入れ子の未知型と循環には **`RegularSchemeInference.infer`** を使う。有限の型node graph・制約・出力nodeからregular principal schemeを構成し、`infer_principal_exact` が実際の呼出し結果の全instanceと元の独立な制約モデルの全instanceを一致させる。`infer_none_iff` は正則再帰型を含むモデル不存在と失敗の同値である。rowはこの入口では固定され、source ASTからの全変換や行の同時求解は別の層にある。

```sh
lake env lean --trust=0 --run RunRegularInference.lean
```

この実行例は恒等関数適用・自己適用のgraphからschemeを作り、再帰する自由parameterを代入する。反変入力とnested pairの矛盾の拒否、共有parameterを守る簡約も実行する。有限深さの実行チェックと、全深さについて証明されたmodel/主型定理を区別する。Simple-subとの対応と参照revisionは [`REFERENCES.md`](REFERENCES.md)、算法の主張は [10.20–10.22](../spec/10-inference-core.md#1020-共有parameterの意味を保つ簡約) に記す。

元の型項からは **`TypeConstraintInference.infer`** が、`TyTerm (Fin n)` の不等式列を共有node graphへ変換し、同じsolverからregular schemeを構成する。`infer_correct` は実際の呼出しについて、未対応・解なし・推論成功の三分岐を証明する。対応範囲では `infer_models_exact` が元の全割当てと自由parameterによる全具体化を一致させ、`infer_instances_exact` が任意の出力slotの全instanceを一致させる。行の割当ては、この入口では固定される。型のconstructorと再帰blockは `RegularInferenceModel` の一つの型carrierに収まる。

行には `RowFlowSchemes` と `NestedRowRequirements.solveRows` を追加した。後者はshapeの飽和で必要になる全arrow行比較を回収し、明示された行制約と合わせて共有parameterの行schemeを求める。関数入力の行比較は反変方向のままである。値型・行の未知数の番号を保つsource clauseの分割は `ConstraintProblems.closed_source_problems_exact` で元の型判断に接続する。値型との統合は `JointConstraintInference`、元の式への接続は上の `SourcePrincipalInference` が担う。

旧モデルのrecord境界は反例として保持する。`RecordTailBoundary` は、空recordと相互部分型であるtailに置き換えても、旧reference algebraではrecord全体が同値にならないことを示す。決定38後の新しい合同関係では、この具体的な障害は解消する。旧否定定理の主張や旧solverの期待値を書き換えず、移行先の保存定理を別に証明している。証明範囲は [10.25–10.27](../spec/10-inference-core.md#1025-record-tailの意味論上の境界) に記す。

## 証明対象

| モジュール | 閉じる主張 | それだけでは示さないこと |
| --- | --- | --- |
| `Yulang.CaseValues` / `CasePatterns` / `CasePatternSafety` / `CaseEvaluation` / `CaseDataTerms` | 具体値の分解、独立な束縛型判断から照合安全性、whole merged payloadの型付け、orの名前集合、上から順のarm/guard/body評価、具体data葉から健全性契約の導出 | 全Rust pattern matrix、sourceの名前解決・型注釈検査・束縛順の整列、関数/effect/再帰との統合 |
| `Yulang.ScopedCasePatterns` / `ScopedCasePatternSafety` / `ScopedCaseEvaluation` / `ScopedCaseTotal` / `ScopedCaseDataProgram` / `PatternBindingChecks` | 先行束縛を読むdefaultと同じ順の型環境、型判断から照合安全性、独立TotalTypingから具体caseのprogress、同一経路の重複binderの静的拒否、Q4–Q7の実値・訪問列 | sourceの環境/presence導出、effectfulな葉、CaseTree・統一ASTへの接続 |
| `Yulang.CaseCoverage` / `CaseCoverageSafety` / `CaseDataProgram` / `CaseCoverageExamples` / `CaseCoverageBoundaryExamples` | 保守的な網羅性checkerと独立判断の同値、guard除外、merged tag残余の正確性、具体programの型付けから実評価・全arm不一致の不在、順序/default/enum payloadの実値例 | false側のsource拒否完全性、record内の複数arm合成、list長さの深い分岐、整数区間合併、source全体のRust pattern matrix、source nominal構築子elaboration |
| `Yulang.JointCaseCoverage` / `ScopedCaseCoverageSafety` / `ScopedJointCaseCoverage` / `ScopedJointCaseExamples` | 複数の反駁可能armによる同一tagのpayload cell被覆、独立判断との同値、旧受理の保存、全tag単位の残余、各scopeの型付けとdefault domain包含から具体caseのprogress、Q4とQ8が同時に働く量化例 | 一般pattern matrix、record/list/整数の既存未認証例、sourceの拒否完全性、effectfulな葉・CaseTree・統一ASTへの接続 |
| `Yulang.CaseTree` / `CaseTreeExamples` | scrutinee/body・pair・letへの有限case入れ子、独立型付けから実評価の型安全性と未一致の不在、任意整数について値と訪問列を保持する入れ子例 | guard/default内部のcase、一般再帰・関数/application/effect/castの統合、source名解決とscope付きdefaultの統合 |
| `Yulang.CasePresenceValidation` | 宣言presenceのoptional許可/required拒否/unknown未解決、具体recordの旧markerへのlookup保存、required/optional所属の対応、型付きlazy defaultからunionに入る実束縛 | sourceからpresence metadataを導出し全patternへ適用するpass、旧markerにないfloat/list/nominalの射影、source defaultのscopeを割り当てるpass |
| `Yulang.LiteralValues` / `LiteralValueExamples` / `Binary64` / `Binary64Rounding` / `Binary64Decimal` | 内容つきliteral、整数範囲、64bit codecの相互逆、数値Eqと独立判断の同値、正負zeroの一致・NaNの不一致、任意tokenの厳密な分数化と有限範囲の全候補最近接偶数丸め | 数値演算、parser/escape、Rust f64との対応、非零巨大指数の資源最適化、既存base-marker ASTとの全体統合 |
| `Yulang.Binary64Overflow` / `Binary64SourceDecimal` / `Binary64SourceExamples` | 全正分母有理数の有限丸めと厳密なoverflow境界の同値、全decoded tokenの成功/静的overflowと独立な有限丸め結果の存在/不存在の同値、旧成功値の保持、両符号のnear-max/midpoint回帰 | lexer・source span/診断・無限大定数の名前との接続、Rust f64との対応、巨大非零指数の資源最適化 |
| `Yulang.PresenceLegacyBridge` | 任意の有限legacy型とmaskのdata意味を保存するpresence翻訳、Shadow部分型の包含保存、閉supported型判断の移送、finite-data planの全parameterを同じexact結果が一方向に包含、optionalの分解と旧width型の反例 | 逆向きの部分型完全性・scheme等価、regular型と自由row parameter、closure/effect行の意味、SourcePrincipalInference全体への統合 |
| `Yulang.PresenceLayers` | required/optional/lacksを保つ有限layer、任意の子述語と正確なmembership checkerから全値で判定同値、mask合成とhidden field消去、field別optional化で相関が失われる反例 | 任意述語の決定可能性、全深さの部分型判定、closure/effect行の意味、拡張solverの主型性 |
| `Yulang.PresenceRegularObservations` / `PresenceRegularLegacyBridge` | 任意graphの全有限観測判定、可換なrenameと有限block closureでの保存・反映、旧regular型のdata所属・data包含との同値、既存common carrierのblockへの接続 | 旧structural subtypingとの同値、arrow/closureと行の意味、全深さの判定算法、presence制約の飽和/coalescing、全source schemeのinstance同値 |
| `Yulang.NominalConstructionRuntime` / `NominalConstructionExamples` | 不変parameterの元の構築位置の順序、適合時のcast抑制、純粋cast後の全request tree保存、EOFの実値保持、metadataとarity保存 | ground境界検査から値型に正しい変換codeの合成、固定struct field・宣言defaultを含むsource elaboration、sourceからのsite/構築AST生成 |
| `Yulang.NominalDataAssembly` / `NominalDataAssemblyExamples` | site実行器から具体ASTへの完全等式、元のrequest treeとEOF値の保持、受理plan・局所CastContract・元site型・独立Code型判断から返却分岐の構築成功と結果型、struct/enum/listの実値例 | sourceのsite抽出・Code生成、固定field/defaultの宣言検査、cast code合成、Fold/Indexのsource辞書との対応 |
| `Yulang.NominalListSpread` / `NominalListSpreadExamples` | 任意位置の有限list spread、独立data型判断と環境・変換契約から実評価と全要素型、記述順に各sourceを一度読む全訪問列、同じ列に対する具体list・nominal metadata・Fold・内部Indexの一致 | 回答済みQ13のsource Fold本体からの意味保存、spread要素の保留cast境界（Q14）、source site抽出・変換選択・保留planの自動生成 |
| `Yulang.FoldTraversal` | 任意stateの走査protocol、局所契約から全有限prefixのitem型・signed request行・有効state保存、終了を仮定しないprogress、無限yield例、rigid roleの一意辞書planと供給driverの一致、純粋cursorと既存forの一歩の対応 | source高階Fold.fold本体からのprotocol生成・意味保存、供給method tableの検証、sourceの型/effect一般化 |
| `Yulang.FoldListSpread` / `FoldListSpreadFinite` | source評価と辞書走査の順序付け、各partのitem型とsource/走査行のunion、局所契約と独立型判断から全有限prefixの安全性/progress、返る場合の要素型、任意の途中走査で後続source保持、独立data型判断・環境・変換契約から旧/新の同一返却列・同順同回数のsource trace | 高階source Foldからの意味保存・method table検証、source推論/辞書elaboration、観測signatureからsource effectへの翻訳、Q14のcast境界 |
| `Yulang.FoldListSpreadRoles` | acceptedなrigid container/item slotから実spread型判断へ、型付きregistryの選択bodyによるitem型・source/走査行union、任意の同goal Dictionaryとのdriver/行の一致 | source Fold goal/associated typeのencoding、source methodから型付きregistryへの生成・意味保存、既存evidenceの再利用、source for_inと全推論器への接続 |
| `Yulang.FoldListSpreadDivergence` | 局所Safe・有効stateでdoneにならない条件から全有限prefixで後続source保持・行保存・非返却、型付き非空literal内の無限repeatと安全性の共存 | 任意のsource Fold本体の非停止判定、source method/protocol対応、停止性を含む全sourceの主張 |
| `Yulang.NominalListViews` / `NominalListIndex` | 同じlistに対するcursor・index・foldの一致、整数indexの成功と有効区間の同値、無効indexの非再開error要求、既存wrapとの一致 | sourceのFold/Index辞書の選択・署名と本文の対応、source名/宣言identityから解決済みerror familyへのelaboration |
| `Yulang.NominalListIndexError` | Q12の解決済みInt/Empty宣言・Cases・Encoding、任意Intの成功区間、全無効原因で同一operation/原index payload、abortiveなbind、wrap/catchとの完全等式と残余行上界 | source名と宣言identityの解決、source Index辞書・本文へのelaboration、統一推論器への行の組込み |
| `Yulang.NominalDataConstructionExamples` | 解決済みnominal構築式、任意整数から計算するstruct/enum/list payloadの型付けと実評価・全訪問列 | 宣言のlookup・型引数・payload宣言型の検査、source constructor default・castの挿入 |
| `Yulang.MultiOperationHandlers` / `MultiOperationHandlerTyping` / `MultiOperationHandlerInference` / `MultiOperationHandlerExamples` | 有限の複数operation表と1つのvalue arm、shallow/multi-shot、重みを保つdispatch、incoming maskの静的拒否、独立型判断とcheckerの同値、型付けから全request/returnの安全性、入れ子化で意味が変わる反例 | 一様Atom以外のoperation署名、operation-local多相、source patternから束縛付きarm表への翻訳、sourceからmaskを求めるelaboration、全言語の主型推論・再帰の安全性 |
| `Yulang.MultiOperationPayloadHandlers` / `MultiOperationPayloadInference` / `MultiOperationPayloadExamples` | 同一keyの順序付きpayload dispatch、missのforwardと残余保持、unguarded反駁不能armだけのkey減算、既存構文のchecker/型判断/安全性の拡張、旧全域表との一致、全armへの明示mask検査 | source patternの束縛、effectful default/guard、個別operation署名と多相、mask導出とfresh移送、全sourceの主型推論 |
| `Yulang.MultiOperationIncomingInference` | 明示incoming maskを実構文checkerに合成、独立型付けとの同値、不許可armの静的拒否、推論成功と環境適合性から既存構文評価のValid、同一maskのruntime gate対応 | source maskの導出と入れ子handlerへの割当て、fresh座標へのclosure/潜在行の移送、構文評価とenterTree後の実行の意味保存 |
| `Yulang.Types` / `Yulang.Inference` | 構造再帰する有限制約生成、独立な宣言的型付けとの双方向の一致、制約schemeの主性、非再帰の値制限付き多相let | 全制約の判定、再帰SCC、sourceのoperation/handlerのelaboration、公開型の正規化 |
| `Yulang.StructuralBase` / `Yulang.Structural` | 行の解釈を共有する具体的な構造部分型モデル、`never`/`any`・union/intersection・幅部分型・関数の分散、生成制約の正例と反例 | 完全なMLsub意味論、再帰型。決定手続きは `StructuralDecisions` で扱う |
| `Yulang.Polymorphism` | effect付きcomputation変数の単相let束縛を受理し、そのeffectを空行へ消す生成制約を拒否すること | 再帰的な一般化、sourceのalias解析 |
| `Yulang.Effects` | 出現ごとの保護・解除、任意の行置換での非capture、well-founded computation treeでの非capture、shallow handlerのeffect上界 | sourceからのelaboration、operation署名の型安全性、全言語のpreservation/progress |
| `Yulang.EffectInference` | core生成器を使うrequest・boundary・shallow handler規則の健全性と完全性、有限個のoperation-local型変数の呼出側での存在具体化・handler側での全称検査、結果と外側環境へのescapeの構造的排除、単相規則と明示された実行時上界の合成 | sourceからのelaboration、atomのpayload内部にある局所変数、局所変数のrole制約、型付けから実行時上界を導く証明 |
| `Yulang.RowInference` | 同じrequest・boundary・handler制約生成を非負行と符号付き行に具体化する共通の双方向定理、operation-local型変数の存在具体化・rigidな全称検査、行置換と評価の両立 | sourceからのelaboration、atomのpayload内部にある局所変数、局所変数のrole制約、型に沿った潜在行の変換、量化を含む制約のsolver |
| `Yulang.SignedStructural` | 実際の符号付き行を持つ構造部分型モデル、operationのeffectと負の解除差分を保持する生成制約の正例・負例、局所型の任意の具体化と独立した二回の呼出し、rigidなpayloadを継続に渡す正例と固定int結果へ返す負例 | 完全なMLsub意味論・solver、sourceの由来条件の保存 |
| `Yulang.HigherOrder` | 有限の型shapeに沿ったproduct/list等の格納callbackの保護と非capture。単純なerase解除の限界を示す反例 | 任意の高階の境界の意味保存。`guard ∘ release` はこのモデルでは恒等でない |
| `Yulang.Directed` | 符号付きの境界差分、両方向の相殺、非負保護listの埋込み、明示した由来条件の下での非capture | sourceから動的な境界を構成し、由来条件を保存すること |
| `Yulang.FreshBoundaries` | 任意の単射による境界座標の拡張、既存の符号付き重み・capture・残余・handler実行の保存、新しい座標の割当てによる原点条件の構成と任意の元のrequest treeの非capture | sourceの全呼出しがこの割当てを使うこと、返り値・payload・response内部の潜在callbackの変換 |
| `Yulang.FreshRowInference` | 全有限RowExprについての境界名の写像と評価の可換性、任意の未知tailを含む評価結果のfresh原点条件、T3のsnapshot・保存履歴・formulaのgateの不変性 | source境界の発見、型slotのfreshening、潜在callbackの変換、型付けからruntime上界を導くこと |
| `Yulang.DirectedHigherOrder` | 任意の有限shapeと値における両方向の高階transportの相殺、由来条件付き非capture、混在した由来のcallbackの例 | 再帰型、atom・operation payload内部のtransport、sourceのelaborationとpreservation/progress |
| `Yulang.DirectedBounds` | 符号付き行でのshallow handlerのeffect上界、保護・解除による上界の双方向のtransport | sourceの型付けからaction・armの上界を導くこと、値内部の潜在行 |
| `Yulang.DirectedHandlerInference` | 成立した共通のhandler生成制約とaction・armの実行時上界から、実際の符号付きhandler全体の上界を導くこと | action・armの前提そのものをsourceの型付けから導くこと |
| `Yulang.Annotations` / `Yulang.AnnotationSnapshots` | 注釈時点の可視effect検査と正確性、符号付きの観測履歴の固定、T3 の具体化時に再検査しない規則と主制約生成器の接続、未知行の後の具体化と当初から既知で可視な禁止effectの区別 | 何がその時点で既知かを決める solver、source 注釈から観測時点を構成する elaboration |
| `Yulang.AnnotationFinalization` | binding/SCC全体の有限Horn制約を解いてから符号付き観測を固定する入口、最小解の真のfactと全モデルで強制されるfactの一致、制約順序・重複・member順序に依存しない受理、一般化前の検査と後の具体化の分離 | 構造型推論から有限fact interfaceへの翻訳、無限のsigned stackを含む全体solver、sourceのSCC発見と名前の振り直し |
| `Yulang.RecursiveInference` / `Yulang.RecursiveExamples` | 有限の同時再帰制約生成と独立な SCC 型判断の一致、全注釈の値型変数だけを具体化する多相再帰、明示的なeffect行の共有、SCC 後の値の一般化と computed slot の保持、depth型再帰の全注釈受理と `any -> int` での単相受理 | source の SCC 発見と全注釈認識、local/captured slot 分類の推論、解の探索、評価依存の検査 |
| `Yulang.QualifiedInference` / `Yulang.QualifiedGeneralization` | resolved method からの role 制約生成と独立な型判断の一致・主性、raw role 制約の自動分配、抽象辞書での定義検査と利用時の証拠要求、環境slotの共有、通常のletでの値型・行の独立した一般化 | 未解決の構造制約から一般化interfaceを発見するsolver、source の method lookup、任意に入れ子になった source qualified let の elaboration |
| `Yulang.ModuleRoles` / `Yulang.QualifiedExamples` | 与えられた部分割当てとinterfaceに対するEOF検査、実際のresolverによる残留role制約の確認、公開型に使う未確定slotの拒否、公開schemeの意味と解の拡張に対する独立性、辞書の有無・型の後決め・非空の潜在行の正例と負例 | module全体から未解決制約を漏れなく収集するsource pass、部分型の解を探索すること、opaqueな意味的型の内部表現に関する閉性 |
| `Yulang.ModuleVisibility` / `Yulang.ModuleDictionaries` | 自file・import・accessの可視判定を実際のEOF検査と辞書木の構成へ接続、非可視宣言の変更・宣言順序・重複による不変性、公開schemeの意味保存、全nodeの可視な由来、file間で渡された辞書木の保持 | source module/import/access解析、未定型の推論、source宣言identityの割当て |
| `Yulang.EOFNoDefaulting` | EOFの未定slotをimpl検索より先に拒否、既存`finishModule`・file可視な`finish`との成功の同値、可視implに依らない未定型の拒否、型確定後の失敗goal、公開型の閉性・同じexportの保持、impl増加で同じexportまたは具体的な曖昧さになること | sourceからの全残留制約の収集、一般化slotの分類、通常の型推論、source診断の位置・文言 |
| `Yulang.EOFRoleInference`（旧仕様の参考実装） | ground headからcompletion候補を列挙する独立した実験の正確性。追加公理の監査には含める | 決定33により現行Yulang3の推論入口ではない。`Yulang`からはexportしない。未定型を唯一implから補完する規則は採用しない |
| `Yulang.RoleEvidence` / `Yulang.RoleEvidenceExamples` | role要求を持つ既存のPolySignatureについて、呼出側の存在具体化と証拠要求、handler側のrigidな全称検査と署名辞書、qualified生成器を使った双方向の一致、実際の符号付きモデルでの辞書使用と証拠欠如の負例 | sourceのoperation/handler構文全体のelaboration、atomのpayload内部の局所変数、型付けから実行時の上界・安全性を導くこと |
| `Yulang.Roles` | 第一階 impl 集合の一方向照合、Paterson 型条件による置換後の型サイズの真の減少と深さ制限なしの解決の停止、健全性、到達する head に重なりがない場合の完全性、到達可能な head の重なりと曖昧さの同値、正例・負例 | generic role の method dispatch、章6.4の receiver 下界による解決保留、effect との相互作用、operation-local role 制約、推論の制約言語との統合 |
| `Yulang.RoleVisibility` / `Yulang.RoleDictionaries` | 可視impl増加で成功は成功または曖昧、曖昧性保存、順序・重複不変、実際のresolverから全where子を持つ辞書木を構成、成功とのiff、成功継続時の木全体保存、受け渡した辞書の保持と既存WithEvidenceへの接続 | source method bodyの実行、未知型の代入探索、重複するgiven binderのsource選択規則 |
| `Yulang.RolesAssoc` | 第一階の関連型の明示定義と default、解決成功時の宣言済み各名前の全域性・一意性、where の導出や照合置換によらない値、goal の変数だけを含む結果、明示定義の置換後のサイズ公式、正例・負例 | 関連型を含む method 署名、`value ~ int` 等の等式制約や where 条件との単一化、receiver 下界による解決保留、source 宣言検査。他 role の関連型を右辺で参照することは2026-11-05の決定により対象外 |
| `Yulang.RoleConstraints` | 具体的なresolverの成功と導出・非曖昧性の一致、関連型選択から普通の等式の追加への接続、全置換について等式制約追加の可換性・冪等性・順列不変性、既存制約との矛盾を上書きしないこと | 未知の置換を探索する単一化器、構造部分型とrole制約を合わせた全体solver。`Store.check` は与えられた置換での検査 |
| `Yulang.CheckedRoles` | 有限の宣言検査と全変数についての Paterson 適格性の同値、証明を入力に要求しないresolver入口、不適格な宣言の拒否、適格な集合での成功・曖昧さの正確性 | source parser/name resolution、関連型宣言の全検査、診断位置・文言、疎な変数番号での計算量最適化 |
| `Yulang.ImplHeads` | impl headの各holeを別の変数へ下ろす処理、全匿名識別子の一回性と名前付き変数の共有、whereから匿名変数への参照不能性、ref全体の照合と部分特化 | source parser・型/行のkind検査、未束縛名の診断、methodの可視性や段階ごとの検索 |
| `Yulang.Horn` | 任意の有限Horn制約に対する解の存在判定と最小モデル。成功・失敗の両方向の完全性 | 構造部分型、再帰型、無限の保護stack、roleの解決 |
| `Yulang.RecursiveRows` | 保護・解除・残余を含む正の再帰的行制約 `E ≤ slot` の最小集合解、全解で強制される出現との一致、固定上界との両立の必要十分条件、既存の有限行解釈の保存、有限行では解けない保護反復の例 | 解への所属の決定手続き、任意の右辺を持つ行包含、構造型solver、sourceからの制約抽出、すべての再帰行の有限表示 |
| `Yulang.InfiniteRowHygiene` | 任意の無限集合行での両方向相殺・包含保存・残余、境界再indexと全行式・再帰最小解の可換性、fresh原点と非capture、同じkeyを含む無限tailの保持、無限行によるrequest tree上界 | 一般の所属決定、無限行のsource型付けからruntime上界を導くこと、潜在closure変換 |
| `Yulang.RecursiveRowGraph` | 有限行制約から有限guard付きgraphへの実行可能なコンパイル、任意の無限行割当てでのモデル保存、独立な到達可能性と既存最小解の一致、有限の到達key・slot支持 | 無限configuration空間の到達判定、半線形な解表示、包含・等価判定 |
| `Yulang.RowTransportNormalForm` | 固定keyに対する有限programの平行移動＋有限禁止入力点への正確な正規化、各途中residualの保存 | guard付きpath全体の半線形性、単なる総変位によるpath判定 |
| `Yulang.FinitePointGuards` | 逆方向に、任意の有限禁止点付き整数平行移動を既存protect/release/residualで表現し、有限graph全体を既存の行問題へ埋め込むこと、独立なgraph到達可能性と最小解の一致 | 一般の到達可能性・半線形性・決定不能性の結論、巨大整数のbit長に対する効率 |
| `Yulang.AffineRows` | 任意の有限境界数・整数周期ベクトルを持つ一つのrayの有限候補による所属判定、二つのrayの包含・等価判定と両方向の正確性 | 任意の相互再帰制約の求解、複数rayのunion同士の包含判定 |
| `Yulang.SymbolicRows` | affine segment・union・差集合からなる有限表現の所属判定、既存の全行式操作についての閉包性と評価保存。shiftは基点を動かし、residualは有限raw点を除去 | 未知の最小解への人為的な上限、全再帰問題の解がこの形を持つこと、任意の有限式同士の包含 |
| `Yulang.SegmentDecisions` | 任意の二つの有限または無限segmentについて包含・等価性を決定し成功・失敗を意味と一致させること。有限sourceは真の上端まで列挙 | 複数segmentのunionの包含、全再帰問題の求解、有限上端に依存しない計算量 |
| `Yulang.CyclicRows` / `Yulang.CyclicRowDecisions` | 一つの初期programと一つの反復programからなる既存の二規則問題について、途中guardを保った最小解の有限表示、所属・包含・等価性の実行可能な判定、実際のDerivesと最小モデルへの接続 | 分岐・複数cycleの相互作用を含む一般graph、一般の半線形最小解の構成、sourceの再帰SCCからこの形式への翻訳 |
| `Yulang.RecursiveRowDisplay` | 推論表示の単一 `as` binderの最小解意味論、展開・折り畳み、一つのslotを持つ任意の有限問題から意味を保つ本体構成、確定した `as` binderと現行の一境界・一tail表示における所属・包含・等価判定の接続 | 一般binder本体のsolver、表示文字列のparser/roundtrip、複数境界の整形と未確定の相互再帰変数の表記 |
| `Yulang.SemilinearWeights` / `Yulang.WeightedPaths` | 任意次元の符号付き整数重みについて、半線形集合の有限union・和・starの構成と意味保存、有限graphのstate elimination、独立な全有限pathとの双方向一致、到達重みの有限半線形表示 | 有限禁止点を含むgraph、半線形集合の一般所属・包含・等価性の決定、性能・最小表示 |
| `Yulang.SemilinearRows` / `Yulang.SemilinearRowExamples` | 固定keyで全normalized guardが空の任意有限row graphについて、元のDerivesと計算した有限半線形表示の一致、実行可能なguard検査、複数seedを混ぜないこと、相互再帰・複数cycle・正負2座標の無制限な例 | 禁止点が残る一般graph、一般の半線形所属・包含・等価判定、source SCCからの制約抽出 |
| `Yulang.GuardedAffineRows` / `Yulang.CertifiedRowSummaries` | 指定座標とslot potentialの有限検査から全中間点のguard通過を導出、非空禁止点を含む複数cycleの半線形表示、固定keyの正規化と元の任意row AST problemの到達・Derivesの同値、検査成功から元の最小解への直接接続、全Slot列挙不要 | certificateの探索、検査を通らない一般guard問題の求解、一般の半線形所属・包含・等価判定、sourceからの制約抽出 |
| `Yulang.FiniteBooleanReachability` / `Yulang.BinaryCarries` / `Yulang.SemilinearDecisions` | 任意次元・任意符号の有限周期集合について、無制限の自然数係数を二進carryの有限到達問題へ変換し、半線形集合への所属・非所属を完全に判定。零周期・相殺・空集合・0次元も含む | 任意のguard付きgraphの半線形表示の構成、実用的な大入力性能 |
| `Yulang.FiniteAutomata` / `Yulang.SemilinearDigits` / `Yulang.SemilinearAutomata` | 全有限語についてのNFA包含・等価性、全整数vectorの符号付き二進表示、全表現での受理との一致、任意の半線形集合の包含・等価性・非包含時の整数反例の存在 | 全guard付きgraphの到達集合が半線形であること、最短反例の抽出、productionの計算量 |
| `Yulang.FiniteWorklist` / `Yulang.FiniteWorklistExamples` | 実際の到達状態だけを列挙する探索と全有限pathとの同値、有限全状態数による完全性と停止、NFAの全冪集合積を実行時に作らない包含判定、無限集合の共同被覆の実行確認 | 最悪時の指数的状態数の回避、言語に対する探索打切りや任意のfuel制限 |
| `Yulang.GuardedRowErasure` / `Yulang.AutomaticRowSummaries` | 正規化された元のrow ASTについて、各slot edgeの禁止点への到達不能性を自動検査し、成功時の半線形表示・所属・非所属を元のDerivesへ接続。外部potential・座標・Slotの有限列挙不要、既存の座標certificateが通る場合を包含 | guardが実際に到達する一般問題の求解。`none`はこの算法の未対応で、言語の拒否や非所属ではない |
| `Yulang.StructuralCut` / `Yulang.StructuralDecisions` | 既存の有限構造部分型preorder全体のcut除去、union/intersection・pair・variant・record幅/先勝ち・関数の型と二つの行の分散を含む完全な比較器、符号付き有限行に対する真偽・同値判定 | 未知型変数のbound探索、再帰値型、Simple-sub全体のextrusion/intrusion/generalization、sourceの推論器 |
| `Yulang.ValueBounds` / `Yulang.ValueBoundSolvers` | ground下界・変数間包含・ground上界から未知の値型を実際に構成するsolver、循環を含む有限graphの停止、全構造型割当てに対する最小性と成功・失敗の完全性、無限半線形latent rowを持つ入力と任意のSetRow割当てに対する完全性 | constructor内部に残る未知型の求解、再帰値型、最小解を多相主型と同一視すること、全Simple-subの一般化とsource全体への接続 |
| `Yulang.RecursiveValueBounds` | 元の再帰row制約から潜在行を解き、未知の値型を構成する入口、元のDerives解に対する健全性・最小性・解なしの完全性、未対応と矛盾の区別 | 一般のguard付きrow問題、任意のrow解と値型の同時探索。rowは元の再帰問題の固定最小解で解釈する |
| `Yulang.ValueBoundElimination` / `Yulang.ValueBoundEliminationExamples` | 既存TyTermの極性検査、正の内部未知型の存在量化の正確な消去、自由なparameterと行の保持、実際のprincipal恒等関数とsolverが構成した型族の同値、負の位置の無条件最小化への反例 | 一般化するparameterの自動発見、constructor内部の未知型を含むboundの解消、任意のlambda/applicationを推論するsource算法 |
| `Yulang.ValueUpperBounds` / `Yulang.ValueUpperBoundsExamples` | 上界の逆伝播と交差、空交差 `any`、全割当てに対する最大性・成功と失敗の完全性、負の位置の全インスタンスを保つ消去 | 正負が混在する変数の独立した既定化、nested bound、再帰値型 |
| `Yulang.ValueBoundSchemes` | flat boundの全解を表す制約のない有限型スキームの構成、任意の自由parameterが解になることと全解を再現できること、任意の混在極性の出力についての全インスタンス保存 | constructor内に未知変数を持つbound、再帰値型、sourceからの一般化interface発見 |
| `Yulang.ValueBoundSchemeInference` | 既存TyTermとfixed rowsから混在極性のprincipal output schemeを計算、元の全bound modelとのinstance exactness、rowsの保持 | 未知record spine、sourceからのgraph抽出 |
| `Yulang.TypeSimplification` | 正のみをnever・負のみをanyへ置く変数除去、認証された共起mergeとsandwich、自動有限passの全instance保存 | 全ての安全なmergeの発見、constructor分配則、唯一の表示標準形 |
| `Yulang.FiniteHorn` / `Yulang.NestedValueSolver` | 型constructor内の未知変数を扱う有限飽和、n²対での停止、独立モデル保存、rigid/row矛盾の拒否 | 単独では成功cacheからの再帰解構成。この接続は次のcoalescingで証明する |
| `Yulang.RegularValueTypes` | 全有限観察による独立な再帰値型意味論、有限型での保守性、guardedな循環導出の健全性、入力/出力の再帰例 | 最終的なas文字列、循環導出体系全体の決定手続き |
| `Yulang.RegularNestedModels` / `Yulang.RegularValueCoalescing` / `Yulang.RegularSchemeInference` | 任意自由parameterから元のnested graphの解を構成、元の全regular modelを再現、subsumptionを含む全instanceの主型性、実際の推論入口と解不存在の完全性 | 未知rowの同時求解、source全体のlowering、一般化・intrusion/T3との全統合、完全な表示標準形 |
| `Yulang.ConstraintNormalForm` | 任意の元Formulaを有限の存在的clauseへ変換、全Exprの元Typingとの同値、letの両枝・capture・結果slotとrowsの保持 | 個々のatomの求解、DNFの大入力性能、source全clauseがnested solverの対応範囲に入ること |
| `Yulang.RegularInferenceModel` | constructorと有限再帰blockに閉じた単一のInference.Model、有限graphの保存・反映、全自由parameterからの解構成と全instance一致 | surfaceのas表示、意味論を追加したrecord正規化 |
| `Yulang.TypeConstraintGraph` / `Yulang.TypeConstraintGraphEquivalence` / `Yulang.TypeConstraintInference` | 元TyTermの共有変数を保つgraph化、semantic realizerの反映、実際のsource型制約solverの全モデル・全出力instance一致、regular model不存在と拒否の同値 | 未知record tail、非対応位置のunion/intersection、未解決行と値型の統合入口 |
| `Yulang.RowFlowSchemes` / `Yulang.NestedRowRequirements` / `Yulang.TypeConstraintRowInstantiation` | core行の共有parameter scheme、shape飽和と行代入の可換性、全arrow行obligationの求解、元の行モデルの回復 | operation head・protect/release・residualを含む一般RowExprの制約消去 |
| `Yulang.ConstraintProblems` | 型・行の同一slotを保つclause分割、元Typingのsubsumption、全閉式から計算した問題のinstanceとの同値 | 各問題の求解や全構文の対応判定 |
| `Yulang.RecordTailBoundary` | 旧reference modelについて、同値tailの置換がrecordの同値を保たない反例、元principalの全instanceをproper spine一つで表せないこと | 決定38後の新モデルの反例、一般solverの不可能性 |
| `Yulang.SemanticRecords` | 旧構造・束規則と任意record head/tailの合同性からなる最小閉包、全旧部分型の保存、10.25のrecord型の同値、基本型が潰れないこと | 任意admissible tailのhead/幅の全義務、一般tail共変則、分配・bottom strictness、再帰型solver |
| `Yulang.SemanticRecordQuotient` / `Yulang.SemanticRecordQuotientInference` | 新しい合同関係による値型の商と全constructorのwell-definedness、任意Formulaと全閉core Typingのraw/商間の双方向保存、record literalの全instance、全coreの実際のgraph compilerとの同値 | 最終的な任意tail規則、商の表示標準形、graph残余制約の求解と自由parameter scheme |
| `Yulang.SemanticRecordAtoms` / `Yulang.SemanticRecordViews` / `Yulang.SemanticRecordAtomNormal` / `Yulang.SemanticRecordLatticeCheck` / `Yulang.SemanticRecordChecker` | 最小合同関係の有限ground型について、構造atomの有限化・proper record view・既存StructuralDecisionsへの接続・入力depthから計算する完全checker・計算されたatom比較を持つcut elimination | 追加tail規則のchecker、未知変数と正則再帰型の求解、row checker自体の構成 |
| `Yulang.SemanticRecordQuotientDecisions` | 上のrow checker/preorder前提の下での代表元不変性、商型の実行可能な部分型判定と意味的等号判定、Decidable/DecidableEqの構成 | 表示標準形やcanonical代表元、最終record関係の未知型solver |
| `Yulang.InferenceModelMap` / `Yulang.SemanticRecordInference` | model写像による任意Formulaの保存、反映・全射の明示前提下での双方向一致、任意の旧環境の型付け保存、literalの全instanceの有限record型による特徴付け | 旧関係と合同閉包の逆向き保存、全coreの実際の求解、表示標準形 |
| `Yulang.RecordConstraintSupport` / `Yulang.OpenRecordConstraintGraph` | 元の全coreからのpolar制約準備、未知tail参照を持つ全域compiler、任意modelでの全割当て・全instance・retractionの一致、union-join/preorder前提下の全core Typingとの同値 | 制約を満たす割当ての探索、充足可能性判定、自由parameterによる主型scheme、SourcePrincipalInferenceのRecordFree除去 |
| `Yulang.SemanticRecordVarianceBoundary` | head/幅・同値置換・既知field存在・冪等性・交換を含む明示した局所法則を満たすが一般tail共変性を満たさない有限のfield存在代数 | payload型・値の実行・inhabited性を含む言語全体のモデル、全仕様からの独立性、sourceの型付け不能 |
| `Yulang.RigidSemanticRecords` | 決定39のrigid要求tailへの共変性だけを加えた最小関係、旧関係の保存、任意admissible tailでのhead/幅、never tailの幅 | 一般tail共変性、分配、bottom strictness、opaqueな型同士でのhidden fieldの同一視 |
| `Yulang.RigidRecordFields` / `Yulang.RigidRecordDemands` | proper recordの最初のfieldによる比較、要求側maskによる任意供給tailの必要十分条件、hidden fieldを比較しないことの完全性 | 非rigid要求へのmask規則、未解決型変数の求解 |
| `Yulang.RigidRecordAtoms` / `Yulang.RigidRecordViews` / `Yulang.RigidRecordAtomNormal` / `Yulang.RigidRecordLatticeCheck` / `Yulang.RigidRecordDemandCheck` / `Yulang.RigidRecordChecker` | 新参照関係の有限ground checker・計算済みatom比較によるcut elimination、rigid要求の別入口とhidden payloadに依存しないBoolean結果 | 任意opaque要求でhidden比較を省く言語規則、未知変数・正則再帰型のsolver、row checkerの構成 |
| `Yulang.RigidRecordQuotient` / `Yulang.RigidRecordQuotientDecisions` | 新関係の商、意味的にrigidな要求tailへの共変性、代表元によらない実行可能な順序・等号判定 | 表示標準形、opaque hidden fieldを消す新しい同一視 |
| `Yulang.RigidRecordInference` / `Yulang.RigidRecordQuotientInference` | 旧型付け・前回商の閉式instance保存、raw/商のFormula・全閉式Typingの同値、新商モデルでの全core graph compilerとの同値 | graph残余制約の求解、全core自由parameter schemeと拒否完全性 |
| `Yulang.RigidRecordOpaqueBoundary` | 全rigid要求でのhidden fieldの除去、never/unionのopaque tailにおけるadmissibilityと非比較、隠れたpayloadに関する比較の正確な特徴付け | 全言語仕様からの独立性、source拒否、一般solver不可能性 |
| `Yulang.RigidRecordSourceBoundary` | 同じ元の閉record式に対するopaqueな2型の型付けとprincipal instance、両型の非比較と全rigid要求での一致 | opaqueな型を同一視する法則、主型schemeやsolverの不可能性 |
| `Yulang.RigidRecordValueInference` / `Yulang.RigidRecordValueInferenceExamples` / `Yulang.RigidRecordValueQuotient` | 全Data構文から自由parameter schemeを実際に構成、有限raw型と商型での全instance主型性・拒否完全性・元principalとの同値、opaqueな代替instanceの保持 | 一般lambda/application・let・field access、正則再帰値型、一般の制約graphの求解、SourcePrincipalInferenceとの統合 |
| `Yulang.RigidRecordFunctionScheme` / `Yulang.RigidRecordFunctionQuotient` | 引数recordにliteral fieldを足す関数族の有限descriptor構成、3自由値型と1自由行での全instance主型性、元principalと商モデルへの接続 | 任意の関数を推論するsource入口、正則再帰値型、全coreのRecordFree制限除去 |
| `Yulang.ShadowSemanticRecords` / `Yulang.ShadowRecordQuotient` / `Yulang.ShadowRecordQuotientInference` | 決定40の任意tailでの隣接同名field消去の最小閉包、商の型等号、旧型付け保存、全core graphと元Typingの全instance一致 | 一般graphの求解、自由parameterによる全core推論 |
| `Yulang.ShadowRecordNormalization` / `Yulang.ShadowRecordChecker` / `Yulang.ShadowRecordQuotientDecisions` | 新関係の有限ground完全checker、意味を保存する停止的正規化、計算されたnormal formsによるcut elimination、実行可能な商等号判定 | 未知graph変数、正則再帰値型、表示canonical化、row checker自体の構成 |
| `Yulang.ShadowRecordDemands` / `Yulang.SingletonRecordDemands` / `Yulang.SingletonRecordGraph` | 決定40のrigid要求の必要十分条件、全元coreのsingleton要求不変条件、実graph tagと既存参照内のerasure閉包 | 任意外部schemeへの無条件singleton化、未知slot値のsingleton制限、飽和済みgraphの完成 |
| `Yulang.ShadowRegularValueTypes` / `Yulang.ShadowRegularInferenceModel` | 既存正則carrierでのshadow等価・合同性、有限型およびfinite block埋込みの保存反映、旧/有限モデルからの型付け保存 | 一般tail参照のcoalescing、正則部分型のchecker、旧solverの新関係についての完全性 |
| `Yulang.RecordDemandInspection` / `Yulang.SourceRecordDemandInspection` | 元nodeだけを使う実行可能なrecord分解、有限/正則モデルの全割当て・全instance保存、元全core Typingへの接続 | 飽和と自由parameter解の構成、残余Models条件を除いた全core推論成功 |
| `Yulang.ShadowRecordValueInference` / `Yulang.ShadowRecordValueQuotient` | 既存の実データ推論算法について新raw/商モデルの全instance主型性、推論成功の完全性、拒否完全性 | 一般lambda/application・let・fieldを含む全core solver |
| `Yulang.ShadowRecordFunctionScheme` / `Yulang.ShadowRecordFunctionQuotient` | 同じopen-record拡張関数族の自由parameter schemaを新関係の全Typingと一致させること | 任意の関数のsource dispatcher、正則再帰型 |
| `Yulang.SourceDataRuntime` / `Yulang.SourceDataSafety` / `Yulang.ShadowDataSafety` | 元の第一階式のTyping・principal formulaから実eval成功と返り値の型適合、実データinfer成功から全商parameterで同じ値の適合、strict/poly letと実field lookup | 関数・branch・effect・再帰sourceの実行、literal具体payload、Rust/elaboration、意味論から部分型への完全性 |
| `Yulang.HandlerPermissions` | incoming actionのarm許可の実検査と診断、fresh境界後の全treeでの非capture、許可requestのdispatch、shallow継続、検査付きruntime入口 | sourceのmask抽出、mixed-origin action全体の許可推論、局所effectへの一律mask適用 |
| `Yulang.RigidRecordVarianceBoundary` | 前回の局所field存在代数がrigid要求への共変性を満たし、旧右辺unionがnonrigidであること | payloadや実行を含む言語全体のモデル |
| `Yulang.JointConstraintInference` | 元の型・行制約から共有parameterのregular schemeを計算、全値型・行モデルおよび全出力instanceの一致、対応範囲での失敗の完全性 | right-join等の非対応行制約、一般のRowExpr求解 |
| `Yulang.SourceConstraintSupport` / `Yulang.SourcePrincipalInference` | record構築以外の全既存Exprが対応範囲内である証明、元の式からの実際の推論、計算された全scheme instanceと元Typing/principalの一致、拒否と型付け不存在の同値 | record構築、surface elaboration、effect operation/handler・SCC・T3・role/castとの統合 |
| `Yulang.SourceInferenceExamples` | 恒等関数の型・行共有、定数関数の負位置のany化と自由な入力行、実際のsource推論結果とcanonical familyの全instance一致 | 返り値blockの構文的な表示簡約 |
| `Yulang.SignedSourceInference` | 上のsource主型定理を無限・符号付き集合行へ具体化、既存effect algebraとの恒等RowView | protect/release/residual制約を生成する全effect ASTの同時求解 |
| `Yulang.ValueInference` / `Yulang.ValueInferenceExamples` | 既存Exprのvar/lit/branch/letE/pair/variantから型を構成し、元のTyping・principal formulaとの成功時の主性と失敗の完全性を証明、値letの両経路、未対応との区別 | 評価時effectを持つ式、一般のlambda/application、SCC、variantのtag合流・case残余、parserからのelaboration、表示の完全な標準形 |
| `Yulang.SemilinearNormalization` / `Yulang.SemilinearFastInclusion` | 零・重複周期と同じ成分の除去の意味保存、単一周期への全座標を使う正確な所属判定、健全な包含の高速成功と完全なNFA判定へのfallback、最適化前後のBoolean結果の一致 | 全半線形集合の最小正規形、異なる成分の共同被覆を一成分比較だけで判定すること、一般の多項式時間 |
| `Yulang.SemilinearRowAlgebra` | 有限key支持と無限の整数重み集合を持つ行の包含・等価性、重複keyの和と欠けたkeyの空解釈、既存SetRow代数との一致、その行を潜在行とする有限ground構造型の比較 | 未知型変数・再帰値型の求解、元のrow制約からの解抽出は別層 |
| `Yulang.SolvedRecursiveRows` | 元の有限row制約から到達可能な全keyを列挙し、guard検査が通る場合の行全体を構成、元のDerives最小解について包含・等価性・非包含の反例存在を完全に判定 | 一般のguard付き問題、すべての後続具体化での開いた行変数の等価性。未対応の`none`と否定の`some false`は区別する |
| `Yulang.RecursiveRowQueries` / `Yulang.RecursiveRowConstraints` | 任意の既存row式をfreshな出力slotへ接続して元の最小解を保存、固定した半線形上界の有限列について元の下界・上界の充足可能性を判定、否定結果と全モデルの不存在の一致 | 未対応のguard問題、未知上界との相互求解、開いた行の全具体化に対する上界保証 |
| `Yulang.StructuralRowResolution` / `Yulang.SemilinearRowQuotient` | 行の表現変更による部分型の保存と単射な意味符号化による反映、同じ集合を表す半線形行を商で同一視し、元のSetRow上の部分型関係を全有限ground型について完全に判定 | 未知の値型変数や再帰値型の求解、半線形集合の最小正規形の構成 |
| `Yulang.StructuralRowTraversal` / `Yulang.SolvedRecursiveTypes` | 型に実際に現れる行slotだけを解き、元の再帰最小解を各行位置へ代入した有限型の部分型・相互部分型を完全に比較、未対応との区別、行を持たない型に無関係なguardの成功を要求しないこと | 未知値型の推論、すべてのモデルや後続scheme具体化に関する部分型関係、source型の抽出 |
| `Yulang.InfiniteOperationalCorrespondence` | 同じresolved式の既存principal制約を任意の集合行で解釈した解から、同じ実行木の全request上界・返却値の構造型解釈・fresh境界非captureまでの接続。handlerの各armの上界と元の継続行は型判断から導出 | 無限行solverの完全性、source elaboration、異種payload署名、runtimeの再帰構文、潜在closureの衛生wrapper挿入 |
| `Yulang.RecursiveEffects` | 全既存core式とrequest・boundary・shallow handlerを同じ再帰ASTに置く有限制約生成、任意の入れ子について独立な型判断との双方向一致・制約schemeの主性、値制限付き多相letと署名のambient slotの保持 | operation-local多相・roleを含む統合、再帰SCC、source elaboration、制約solver、型付けからruntime安全性への接続 |
| `Yulang.RecursiveEffectsConservativity` / `Yulang.RecursiveEffectExamples` | effectを含まない全core式で実際の生成formula・principal schemeを保存する等式、旧型判断との一致、入れ子handler・多相let・computation引数・保護と負債の正例と負例 | source parserからの翻訳、全制約solver |
| `Yulang.OperationalTyping` / `Yulang.OperationalTypingExamples` | 形状解決済みの単相核の実行可能なcheckerと独立型付けの一致、checker受理から実際の全requestの推論行上界と返り値の潜在関数の健全性、shallow継続・複数回再開・arm再送出・格納callbackの実行例 | 未知shapeの推論、一般再帰、source elaboration、異なるpayload型を持つoperation、値内部への衛生変換の挿入 |
| `Yulang.OperationalCorrespondence` / `Yulang.OperationalCorrespondenceExamples` | 形状解決済み式の消去結果に対する任意の既存再帰型判断から実行上界・返り値の意味を導くこと、union/intersection・値制限付き多相letの解釈、実際のprincipal formulaの解から閉式の全request上界への接続、具体的な解と空行解の拒否 | annotated checkerとの受理集合の一致、未知shape・再帰型の推論、異種operation署名、sourceの注釈や潜在値の衛生変換のelaboration |
| `Yulang.CheckedHygiene` | checker受理または実際のprincipal formulaの解から実行上界を導き、推論行のfreshな表現または実際の座標割当てから原点条件・新境界での非captureを導くこと | sourceが全境界を正しく割り当てること、payload・response・返り値の潜在closureのtransport |
| `Yulang.OperationalTransport` | 実際のcomputation引数を持つ関数・pair内の関数・request treeの高階wrapper、任意の値での両方向の相殺、対応する引数との呼出し・sequencingの等式 | sourceでのwrapper挿入、任意の未変換引数でのdispatch不変性、freshな世界へのclosureの構成 |
| `Yulang.OperationalTransportTyping` | 有限行checkerの型・部分型・実行時適合性の変換前後の同値、既存checker受理から潜在closureまで包んだ同じ評価の型保証 | 未知shapeの推論、sourceでの境界選択、非captureに必要な原点条件の発見 |
| `Yulang.InfiniteOperationalTransport` | 任意の無限集合行を含む既存構造型と高階実行値の対応、principal解から潜在closureのinterface、静的出力行の原点条件から返却関数の呼出しの非capture | sourceでのwrapper挿入、古いclosureのfresh化、record・variantのruntime表現、計算の停止、Simple-sub全体 |
| `Yulang.OperationalTransportSubtyping` | 任意の集合行について、既存の構造部分型関係全体とcomputation部分型の変換前後の同値。recordの幅・先頭field優先、variant、union/intersection、関数の両方の行も含む | 未知型boundのsolver、record・variantの実行時表現、source elaboration |
| `Yulang.OperationalTransportExamples` | checkerで受理される実際の式の評価による格納callback・遅延producerの保護と解除、変換後入力型との適合、負の出力差分の復元、内側globによる外側保護の保持 | sourceによるwrapperの自動挿入、静的原点条件なしでの一律の非capture |
| `Yulang.FiniteReachability` | 有限隣接リストから計算する到達集合と独立な有限経路の判断の一致、空の始点集合からの到達不能性、辺・始点の順序と重複に対する不変性 | source の依存関係抽出、未具体化の多相 cast 集合の有限性、実用的な計算量 |
| `Yulang.EvaluationOrder` | 名前解決済みの有限宣言・module 文からの評価依存計算と独立な推移的依存判断の一致、computed 自己依存・未来の computed binding の拒否、受理された初期化・文の全依存が元の順序で利用可能なこと、lambda による遅延と直接適用時の依存の復帰 | source の名前解決、局所 closure/alias や格納された関数のフロー、任意の高階 callback の実行が依存判断に含まれること、全言語の副作用順序の保存 |
| `Yulang.EvaluationSafety` / `Yulang.EvaluationReads` | 名前で決まらない呼出しへのmodule全体の関数本体近似、独立なCBV読み取りprefixの上界、closure由来の保存、局所・返却・格納closureの読み取り安全性、既評価prefixからの参照先の利用可能性 | source elaboration、外部由来closure、可変store、計算全体の停止・progress。module内のlambda由来とsource位置の構造を明示 |
| `Yulang.Initialization` | 同じresolved本体のSCC生成と二つの初期化検査への接続、値制限の一致、型の割当てによらないcomputed cycle拒否、生成制約から実際の読み取り先の先行性と既評価prefixでの値の存在を導くこと | 全注釈を持つsource moduleのelaboration、module文の結果型検査、全言語のprogress/preservation |
| `Yulang.Methods` | unionの相異なるreceiver候補の0・1・複数の三分、全memberから選択先へのcast検査、選択と変換検査全体の順序不変性 | method lookupの優先順位・可視性、未確定receiver下界の保留、source unionの正規化。refは特別扱いせず全体を照合する（`ImplHeads`） |
| `Yulang.MethodResolution` / `Yulang.FrozenMethods` / `Yulang.FrozenMethodExamples` | SCC最終snapshotの未知receiverで可視role候補0/1/複数を決定、既知の構造field優先、独立な選択・型判断と実際のprincipalの一致、任意の後続代入後も選択と宣言要求を保持、Size/boxの受理・拒否 | SCC知識の算出、nominal/inherent/effect methodのlookup全体、scopeと宣言tableの整合性検査、source全体のelaboration |
| `Yulang.Casts` | 普通の適合性と別の境界変換判断、関数の入力反変・出力共変、tuple・record field・variant payload の共変変換の実行可能な検査と正確性、固定nominal引数を変えるには外側全体の規則が必要なこと | 普通の部分型の決定手続き、effectを持つcastの実行意味、等価な型表記の正規化、未具体化のcast宣言のground化 |
| `Yulang.PureCasts` | 空の符号付き行によるcast宣言検査、チェック済み本体から合成した構造変換の純粋性、境界挿入と関数wrapperによる実際のrequest tree・任意の行上界の保存 | 宣言本体のoperationalな行上界をsource型付けから導くこと、`Casts.Boundary`からtyped planを合成するelaboration、異なるcast経路の値の一致 |
| `Yulang.CastGraph` / `Yulang.CastExamples` | 有限ground登録の検査と深さ制限なしの経路判定、直接重複拒否と複数の間接経路許容、適合時の変換省略、nominal全体からpair・関数・unionへのunbox、source unionの全member検査 | 多相endpoint探索とのsource表現の接続、経路コードの合成、異なる経路の実行結果の一致。登録された直接sourceはnominal/baseに限定 |
| `Yulang.ParametricCastRules` / `Yulang.ParametricCastUniverse` / `Yulang.ParametricCasts` | 多相castの宣言検査と全置換後のサイズ非増大、入力と有限宣言から導く有限alphabet・サイズ上界・到達型集合、任意の有限経路との同値を満たす実行可能な探索、等サイズ循環と固定ground型の拡大の許容 | 明示規則のendpoint探索からsource境界へのelaboration、直接規則の重複・重なり診断、構造変換を混ぜた全言語のsolver、実用的な計算量 |
| `Yulang.LiteralCasts` | list literal の元の構築位置を保持した変換計画、期待要素型が決まった場合の全要素の境界検査、EOFで期待型がない場合の元の要素型のunionと変換省略 | 弱い要素型を解くsolver、cast本体の実行・effect、構築済みlistの変更、空unionを含む表示上の正規化 |
| `Yulang.NominalConstructions` | 任意の有限個の不変パラメータを持つstruct/enum/list構築、各元の位置での境界検査、パラメータごとのEOF unionと変換省略、構築子・tag・位置の保存、既存list plannerへの厳密な特殊化 | 全パラメータ出現位置のsourceからの収集、弱い型変数の解探索、未使用パラメータの既定値・公開可能性 |
| `Yulang.Variants` / `Yulang.VariantsMerged` | support の分割・残余の最小性と最大性、同一 tag の payload 合流と tag 一意性、合流と残余の交換、tag 全体の選択・除去、全 tag 処理と空行の同値、merge 準同型による payload 置換 | payload 内部の source pattern 網羅性（2026-11-05 の決定により対象外）、guard 付き arm の被覆（章3b.4により数えない）、payload の部分型 solver、open row の solver、source 全体の case 検査への接続（保守的な核との接続は `CaseCoverage` で証明） |

`Variants.Merged.Row` は tag の重複がない有限行を表す。`normalize merge` は同一 tag の payload を入力順の右結合で合流し、`lookup_normalize` はその結果を `mergeAll` と一致させる。該当 tag がなければ `none`、一つならその payload、複数なら指定した `merge` を用いる。tag の列順は最後の出現順の逆順である。これらの定理に結合則・交換則・冪等則は不要で、入力の並べ替えや重複挿入で payload が等しくなるとは主張しない。`normalize_map` だけは `f (merge a b) = merge' (f a) (f b)` を仮定する。`variant_union_upper_bound` は既存の構造部分型規則から `variant l a ∪ variant l b ≤ variant l (a ∪ b)` の一方向を導く。case の入力型を閉じる推論器や、部分型モデル全体の正規化を証明したものではない。

`Roles.Term` は変数と有限引数列を持つ型構築子だけを表す。型構築子・型変数を各1と数え、複数引数の head / where 条件の大きさは型サイズの和とする。role 識別子と引数列の spine は数えない。`Impl.WellFormed` は各 where 条件について、head より真に小さいことと、各変数の出現回数が head を超えないことを要求する。`Term.subst_size` / `args_subst_size` は、置換後のサイズを元のサイズと各変数の出現回数に基づく増分の和で表す。`size_decreases` はこの二条件から、任意の置換の下での真の減少を導く。`resolve impls wf goal` は全 impl の適格性の証明を受け取り、goal の引数サイズを測度として停止する。`wellFormed_cons` は、impl の追加時も適格性が宣言ごとの条件であることを示す。適格性の診断を返す source 宣言検査器は未接続である。

照合は impl の変数だけを置換し、goal の変数は rigid に保つ。繰り返し現れる変数には同じ型を要求する。`matches_iff` は実行可能な照合と存在的な head 一致の同値を、`constraint_variables_in_head` は head にない変数が where 条件にもないことを示す。`matched_constraint` により、照合に使う置換の未使用変数の既定値は where 条件の結果に影響しない。`Impl.key` は宣言の識別子であり、同じ head / where を持つ別宣言も別候補として表せる。同じ impl 値の繰り返しは同じ宣言として除重複する。入力リストは可視な impl 集合を表し、import・可視性の検査は扱わない。

曖昧さは where 条件を調べる前の head 一致で判定する。head 候補が二つ以上あれば、条件の成否によらず `ambiguous` となる。一意な候補の全 where 条件を調べ、子の `ambiguous` は兄弟の `noImpl` より優先する。`resolve_resolved_iff` と `resolve_noImpl_iff` はこの成功・失敗条件を正確に述べる。`Derives` は resolver を参照しない存在的な宣言的導出であり、重なる impl でも導出自体は存在し得る。`resolve_sound` は成功から導出を、`resolve_complete` は導出と到達する head の非重複から成功を導く。`ReachesOverlap` は一意な候補の条件をたどって重なる head に至る有限経路であり、`resolve_ambiguous_iff` はその存在と `ambiguous` を同値にする。`Examples` は二重 list の成功、str impl の不在、rigid 変数、変数を複製する条件の拒否、サイズが増える Foo impl の不適格性と有限導出の不在、head が重なる例を検証する。Foo の有限導出の不在は適格性を仮定しない帰納法で示し、宣言的導出の健全性と解決の実行可能性を区別する。

`Yulang.RolesAssoc` の `Roles.AssocImpl` は既存の `Impl` を包み、関連型名から右辺 `Term` への辞書を添える。既存の `Impl` と定理は変更しない。`RoleDecl` は引数数と宣言済みの名前・default を表し、default の変数は `0..arity-1` の引数位置だけを指す。辞書の名前の無重複性と、同じ元の impl に同じ辞書を対応させる `AssocEnv.coherent` は表現上の不変条件である。source の重複宣言の診断や意味は定めない。`AssocHeadVars` は明示定義の変数が head に現れること、`AssocComplete` は署名との引数数の一致と必須定義の充足、`AssocDeclared` は未宣言名を提供しないことを要求し、`AssocWellFormed` は全 impl に対してこの三条件を要求する。

`assocOf` は既存の `resolve` が成功したときだけ、一意な impl の右辺を head の照合置換で一度具体化する。明示定義がなければ、default の引数位置を goal の型引数で置換する。`Term` に関連型参照はなく、別の関連型の展開や新しい再帰・停止測度は不要である（章6.3、確定, 2026-11-05）。`assoc_independent_of_constraints` と `assoc_explicit_eq` は、解決成功を前提として値が選ばれた impl と照合置換で決まり、where の解決導出によらないことを示す。`assoc_derivation_agrees` / `assoc_derivations_unique` は、resolver を参照しない `AssocDerives` の二つの導出でも値が一致することを示す。Paterson 適格性と関連型適格性の下で、`assoc_total_closed` は、解決済み goal の**宣言済みの各名前**について結果が存在し、その変数がすべて goal に現れることを証明する。`assoc_unique` はその値の一意性を示す。`assoc_explicit_size` は明示定義について既存の `Term.subst_size` と同じ正確なサイズ公式を与える。`AssocExamples` は str・box・定数と引数位置の default・明示定義による default の上書き・rigid な goal 変数の正例と、head 外の変数・必須定義の欠落・未宣言名の提供を拒む負例を検証する。関連型を含む method 署名や where 条件との単一化は `RolesAssoc` 単体の対象外である。関連型選択から普通の等式を追加する規則は確定済みで、`RoleConstraints` がその接続と解集合の順序不変性を扱う。未知の置換を探索する全体solverは別に必要となる。

`Horn.solve` は全 `2^n` valuation を列挙する参照実装で、実用solverの性能を主張しない。有限性は `Fin n` という入力型に明示されており、任意のYulang制約がそこへ落ちるという未証明の仮定を入れていない。

`FiniteReachability.closure` は有限グラフの始点と辺を Horn 制約に翻訳する。`closure_exact` は、結果の真の成分と、始点から有限回辺をたどる独立な `Reach` 判断とを双方向に対応させる。経路長の打切り・非循環性・解決成功の仮定はない。`closure_empty` により、循環する辺だけでは到達点は生じない。評価依存と ground cast の探索で共有する基盤であり、このモジュールだけでそれらの source 規則との対応を主張しない。

`EvaluationOrder` は局所変数と有限個の global 宣言を区別する式を入力とする。評価位置に現れた global 名から、その宣言の関数本体へ推移的に進む。関数を引数として渡す場合も同じ辺をたどる。名前付き宣言の `invokedReferences` は先頭の引数lambdaだけでなく、分岐の結果やcallee位置から返るlambdaも再帰的に開く。独立な `InvokedUses` 判断との一致と、旧来の有限回の直接適用で見つかる依存をすべて保持することを証明した。`check_exact` は computed binding の初期化と、位置を持つ module 文の両方について、実行可能な判定と独立な `Ordered` 判断が一致することを示す。到達した computed binding の位置には真の不等号を要求するので、自己依存・未来への依存は拒否される。関数だけの相互再帰を禁止する規則はない。

`lambda_no_dependency` は lambda **構築時**の依存がないことを示す。`applied_lambda_preserves_body_dependency` は直接適用すれば本体の依存が戻ることを示し、curried な直接適用にも負例がある。`accepted_initializer_earlier` / `accepted_statement_available` は、この依存判断で必要とされる computed binding が、並べ替えていない宣言順序で先行することを証明する。任意の source callback の実際の呼出しをこの判断が過大近似することはまだ示していない。分岐からlambdaを返す名前付きfactoryの即時呼出しには拒否・受理の回帰例がある。この基礎層だけでは局所変数を通るclosureを追わないため、決定23に従うmodule全体の近似と実行時の接続を、次の `EvaluationSafety` / `EvaluationReads` に追加する。

`EvaluationSafety` は、名前で決まらない呼出しで、宣言とmodule文に含まれるすべてのlambda本体の参照を候補にする。直接のlambda、または宣言本体がlambdaである名前だけは、その本体を使う。`EvaluationReads` の `Eval` と `Reads` はcheckerを含まないCBV意味論で、後で発散する実行の読み取りprefixも扱う。`Reads.read` はstoreに値があることを要求せず、未初期化の読取りも表せる。`reads_needed` はmodule由来のclosureを持つ任意のstore/environmentに対し、実際の読みが計算した依存集合に入ることを示す。`eval_closed` はclosureと捕捉環境の由来を実行に沿って保つ。`accepted_read_initialized` は、先行するcomputed bindingの結果を記録したprefix storeに対し、読まれる値の存在を導く。`initialize_next` は実際の初期化結果を記録するとprefix不変条件が進むことを示す。さらに `EvaluatedPrefix` は空storeから始めたcomputed宣言の実際の初期化履歴を表し、`EvaluatedPrefix.invariants` がclosureの由来と先行値の存在を導く。`accepted_prefix_read_initialized` はこの履歴から、現在の式の終了を仮定せず読み取り先の値が存在することを示す。位置を進めるときは、その位置の宣言が一意であることを要求する。間にあるmodule文の実行・終了や、その履歴全体の存在は別の義務である。これは保守的な上界であり、実際に読まれる集合との同値や全実行の停止を主張しない。

`Initialization.toCore` は同じ依存構文の本体を型推論の式へ翻訳し、global名の添字をlambdaの局所束縛の数だけずらす。有限のscope検査で、不正な局所添字がglobal名を指してしまう場合を拒む。`value_restriction_agrees` により両側のcomputed分類は一致する。`generate_exact` は、生成制約の解と「同じ本体の同時単相型判断＋初期化順序判断」の一致を示す。`computed_cycle_rejects_generated_constraints` は任意のモデル・割当てについて、computed cycleが合成後の生成制約を満たせないことを示す。対象にはunit・Boolean・pairのprojectionを含み、module文はこの層では依存だけを検査する。生成器は `EvaluationSafety.check` も要求し、`generated_initializer_read_earlier` は実際の読み取りprefixに対して先行性を導く。`generated_prefix_initializer_read_initialized` は、生成制約の解と実際の既評価prefixから、次の初期化の読み取り先に値が存在することを導く。現在の読み取りの被覆や利用可能性を別の前提として要求しない。

`Methods.resolve` は member ごとの method の有無が確定した段階を扱う。`resolve_unique_iff` / `resolve_missing_iff` / `resolve_ambiguous_iff` は、それぞれ相異なる候補が 1 個・0 個・2 個以上である条件を示す。`select_ext` はリストの membership が同じなら結果も同じことを示すため、順列だけでなく同一 member の繰り返しも曖昧さを増やさない。

`CheckedRoles.checkImpl` は各 where 条件のサイズ減少と変数出現回数を検査する。条件側の変数番号上界より上の出現回数は 0 なので、有限回の検査と無限個の変数についての `Impl.WellFormed` が一致する。`CheckedRoles.resolve` は全宣言を先に調べ、成功した場合だけ既存の停止性証明付き `Roles.resolve` に渡す。`resolve_exact` は適格性を前提にせず、結果が成功することと「宣言集合が適格で、導出があり、到達する head に重なりがないこと」の同値を示す。不適格な宣言は、その goal の解決で使われなくても拒否する。

`RoleConstraints.addAssociated` は既存の関連型解決が返した値を、普通の型変数との等式として蓄積する。`Store.permutation_preserves_solutions` は一つの選んだ置換だけでなく、**すべての置換**について解集合が順序に依存しないことを示す。`conflicting_constraint_rejects` は同じ変数への char と str の要求が、後からの代入で上書きしても解にならないことを示す。`Store.check_dichotomy` は固定した置換での整合・矛盾の二分であり、解となる置換の存在判定器ではない。

`Casts.accepts_exact` は、与えられた普通の適合性の判定と明示castの探索を用い、独立な `Boundary` 判断と実行可能な追加変換の検査を対応させる。適合すればそのまま通し、不一致の場合だけ構造に沿った変換を調べる。recordはfield名で照合し、既存の構造型モデルと同じく最初のfieldが後の同名fieldを隠す。`union_mismatch_iff` は不一致の場合に全memberの検査が必要なことを示す。無条件の `union_boundary_iff` では、普通の適合性がunionの除去則を満たすことを明示的に要求する。`structural_union_boundary_iff` は既存の `StructuralBase.Subtype` と一致する適合性からこの前提を導くが、本層自体は部分型判定器を実装しない。有限構造型の判定は `StructuralDecisions` で別に実装・証明する。

このground型構文で、登録先の同一性と固定nominal引数には構文的等号を用いる。nominal引数内のunionの並べ替えなど、意味的に等価な型を同じ表現にする正規化は前段の課題である。`equalityCompatibility` は検査の具体例用の適合性であり、Yulangの部分型solverを置き換えるものではない。

`CastGraph.Registry.find_exact` は、有限のground型の登録と、先に証明した有限経路判断を結ぶ。登録は型ごとに一つの頂点を持ち、同じ直接のsource/target対の重複を拒否する。異なる間接経路が合流するdiamondは許容する。`compatible_kept` は適合する境界で変換探索を使わないことを示す。`Methods.checkCall_exact` はmethodを持つ相異なる型がちょうど一つであり、すべてのreceiver memberからその型への境界変換が成立することを要求する。`checkCall_perm` はこの変換検査まで含めた結果の順序不変性を示す。例は固定した`list user_id`から`list int`への要素castの不許可と、list全体の明示規則による許可を区別する。 `cast(x: box 'a): 'a` の具体化ではtargetがpair・関数・unionにもなり得るため、直接sourceのnominal/base条件を保ちつつtarget制限を外した。`nominal_mismatch_iff` は任意のtargetについて外側全体の規則を要求する。source unionは引き続き全memberを個別に検査し、whole-unionだけのoracleでは欠けたmemberを隠せない。

`ParametricCastRules.Rule.substitution_nonincrease` は、targetのサイズと各変数の出現回数がsource以下なら、どの置換後もサイズが増えないことを証明する。固定したground castはサイズを増やしてよいので、全到達型には初期型のサイズと宣言のtargetサイズの最大値を上界として使う。構築子の有限性も仮定せず、初期型と有限個のtargetからalphabetを作る。`ParametricCastUniverse.reachable_types_finite` はこのalphabetとサイズ上界から計算した有限リストが、すべての有限cast経路の到達先を含むことを示す。等サイズの循環そのものは許される。`ParametricCasts.query_success_iff` は「宣言が適格、出発型がground、独立な明示規則の経路が存在すること」と成功を同値にし、`query_failure_iff` は同じ検査済みの領域で経路の不在と失敗を同値にする。有限instanceグラフは入力ではなく、証明済みの有限リストから実際に構成する。この探索は全候補型とBoolean valuationの列挙による参照実装で、実用的な性能は主張しない。構造的な持ち上げを自由に混ぜた全言語の探索とは区別する。サイズはnominal引数の内部も数える `Roles.Term.size` であり、構造変換の停止測度でnominal引数をopaqueにする `Casts.Ty.size` とは用途が異なる。

`LiteralCasts.finish_exact` は、保持された各要素の構築位置と元の型に対し、期待要素型が与えられた場合だけ境界検査を要求する独立な `PlanTyping` と実行可能な計画作成を対応させる。どちらの場合も元の構築位置を保持する。EOFまで期待型がなければ、元の型の列をunionとして記録し、要素の命令はすべてkeepになる。これはコンパイル時に保留された構築位置へ変換を割り当てる規則であり、すでに構築したnominalなlistの型引数へcastを通す規則ではない。`expected` を決める弱い変数のsolverは別に必要である。

`PureCasts.Declaration` は実際の `Directed.Computation` 本体と、その推論行による上界を持つ。宣言の検査は行全体の空性を要求し、保護されたheadや負の差分も純粋と誤認しない。`Plan.run_eq_pure` はチェック済みの基本変換から合成した任意の有限planの純粋性を導く。`insert_requestTree` は返り値を除いた実際の要求木（payload・継続の分岐・符号付き重みを含む）を保存し、`insert_bounded_iff` は任意の行上界について同値を示す。関数の `wrapper_requestTree` は、変換後の引数で元の関数を呼んだ場合との対応である。入力値を変える前後で同じ実行になるとは主張しない。宣言本体の上界をsource型付けから導くことと、境界判断から実行planを合成することは別の接続義務である。

`NominalConstructions` は各元の構築位置を有限の不変パラメータslotへ対応させ、同じslotに属する全値を検査する。未解決のslotは、そのslotに属する元の型だけのunionを記録して変換しない。複数field・別々のパラメータ・enum tagの例があり、`finish_literal_exact` は一つのslotのlist構築を旧 `LiteralCasts.finish` へ射影すると、失敗も含め結果が厳密に一致することを示す。出現しない未解決slotは `unionOf []` という記述のままであり、bottomや既定型への決定・公開可能性をこのplannerで作らない。

`ImplHeads` は名前付き変数を偶数、各holeを別の奇数の識別子へ下ろす。`anonymous_occurrences` は任意の有限headと任意の匿名識別子について、割り当てた範囲では一回、範囲外では零回の出現を証明する。`named_occurrences` は名前を共有する箇所の出現回数を保ち、whereの名前は匿名識別子へ触れない。`two_holes_accept_all_types` と `repeated_name_matches_iff_equal` は任意の二つの型について、この違いを実際のhead matcherで示す。refも同じ全体照合を使うため、intのmethodをrefの中身へ自動委譲せず、`ref _ int` の特化は任意のeffect引数に適用できる。

`EffectExamples` は、同じfamilyの保護されたtail、境界ごとの解除、繰り返した保護、型引数を含むkey、shallow/multi-shot、handler armが新しく起こすeffectを検査する。nested `sub` の核の例は`0`、保護を消した比較例は`2`と計算される。これらはsource例に対応して手で構成した核の式で、parserからの翻訳の正しさを主張しない。

`shallowHandle_bounded` は、value armとoperation armの実行時effect上界を前提として、結果のeffectが`residual input ++ armEffects`で抑えられると証明する。継続の上界には元の入力行を保つ。この前提を型付けから導くsource handler推論器まで証明した、とは読まない。

## 高階の衛生性

`HigherOrder` のerase解除では、先に解除してから保護する往復が壊れる。`Directed` は許可されていないkeyについて、各境界の整数weightを保護で `+1`、解除で `−1` だけ変える。同じ境界と同じ許可maskの一対について両方向の相殺が成り立つ。handlerがcaptureできるのは、keyが一致し、すべてのweightが0のときだけである。

`DirectedHigherOrder.transport_opposite` は、product・sum・list・arrowで構成する任意の有限shapeと、その任意の値に対してこの相殺を証明する。関数の入力では方向を反転し、戻りcomputationと値では方向を保つ。新鮮性・weightの上限・fuelの仮定はない。

一方、非captureには由来の条件が必要である。weight `−1` に `+1` を足すと可視になるため、任意の符号付き入力を保護すれば必ず非captureになるとは主張しない。`guard_arrow_noncapture` は、反変方向に引数を変換した後の関数呼出しについて `ZeroAt` を仮定する。

`contravariant_debt_preserves_local_callback` は、callbackを奪う内側handlerの結果 `99` と、transportを入れて呼出側のhandlerへ届く結果 `7` を比較する。引数側の負の差分が内側でのcaptureを阻止し、帰りの正の差分が元の可視性を回復する。

`FreshBoundaries` は、古い境界を単射で埋め込んで新しい座標を割り当てる。既存の負の重みも保ったまま、新座標での `ZeroAt` を構成する。`FreshRowInference.fresh_eval_zero` は未知tailを含む全 `RowExpr` で同じ条件を導く。`CheckedHygiene.inferred_fresh_origin` はその静的な行の表現とchecker受理から、実際の評価木の原点条件を得る。行の表現は明示的な前提であり、checker自身がsourceの境界割当てを発見したとは扱わない。

`CheckedHygiene.closed_checked_boundary` は閉式のchecker受理だけから、評価木を実際にfresh化して保護した後の行上界と、任意の内側shallow handlerによる非captureを結合する。action・armの上界や `ZeroAt` は入力に要求しない。このfresh化は即時request treeに作用し、返り値の型は元の `Value n` のままである。値の内部に格納されたclosureを新しい境界へtransportする定理とは区別する。

`CheckedHygiene.principal_fresh_boundary` は同じ結論を、実際の `RecursiveEffects.principal` の解を入口にして導く。`OperationalCorrespondence.principal_effect_bound` によってruntime上界を構成するため、annotated checkerの受理を別途仮定しない。

`OperationalTransport` は上の値渡しの模型ではなく、実際の `OperationalTyping.Value`・`Tree` に高階wrapperを定義する。関数はcomputation引数全体を逆方向へ戻し、呼出し結果のrequestと返却値を順方向へ写す。`value_opposite`・`tree_opposite` はすべての有限resolved shapeについて両方向の相殺を示す。`value_apply_tree` は関数と入力interfaceをともに写した呼出しの正確な対応であり、未変換の引数に対するdispatchの不変性ではない。

`OperationalTransportTyping.valid_iff` は有限行checkerの型について、`InfiniteOperationalTransport.compHolds_iff` は任意の集合行を持つ既存構造型について、変換前後の型と実行の対応を双方向に証明する。後者は無限行・負の重み・型のunion/intersectionを許す。`closed_inferred_transport_valid` と `principal_transport_valid` により、checker受理または既存principal formulaの解から、即時requestに加えて返却・格納されたclosureの潜在interfaceも導く。runtimeのshapeはatom・pair・arrowであり、record・variantの実行時表現までは追加しない。

`InfiniteOperationalTransport.guarded_call_noncapture` は、型に適合する変換後の引数と、元の出力行の静的な `ZeroAt` から、保護した呼出しの非captureを導く。実行時の上界と原点条件は関数の型から構成する。`principal_guarded_arrow_calls` は、この保証を変換後の評価が返す各closureへ接続する。これは `AllReturns` の保証であり、値が返ることや停止性を主張しない。`fresh_output_call_noncapture` は、既に拡張された境界集合で型付けされ、出力行が `liftRow` である関数への系であって、任意の古いclosureをfreshな世界へ持ち上げる構成ではない。sourceでwrapperを挿入するpassは別の義務として残る。

`OperationalTransportSubtyping.subtype_iff` は実行時の解釈とは独立に、既存の `StructuralBase.Subtype Included` 全体を保存・反映する。recordの幅と先頭field優先、variant、推移則を含む。`comp_subtype_iff` は実際の集合行推論モデルの `Inference.Comp.le` まで接続する。したがって、この型変換だけで新しい部分型関係を作ったり、元の制約を失ったりしない。未知のboundを解くことまでは意味しない。

`OperationalTransportExamples` はcheckerで受理される既存の式を評価する。即時境界だけでは内側handlerがpair内のcallbackを奪い `99` を返すが、高階wrapperでは要求が通過し、対応する解除後に呼出側がpayload `7` を受け取る。callbackを生成する途中のrequest `13` も、computation引数全体の反変変換で保持する。混在した由来のinvokerについては、実際の引数が変換後の入力型に適合することと、出力行にraw要求が残ることも検査し、純粋性や無条件の非captureを主張しない。別の境界のglobが外側の負の差分を消せないことも確認する。

## 型推論の主定理

`AnnotationSnapshots.observe` は、現在の行式に含まれる concrete な頭を符号付き行として計算し、残った行変数をこの観測では opaque とする。観測を取る前に、その時点ですでに分かっている置換は適用されている必要がある。`TrackedRow.subst` は行式を具体化し、注釈時点の履歴をそのまま保つ。`principal_observed_exact` は、保存した観測の許容性と既存の宣言的型判断の連言が、観測を付けた主制約schemeの意味と一致することを示す。許容された観測から後の行変数へ上界・等式は追加しない。T3 の例では、未知行を観測してから禁止effectへ具体化した履歴は受理され、その具体化後の行を**新しく**観測すれば拒否される。当初から既知で可視な禁止effectを未知tailの横に置いても拒否される。

`AnnotationFinalization` は有限Horn factの層で、SCCの全memberの制約を集め、実際の `Horn.solve` の最小解を計算した後に観測する。`known_iff_forced` は、その解で真のfactが全モデルで強制されるfactと一致することを示す。`finalize_constraint_order` と `scc_member_order` は制約の生成順序・memberの収集順序に依存しないことを示す。並べ替えても名前解決済みのfact/row識別子は固定する。`principal_finalized_exact` はこの検査を既存の主制約生成へ接続し、`gate_subst` は後の具体化で再検査しないことを示す。同じSCCの別memberから伝わるeffectは検査対象で、入れ子のbindingは自身の単位を先に確定する。この実装は既知の置換を外から渡すだけの層より進んだ有限solverだが、sourceの全制約がその有限interfaceへ翻訳できることまでは証明していない。

`RecursiveInference.generateSCC_exact` は、任意の有限 member 列について、同じ再帰仮定環境で全本体を検査する生成制約と独立な `SCCTyping` を双方向に対応させる。`closeSCC_exact` は slot 群を全本体の外側で存在量化するため、呼出しごとに型を選び直さない。全注釈の `FullAnnotation` は値型の有限変数だけを呼出側で具体化し、定義側ではそれらすべての割当てで本体を検査する。`rowsCaptured` の構文検査により、注釈中の明示的な行slotは外側の共有割当てを参照する。同じ SCC の別 member からも同じ注釈schemeを使う。これらは制約生成の正確性であり、source の SCC 発見や制約の解探索そのものの証明ではない。

`generalizeMember_exact` は、SCC全体を検査した後の一つの値memberの具体化を記述する。存在量化するlocal slotに属する全unannotated memberへ、構文上の値かつpureに型付けされるという検査を入れる。computed memberはcaptured slotに残り、別々の具体化で同じ割当てを参照する。`RecursiveExamples` では、SCC後のidentityをintとstrで独立に使うこと、別memberを公開するときにもcomputed memberをlocal slotへ隠せないこと、全注釈の関数と単相関数が互いに呼び合う例を検証する。

`unannotated_depth_typable` は、`x`を`(x,x)`へ変えて再帰する同じ式を、単相型 `any -> int` で受理する。再帰引数のpairを `any` へ広げることができるため、決定36以前のtopを持たないモデルでの単相拒否は、現在の体系では偽になる。`generated_unannotated_depth_satisfied` と `closed_unannotated_depth_satisfied` は、この実際の割当てを生成制約・closed SCCへ接続する。`generated_annotated_depth_satisfied` の全注釈のschemeによる受理も維持する。source例の算術と条件値はliteralへ抽象化しており、実行の停止性は主張しない。

`QualifiedInference.principal_exact` は、resolved methodの有限のrole要求を制約に加えた生成器と独立な宣言的型判断の一致を、元の構造的な式の全ケースについて証明する。この層の通常の `letE` は単相で、qualifiedな値の一般化は `qualified_let_exact` の別規則で接続する。一般化interfaceはlocal slotと環境slotを明示する。`partition_exact` はraw role要求を自動で分け、local slotを含む要求をschemeへ、環境slotだけの要求を残留制約へ移す。混合した要求の環境slotは量化せず共有する。定義は抽象辞書を仮定して全local割当てで検査し、利用時にその具体化の証拠を要求する。

通常のqualified letは `Comp` slotを量化し、値型とeffect行の両方を独立に具体化できる。operation-localの型変数や全注釈による多相再帰とは量化の種類が異なる。`QualifiedRowExamples.independently_instantiates_latent_row` は一つのschemeを任意の符号付きcallback行で具体化できることを示し、相異なる非空行でも確認する。`QualifiedExamples` は、具体的なimplがなくても未使用の`twice`を定義できること、そのschemeを証拠なしでは使えないこと、実際の`Add int`解決が利用を可能にすること、環境に由来する制約が消えないことを示す。これらは供給された有限interfaceの正確性であり、未解決の部分型制約からそのinterfaceを発見するsolverまで証明したものではない。

`ModuleRoles.finishModule` は、EOFで渡された部分割当てとinterfaceについて、公開型およびraw role要求に現れるすべてのambient slotが確定しているか検査し、残留role要求を実際の `Roles.resolve` で確認する。`finishModule_no_unresolved_exports` と `finalized_scheme_exact` は、受理した公開schemeが元のschemeと同じ意味を持ち、未使用の未確定slotをどう補完しても意味が変わらないことを示す。未確定weak slot、同じファイル内でintに決まる例、証拠のないstr、implなしで公開する抽象qualified関数の各場合を検証する。module全体から全残留制約を収集するpassと、その部分割当てを求めるsolverはこの入口の前段である。

`RoleEvidence.Signature` は既存の `PolySignature` にrole要求を追加する。`request_constraints_exact` は局所型を存在的に具体化して呼出側の証拠を要求し、`handler_constraints_exact` はactionとvalue armの型を先に決めてから、すべての局所型で署名の辞書を加えてoperation armを検査する。外側の環境と結果はその局所型によらず、継続は元のinput rowを保つ。`RoleEvidenceExamples` は実際の符号付き構造モデルで、抽象payloadにAddを使ってからresumeする腕を署名辞書つきで受理する。同じ腕の辞書なしの場合は**すべての外側の結果型・行**で拒否し、呼出側に証拠がないrequestも拒否する。handlerの型判断からoperationalなeffect上界を導く定理ではない。

`principal sΓ e` は一つの結果slotを持つ有限の制約schemeを返す。`principal_exact` は任意の型・行のモデル、対応する入力環境、型と行の割当てについて、次を証明する。

```text
(principal sΓ e).Holds m (extend ρ (A, ε))
  ↔ Typing m Γ e (A, ε)
```

環境の前提 `EnvRel` は、入力schemeと入力bindingが同じ型の候補を表すという条件であり、solverの成功や式自身の型付けを仮定していない。空環境には無条件に成立する。`Typing` と `BindingTyping` は `generate` や `Formula` を参照しない独立の帰納的判断である。

対象の式は変数・基本literal・lambda・computation application・非再帰let・分岐・pairとprojection・recordとfield・variant注入。多相letは純粋な構文的値の有限schemeを保存し、利用ごとにfreshなslotへ代入する。外側の環境のslotは共有したまま。単相letはすべての右辺に使え、一つの型を共有して右辺と本体の実行行を合流する。構文的な値にはこの二つの経路の選言を生成する。`Polymorphism` は、computation引数を指す変数を束縛でき、そのeffectが消えないことを検証する。

`Structural`では、混合分岐が`int | str`を持ち`int`だけにはならないこと、多相identityの二回の利用で`pair(int, str)`が得られること、余分なfieldを持つrecordから`int`を取り出せることを、**生成された制約の意味について**検証する。record spreadのtailには `restType ≤ emptyRecord` を要求し、scalarをtailにする式は任意の結果型・行について拒否する。任意の制約を受理する空虚なモデルではない。

`RowInference.handler_constraints_exact` はcore生成器とhandlerの規則を接続し、同じ定理を非負行と符号付き行に使う。継続には元のactionの行を持たせ、結果にはactionの残余と両armの行を加える。既存の単相署名と定理は維持する。潜在行を含む高階の型変換はこの定理の対象外である。

`EffectInference.PolySignature α n` はambient slot `α` と局所型変数 `Fin n` を分け、署名の入出力を `TyTerm (α ⊕ Fin n)` で表す。局所slotは値型だけを具体化し、行成分は空行とする。`poly_request_constraints_exact` は、呼出側の生成制約が「ある局所型の割当てで独立なrequest規則が成立する」と同値であることを証明する。各呼出しの存在量化は独立し、好きな型を選べる。

両モジュールの `poly_handler_constraints_exact` の型判断は `∃ input returned, … ∧ ∀ ι, ∃ operated, …` の順序である。actionとvalue armの型・行を先に固定し、すべての局所型割当て `ι : Fin n → m.Ty` についてoperation armの型付けと結果への包含を要求する。継続は元のactionの型・行を保持する。結果 `out : CompTerm α` と外側のscheme環境 `SchemeEnv α` は局所slotを含まない。`local_result_no_escape` は局所割当てを変えても結果の型・行が同じであることを、`local_outer_environment` は任意の局所割当てで同じ外側binding環境を表すことを示す。これはescapeを構造的に排除する核の規則であり、source上のescape検出・エラー報告の証明ではない。atomのkey・追加effectは局所割当てによらず固定され、atomのpayload内部の局所変数とrole制約は扱わない。

`SignedStructural.generated_poly_request_at_any_type` は任意の構造型（複合型・effect付き関数型も含む）で呼出制約が成立することを、`generated_poly_requests_independent` は同じ署名・同じ外側の割当てでintとstrへの二回の独立した具体化が成立することを示す。`generated_poly_handler_resumes_payload` は任意の局所型のpayloadを同じ型を受け取る `k` へ渡す腕を受理する。`generated_poly_handler_payload_escape_rejected` はそのpayloadを固定のint結果へ直接返す腕を拒否する。後者は局所型をstrとしたときの `str ≰ int` による具体的反例であり、任意のモデル・任意の結果上界についての拒否を主張しない。

`SignedStructural` は実際の符号付き行を使い、生成されたoperationの制約が自身のeffectを含む行で成立し、空行では成立しないと証明する。保護前の解除が作る `−1` の差分についても、生成された境界制約がその行を保持し、空行へ消せないことを証明する。型構築子・部分型規則・scalarの分離は `StructuralBase` を通して非負モデルと共有し、別の型体系を複製しない。

`DirectedHandlerInference` の `generated_signed_handler_composes_effect_bounds` は、成立した `RowInference.handlerConstraints` から得たaction・armの型付けと、明示された実行時の上界を組み合わせる。結論は実際の `Directed.Computation.shallowHandle` の出力上界である。制約の定理とoperationalな定理を別々に置くだけでなく接続しているが、型付けから実行時上界を得る前提そのものを証明したとは扱わない。

`RecursiveEffects` は全core構文とrequest・boundary・handlerを一つの再帰ASTにまとめる。生成の双方向定理は、型モデルと行代数の空・和・包含を整合させる `RowView` の下で成立する。`RecursiveEffects.Conservativity.generate_preserved` は旧 `Inference.Expr` の全constructorについて、fresh slotや値制限letの両分岐まで含め、生成formulaが旧生成結果の埋込みと等しいことを証明する。`principal_core_exact` は旧 `Inference.Typing` 自体との対応を導く。新しい生成器へ置き換えたことだけを理由に、既存coreの意味を変更しない。

`RecursiveEffectExamples` は入れ子のhandlerとlambda内部のhandlerを検査する。同じkeyをarmで再送出する式、保護された要求、負の解除差分は、任意の結果型・slot割当てでも空行には型付けできない。未使用computation引数を純粋に扱う一方、computed letが実行する右辺のeffectを消せないことも示す。

`OperationalTyping.infer` はshapeが解決し、lambdaの入力型とhandlerの結果型が与えられた単相核のcheckerである。`infer_exact` は実行可能なcheckerと独立な構文的型判断の一致であり、未知の構造型や全言語の主型を求めるsolverの完全性ではない。`typing_sound` はaction・armを含む部分式の型付けに帰納法を適用し、実際のrequest treeの上界と、返された関数を任意の適合するcomputation引数へ適用したときの上界を同時に導く。閉式の `closed_inferred_bound` はchecker受理だけを前提とする。

この評価は関数へ引数をcomputationとして渡す。引数の行を無条件に呼出し結果へ加えず、computed letは右辺を実行する。shallow継続の型には元のaction行を保ち、armが新しく出す要求は残余の外へ加える。`OperationalTypingExamples` は未使用引数、明示的に許可した引数の処理、再開後の未処理要求、同じ継続の二回利用、同じkeyの再送出、pair内のcallback、負の差分についてchecker結果と実際の評価を確認する。即時boundaryが返り値内のcallbackを勝手に変換しないことも検証する。

`OperationalCorrespondence.erase` はこのresolved式からlambda入力注釈・handlerの結果型・明示的なwidenを消し、`RecursiveEffects` の同じ演算へ写す。`erasure_typing_sound` は消去結果の任意の再帰型判断を解釈する。既存の `StructuralBase` のunion・intersection・関数の分散を含み、値制限付き多相letでは純粋な右辺の一つの評価値が各使用箇所の型を満たすことを導く。atomは一つのopaqueなcarrierで、構造型ではunitをそのmarkerにする。source literalの型をunitへ変更する規則ではない。

`principal_operationally_valid` と `principal_effect_bound` は、閉じたresolved式の実際のprincipal formulaの解だけから、返り値の意味と全requestの上界を導く。個々のaction・armのruntime上界もannotated checkerの受理も前提としない。二つの入口は同じ評価に対して健全だが、受理集合の一致は主張しない。注釈の不一致でcheckerが拒否しても、注釈を消した式の制約には解があり得る。source注釈を保持するelaborationの正しさは別の義務である。

`OperationalCorrespondenceExamples` は実際のrequestと、lambda内部のhandlerが許可したcomputation引数を処理するapplicationについてprincipal formulaの解を構成し、同じ評価の行上界へ接続する。requestのformulaには、どの結果値型を選んでも空行の解がないことを示す。この入口の前提が具体的に充足でき、effectを自由に消せる空虚なモデルではないことを確認する。

## 検証ゲート

`lakefile.toml` は全モジュールのコンパイルに `--trust=0` を指定する。`Audit.lean` はYulangの各モジュールからimportされた**すべての宣言**について依存公理を走査し、`propext` / `Quot.sound` / `Classical.choice`以外があれば失敗する。私有宣言も対象とする。その後で主要定理の依存を個別表示する。

`sorry`、追加の公理、`native_decide` での証明を使わない。Lean が通常使う公理と、未証明の主張を公理化することを区別する。GitHubの`Lean inference kernel` workflowも、ビルドとこの監査を実行する。

構文例の計算確認と一般定理も区別する。全言語の推論器、Rust との接続、公開型の表示、実行時の型安全性については、対応する定理を持つまでは完了と呼ばない。
