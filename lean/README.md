Warning: truncated output (original token count: 140556)
Total output lines: 4747

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

共通判断に対する実 `Core.infer`、主型性・拒否完全性・unsupported 不出現は下記の定理で閉じた。
現在は旧 presence 構文に literal・structural data・strictApp・単一 unguarded bind case・leaf を再帰的に統合する。
effects/qualified/一般 case/nominal を含む全断片の相互作用を、この入口で推論する主張ではない。
`cast` は site の構文のみで、統一した挿入/型付け規則は M4 に残す。
literal の静的基底型と presence は同じ Common carrier に接続した。float・nominal の planner 結果は未統合。
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
[全自由 scheme・共有 witness・標準形の統合結果](../notes/handoff/2026-11-07-m1-symbolic-results.md) と
[共通 Core 構文と関数 interface の拡張結果](../notes/handoff/2026-11-07-core-common-coverage-results.md) にまとめる。

2026-11-07 の [A1 完了結果](../notes/handoff/2026-11-07-m1-a1-results.md) で、
`CommonLegacySharedWitnesses.legacy_generated_shared_witnesses` と全旧 supported source の
`legacy_instances_reflected` を証明した。constructor 部分言語の前提はなく、指定された旧結果行を保持する。

復旧記録 §7 の現在の残りは次の通りである。下の歴史的な部品定理の表で「示さないこと」と
記す項目は、その定理単独の範囲であり、後続の統合定理で閉じたものを含む。

| 復旧記録の契約 | 現在の証明 | 残り |
| --- | --- | --- |
| 7.1 symbolic rigid 分解 | source/Core の全実生成 clause、独立 rows/values、同じ共有 ID で exact | この契約は完了 |
| 7.2 有限飽和・全 parameter soundness | optional 境界を含む実 worklist の停止・全 rigid 分解と、返却 scheme の任意行・型 parameter による全 Models | この契約は完了。分岐数・総実行時間の多項式上限は主張しない |
| 7.3 全 instance exactness | 全実生成 clause の任意独立 rows/values を、行の等号と全 compiled node の要求同値で回収 | この契約は完了。任意の手書き atom 列には別途明示した構文条件が必要 |
| 7.4 公開入口・決定46 | 残余のない拡張 `Core.infer` の主型性・拒否 iff / unsupported 不出現、旧 presence 入口の保存、旧 instance ⇒ 新 solved instance。全旧 supported source と任意旧結果で共有旧 witness を構成し、新 instance から同じ行・要求同値な旧 instance を回収 | A1 の契約は完了。任意の新 exact/default target への反映はこの契約の対象外 |
| 7.5 全 public interface 標準形 | 既存有限 constructor/scalar 文法に加え、任意の共通 curried depth・任意 arity・引数の正負共有を持つ variable-domain/scalar-result family の完全 code。実公開 instance と partial EOF も接続 | 一般 domain/constructor 結果、異なる depth、一般行式・弱さ・regular graph・nominal/role 義務をまとめた完全 encoding と全 inference/export/display 接続 |

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
§7.4 のうち、旧 presence モデル（現在の `Core.PresenceOnly.infer`）と、その構文拡張を扱う実 `Core.infer`、
残余のない principal theorem、拒否 iff、unsupported 不出現まで接続した。旧 supported source 全体への決定46の反映は
`CommonLegacySharedWitnesses` で閉じた。§7.5 の完全な public interface 標準形は残る。以下の局所定理と、その後の統合定理を区別する。

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
| `CommonBoundRefWorklist.generated_run_models_exact` / `generated_core_run_models_exact` | 任意の source/Core 式の任意生成 clause、任意独立 rows/values について、元 constructor Realizes の下で、元型比較列の成立 iff 実 run のいずれかの全辺・補助制約が成立。生成 grammar/width を内部で供給 | この部品単独での元明示行制約の求解、任意自…120556 tokens truncated…片。identityはscalar factの伝播規則であり、
seedが無いidentity class全体へ任意型の等式を追加する主張ではない。新しいslotや
変数辺、実parser由来のsource/invocation、一般のchild生成、最終四分類、辞書同値は
未達。B4の5橋は引き続き未完成。一般のordinary entailmentや総runtime上限も含まない。

## Cycle101: 構造的なソースからmixed閉包へ

`CommonRoleStructuralMixedSource` は、検査済みの構造的な有限occurrence列から
source table・receiver/output slot・物理的なsource等式を計算し、関連型とordinary
の交互閉包へ接続する。任意のprogram/stateに対して、実出力のscalar evidenceは、
元stateの明示的なseed、相互辺、独立な構造的関連型導出からなる名前上のjudgmentと
一致する。生成される異なるfactは8 * occurrence数以下。

`run_source_exact` は任意のassignmentについて、実出力を満たす条件が、元stateを
満たし、単一のsource型valuationへ因数分解でき、そのvaluationが全独立導出を
満たすことと同値だと示す。seedの無い同名occurrenceも型を共有する。effectは同一視
しない。`solver_source_exact` はそのモデル存在と実ordinary solverの受理を結ぶ。
rawのscope/arity/関連型名の検査に成功しても、ordinary整合性までは保証しない。

scope解決済みの名前、有限occurrenceの選択、registry、元stateは入力のまま。
ordinaryの一般の意味的帰結を全部検出する主張ではない。ordinary専用変数をこの
occurrence tableの外に持つ場合も未接続。並べ替えでslot自体が変わる場合のreindexing、
実parser、動的child、invocation identity、四分類、辞書同値は未証明。B4の5橋は残る。

## Cycle102: ordinary専用変数も含む計算されたallocation

`CommonRoleAmbientMixedSource` は、構造的occurrenceのtableの後ろに、有限な
ordinary専用のsource名列を加える。receiver/output slotは既存prefixへの埋め込みで
計算し、専用変数に架空のassociated occurrenceを作らない。任意のp/extra/stateに
対して、associated出力とordinary相互辺の交互閉包は、元stateのseed・相互辺と
独立な構造的associated導出からなる名前上のjudgmentに正確に一致する。

`run_source_exact` は、すべての出力モデルが、元stateと単一のsource型valuationへ
正確に対応することを証明する。ordinary専用変数から始まるseed、その変数を中継
する辺、同名のoccurrenceとの共有、seed無しの等式にも同じ主張が成り立つ。
effect成分は同一視しない。`solver_source_exact` はそのモデル存在と実solverを結ぶ。
異なるscalar factは `4 * (2 * p.length + extra.length)` 以下。

extraの有限な名前列と元stateは依然入力であり、実parserからのloweringは未接続。
ordinary一般の意味的帰結の検出、新しいslotを生成するdriver、非scalar Form、
invocation同一性、最終四分類、辞書同値は未達。B4の5橋は残る。


## Cycle103: 名前つきordinary制約からextraと初期stateを計算する

`CommonRoleNamedOrdinaryInputs` は、scope解決済みの名前とscalarの間の有限な
subtype制約列から、ordinary専用の名前列と文法証明つき初期Stateを計算する。
callerはextra・slot map・元stateを渡さない。単方向の上下界、相互辺、scalarの
両向きseedを扱い、associatedの構造的programと実mixed closureに接続する。

`run_source_exact` は、すべての出力モデルを、元の名前つき制約を満たす単一の
source型valuationと、独立なseed・相互辺・associated導出に対応づける。
`solver_source_exact` はそのモデル存在とordinary整合性の同値。effectは共有しない。
`solver_congr` は入力制約の順序・重複が変わりslot配置が変わっても整合性が不変と示す。

これは一般のordinary意味的帰結の検出ではない。int <= a <= c <= intのように
直接seed pairが無い入力では、型が意味的に固定されてもassociated生成を起動しない。
またordinary整合性は全roleの解決成功を意味しない。未解決・unsupported・曖昧な
associated要求が残る場合がある。実parser/式から制約を導くこと、一般Form、動的
child、K2、最終四分類、辞書は未接続。B4の5橋は残る。

Cycle103のextraは同名を重複除去してから割り当てる。元制約は削除しない。
22-slotの整合性検査の時間超過を受け、同じ例を11-slotに減らした。意味保存の
定理の型は変わらない。一般的な性能保証を追加したわけではない。


## Cycle104: checked grouped source and ordinary inequalities

`CommonRoleCheckedMixedSource` connects the existing grouped associated clauses
and named ordinary inequalities at one outer entry. It computes the lossless
role package, structural program, extra names, slot allocation and initial State,
then runs actual mixed closure. `run_true_iff` says, for every finite source and
well-formed registry, that `some true` is equivalent to fragment validity and one
source valuation satisfying all original inequalities and independent scalar
facts. Neither a generated program nor successful checking nor an ordinary State
is supplied as an outer premise. `none` is exactly fragment invalidity;
`some false` is valid syntax without a model of the stated closure fragment.

The original role obligation list is retained by the checker, including clauses
with no associated equations. Ordinary consistency is not role discharge:
unseeded or unsupported roles can remain unresolved when the result is true.
Independent Derives uses direct scalar pairs, reciprocal edges and source
clause equations, not arbitrary ordinary entailment. Whole-clause and ordinary
constraint reorderings/duplications preserve the outer outcome even when
allocation and states change. Reordering equations inside a clause is not part
of this congruence premise. Effect rows are not unified by source type identity.

This closes the checked grouped-clause/named-ordinary connection, not expression
lowering or parser adequacy. Scope-resolved names, finite clauses, ordinary
inequalities and declaration registries remain inputs. Dynamic where children,
general state-changing termination, final four-way classification and canonical
dictionary observations remain open. All five B4 packages remain incomplete.


## Cycle105: retained roles consume computed mixed evidence

`CommonRoleEvidenceDischarge.run_success_iff` closes the finite bridge from the
actual mixed closure to every retained source role. For arbitrary finite checked
source syntax and a declaration-well-formed registry, outer `some (true,true)` is
equivalent to fragment validity, independent ordinary Models, and for every
original clause an independently derived scalar receiver plus declarative
structural role discharge. No caller head map, State, slot map, successful check,
fuel or role-success premise is required. Bare clauses are preserved even when
they introduce no allocated slot.

The two Booleans are separate observations: ordinary consistency and
evidence-backed role discharge. Neither false is assigned a language-visible
classification. Ground templates also require receiver evidence in this finite
adapter; bool/unit evidence is retained ordinarily but the existing int/str
encoder cannot discharge it. Direct pairs and reciprocal edges, not arbitrary
ordinary entailment, drive closure. `run_congr` covers whole-clause and ordinary
constraint membership equivalence, not changes inside a clause's equation list.

Scope-resolved grouped clauses, named ordinary inequalities and registries remain
inputs. Parser/expression lowering, dynamically generated children, general
state-changing saturation, four-way classification and canonical dictionary
observations remain open. All five B4 packages remain incomplete.

## Cycle106: source evidence and recursive diagnostic forests

`CommonRoleRecursiveDiagnostics` constructs the complete unique-head rigid
where tree by Paterson recursion. Independent `Represents` and declaration-index
`Path` retain missing and overlapping children, exact child order/multiplicity,
and arbitrary-depth subtree correspondence, with no fuel or work-table input.
`CommonRoleSourceDiagnosticForest` connects every computed mixed-source scalar
attempt to those trees, retains all source rows (including bare roles), and
proves source-to-child path exactness. Its compatibility projection is exactly
cycle105's separate ordinary/role Boolean observation; it does not introduce a
new final classification. Equal registry references are deduplicated by the
existing candidate identity rule; distinct declaration keys remain distinct.
General source lowering, dynamic fresh allocation, Form saturation, final
four-way classification and source dictionary equivalence remain unfinished.

### Cycle107: source diagnostics carry actual dictionary plans

`CommonRoleDiagnosticDictionaries` structurally projects retained trees to the
existing `RoleDictionaries.Plan`. For every well-formed rigid registry and goal,
the returned payload is exactly the erasure of an indexed Dictionary, preserving
all selected declaration identities and ordered repeated child occurrences.
Arbitrary dictionary paths agree with independent declaration paths.
`CommonRoleSourceDictionaryForest` enriches every existing scalar attempt with an
optional Plan. Literal erasure returns the complete original diagnostic report,
including failures and unsupported encodings. Source-backed payload and path
exactness use independent source derivation, structural materialization and
indexed dictionaries. Root success is explicit for successful-root path lookup.
Ordinary consistency stays separate; plans may be present in a contradictory
source report. No global evidence choice, method execution, final classification
or source-level observational dictionary equivalence is established. All five
general B4 packages remain unfinished.

## Cycle108: visible environments and retained diagnostics

`CommonRoleSourceEnvironmentCongruence` connects equal membership of visible
associated declarations to independent source evidence, Models, both observable
bits, and the full ordered dictionary Plan in every matching returned source row.
The declaration bodies, fixed role signatures, WellFormed and AssocWellFormed
premises are explicit; reordered or repeated identical declarations are covered.
`CommonRoleDiagnosticOrder` preserves complete recursive diagnostics up to a
permutation of overlap heads only. Child positions, goals, failed siblings and
projected dictionaries are preserved at arbitrary finite addresses.
These are finite scalar/rigid fragment theorems, not general state saturation,
K2/final four-way classification, parser adequacy or method observational equality.

`CommonRoleExpressionDictionaryForest` additionally runs the mixed closure and
retained dictionary forest directly from checked annotated literal/variable/let
expressions. Both ordinary bounds are generated internally. Their all-model
meaning is exactly existing expression typing plus the annotation upper bound;
independent expression Derives characterizes every returned full dictionary.
Binding-only names are retained, so contradictory repeated names cannot vanish
merely because no role clause mentions them. Unsupported expressions are outside
this explicitly restricted fragment, not final language rejections.

`CommonRoleStructuralOrdinaryMaterialization` reads paired ordinary bounds for
closed int/pair/union/tick Forms at arbitrary depth. It replaces a variable only
when all recorded structural payloads are syntactically the same, independent
of atom order and duplicates. Every state model preserves the original Form
meaning. Actual generated graph models reflect this meaning and the independent
regenerated frontier. This is deliberately incomplete for semantic entailment:
distinct but equivalent payloads remain unresolved. One-state idempotence is
not saturation termination, and future arbitrary states have no derived finite
source bound here.

Cycle109 adds CommonRoleStructuralMaterializationProgress: inclusive actual
ordinary states change structural materialization at most twice per original
variable occurrence, including loss of uniqueness on equivalent syntax. The
computed additive-state trace needs no caller model or Chain. This is a bound
on diagnostic regeneration events, not termination of the batch-producing
driver or a bound on future structural payload size.

Cycle109 also adds a computed structural child domain, lossless full-diagnostic
replay, and a bridge from actual finite decomposition/transitivity closure.
CommonRoleDerivedStructuralMaterialization detects uniquely represented paired
payloads by the independent seed/split/trans derivation, preserves every model,
and bounds all replay rebuilds and generated-child visits for finite additive
ordinary jobs. No caller supplies propagated atoms, trace, model or child list.
The batch stream and source slot/invocation maps remain inputs. Checked State
upper terms remain in the existing grammar; raw join/tick materialization is
not promoted to a complete checked ordinary solver or the full B4 theorem.

CommonRoleStructuralSaturationTrace removes the external batch stream for the
existing finite ordinary seed/split/trans rules. It instruments firstFresh in
actual discovery order, derives the carrier/capacity from original atoms,
checks the original State with the real ordinary solver, and preserves every
original model at every generated snapshot. The final atom membership is
exactly independent Derives, terminal closure is proved, and all diagnostic
snapshots and fresh ordinary graphs use the generated trace. This completes
that finite ordinary driver, not general mixed role-to-ordinary saturation.

CommonRoleStructuralHornClosure and CommonRoleStructuralAssociatedClosure compute
one finite carrier for mutually alternating structural ordinary and actual
associated-declaration equations. The carrier and causal fresh-atom trace are
internal. Exactness uses independent seed/split/trans/associated derivations;
all-model semantics states the additional activated equations explicitly.
Finite source occurrences/templates and scalar associated decoding remain
fragment restrictions, not language rejection rules or full B4 completion.

CommonRoleStructuralAssociatedSolver reconstructs a grammar-checked State from
the initial state and all scalar equalities actually proved by the mixed closure.
Its models are exactly the full structural closure models; the real ordinary
solver therefore rejects exactly inconsistency of that closure.
CommonRoleStructuralAssociatedReplay drives every generated cumulative snapshot,
bounds tree rebuilds and all recursive child visits, and regenerates ordinary
graphs even on unchanged-tree plateaus. Associated updates can narrow models;
only final models are guaranteed to satisfy every earlier snapshot.

CommonRoleStructuralHornSchedules gives independent causal small steps and
fresh executions for arbitrary ordinary/associated firing orders. Every legal
execution fits the computed syntax carrier, and every maximal execution has
exactly independent Derives, the actual solver model set, and the same structural
materialization. The real generated trace is proved to be such a maximal
execution. This does not identify dictionary lists or arbitrary language schedules.

CommonRoleStructuralNamedInputs computes compact slots from every source atom
constructor (including nested arrow rows) and finite structural source templates.
Its Boolean checker is equivalent to the existing checked State grammar.
Present names have injective slots and never use the one unused internal slot.
The public run constructs the State, mixed closure and ordinary consistency
check, with exact original-name/all-model provenance. Parser/scope adequacy and
dynamic occurrence selection remain open; grammar failure is not a new language
rejection rule and ordinary success is not complete source-role discharge.

- Cycle111: `CommonRoleStructuralRenaming` and `CommonRoleNamedStructuralDerivations` prove allocation/readback exactness for independently derivable original-name structural atoms and actual ordinary-solver success iff a named model exists. Static checked single-placeholder/scalar fragment only; general B4 remains open.

- `CommonRoleRawStructuralSource` removes externally checked templates: executable scope checking and ordinary grammar precede allocation and actual solver execution. Independent raw-name derivations and all-model contracts retain occurrence order and repeated endpoints. Unsupported scope is adapter failure, not a language rejection decision.

## Cycle112: B4 skeleton / lossless root / scalar dictionary

`B4Skeleton` preserves the existing five-clause target and proves composition
from 12 smaller explicit obligations. No full-source bridge instance is supplied.
`CommonRoleSettledRootClassification` retains unsuccessful children in their own
positions and characterizes root rejection by the three local reasons.
`CommonRoleScalarDictionaryModels` runs ordinary consistency, materialization,
and the real singleton int/str dictionary elaborator, with evidence in every
ordinary model. General B4 and where-order dictionary equivalence remain open.

`CommonRoleSettledVisibleOrder` proves equality of the full diagnostic trees
under permutations of visible declarations, preserving selected declaration
identity, every child, and incomplete results. It does not permute where lists.

## Cycle118: ordinary-state scalar registries

`CommonRoleScalarRegistry` takes arbitrary finite visible int/str leaf declarations
and an arbitrary ordinary state. Independent source-membership candidates and
paired-atom knownness give all four adapter outcomes exactly, including the
actual selected dictionary. Successful dictionaries are sound for every input
Common model. Visible-set equality preserves exact outcomes and dictionary
payloads, covering permutation and duplicate enumeration. Unsupported scalar
materialization remains adapter pending; inconsistent states are unavailable.
Where children, general K2, associated equations, and general B4 are not claimed.

`CommonRoleScalarExpressionRegistry` removes the caller-supplied ordinary state
and receiver slot for closed literal/variable/let expressions with explicit
int/str annotations. Its source entry computes validation and paired bounds,
then the real solver and dictionary elaborator. Exact classification is stated
using independent original-expression evaluation and declaration-origin matching.
Every returned dictionary is sound for every declarative expression model
satisfying the annotation. Unsupported syntax remains an adapter boundary.

`CommonRoleSaturatedScalarRegistry` classifies an original source name after the
existing named ordinary/associated closure computes its shared state. Allocation,
root lookup, consistency and materialization are internal. Exactness uses original
named derivations; every selected leaf dictionary holds in all original source
models. Visible-set changes and ordinary-input reorder/duplication preserve the
literal outcome and dictionary despite changed allocation. Existing associated
environment checks remain inputs; general materialization and B4 remain open.

`CommonRoleScalarTargetObstruction` supplies a real model-inhabited empty source
registry/state witness for the old B4 target's pending/rejected overlap. The
actual scalar adapter returns pending. No executor satisfying genuine state
reachability can satisfy that old target on this explicit leaf adapter. This
refutes the old formal instantiation, not intended language B4. The knownness
guard and lossless-tree alignment need supervisor review; existing targets and
language rules are unchanged.

The saturated scalar adapter keeps its final visible scalar entries separate
from the associated-declaration environment. Their agreement as one language
source registry and parser/module visibility are still unconnected boundaries.

## Cycle119: revised B4 target (I-17)

`B4TargetV2` keeps the original unrestricted input/model quantifiers and five
clauses, while guarding all root rejection reasons by knownness and returning
lossless diagnostic trees. `B4TargetV2Functionality` proves independent local,
tree and completed-classification uniqueness without an executor hypothesis.
`B4SkeletonV2` assembles twelve local bridges into the revised target; the
general source instance still has 12/12 unfilled fields. `B4TargetV2Regressions`
checks the original scalar pending/empty case and preserves a rejected child
without classifying its parent. The old target and old bridge package remain.

### I-18 item 5: source dictionaries and general registry order (cycles121–122)

`GeneralSourceDictionaries` retains each actual multiargument demand and source
identity in finite dictionaries. Its structural comparison preserves identities,
keys, multiplicities and state linkage; its `Evidence` still has an explicit
unimplemented local-instance parameter and is not the general B4 Evidence field.
`GeneralSourceDictionaryEquations` gives exact ordinary-atom meaning for every
instantiated head and repeated associated output at any common assignment.
`GeneralRegistryReordering` permits only visible/where enumeration changes and
proves that all independent declaration checks survive. General capture,
instantiation, candidate semantics, and the dictionary-to-B4 adapter remain open.

`GeneralRegistryChildOrder` proves reorder equivalence and preservation of whole
child emissions. Its raw-order obstruction is addressed locally by
`GeneralCanonicalChildOrder`: sort existing unique clause IDs, preserve Checked,
and obtain literal equality of complete canonical emissions under reordering.
`GeneralDictionaryStateEquations` derives all-model head/output meaning from
actual stored local inequalities, using separate type and row source maps.
`GeneralDictionaryEquationExamples` supplies a satisfying model, repeated-output
and source-ID regressions. These components do not fill the general B4 boundary.

## Cycle123: inspection-pending target

B4TargetV3 and B4SkeletonV3 retain the lossless diagnostic target and its twelve
open general-source bridges. Inspection pending is below K2 and above empty
rejection. Local/Classify are functional on arbitrary boundaries. Local totality
requires explicit deterministic surviving children; a stable countermodel proves
excluded middle alone is insufficient. No general B4 completion is claimed.

GeneralDictionaryReadback proves exact key-payload/indexed-evidence correspondence
and unique readback under explicitly deterministic ordered source children.
GeneralDictionaryModelEvidence lifts actual stored ordinary inequalities through
the whole dictionary in every shared-state model, with one uniform source witness.
The declaration-to-equation package relation is still unimplemented; equation
evidence alone is not complete role Evidence. Regressions use a satisfying model
and two distinct child source IDs with identical erased leaf payloads.

GeneralDictionaryPayloadOrder gives the actual key-only payload its least
structural sibling-permutation equivalence, preserving keys and subtrees.
GeneralDictionarySemanticOrder transports the full source child list alongside
payload order and proves shared-model equation evidence for every permutation.
Canonical ordered evidence and unordered conjunction evidence are distinct;
a regression proves the unordered relation is not literally child-functional.

GeneralDictionarySemanticUniqueness proves source dictionary uniqueness modulo
sibling order under explicit local selected-key/child uniqueness. The actual
checked-registry EmissionPlans discharge same-key child determinism at a fixed
capture/allocation frame. GeneralDictionaryPlanLookup is an executable exact
lookup of those independent plans and is invariant under registry/where order.
Plan is not Survivor: matching, feasibility, frame construction, freshness and
declaration-to-equation semantics remain unproved general-source obligations.

GeneralDictionaryPlannedEvidence couples actual executable declaration-plan
lookup to stored all-model equation evidence. Same-key child determinism is
derived from checked IDs and the fixed frame; the declaration-to-term relation
remains explicit and unimplemented, and is not substituted with role satisfaction.

## Cycle124: dictionary equation recording and RHS provenance

GeneralDictionaryEquationRecording implements exact source-preserving ordinary
recording, automatic Recorded membership, joint feasibility and conservative
model preservation when already entailed. GeneralDictionaryAssociatedProvenance
retains explicit Pattern bodies separately from positional Roles.Term defaults,
with exact lookup, declared coverage and complete output-source preservation.
Neither module supplies full role Evidence, candidate applicability or the
missing nominal/center-free interval term interpretation. General B4 remains
12 unfilled bridges out of12.

GeneralDictionaryBatchRecording and GeneralDictionaryTransactions now compute
one finite ordinary transaction for every annotated dictionary node, construct
Recorded automatically, and prove exact joint feasibility and one uniform
source witness in every final model. Frames vary by complete root occurrence;
separate calls need not share captures just because their implementation key
is equal. The family remains supplied and has no proved revisit coherence.
GeneralDictionaryPlannedOutputs couples canonical children and every explicit/
default root RHS to the same actual checked visible declaration.

- Cycle125: `GeneralDictionaryOutputBinderTerms` computes actual explicit output-only RHS variables, proves lookup/independent-denotation equivalence, and connects every recorded root output to its checked producer child source. Default/input/compound bodies remain deferred; all12 general B4 bridges remain unfilled.

- Cycle125 follow-through: `GeneralDictionaryBinderLocations` finds source IDs in the actual injective state map and computes every local output term. `build` accepts only head/endpoints/targets, defers the whole package if any output fails, and proves actual RHS provenance after recording. Concrete checked-source and shifted-slot examples retain repeated targets and exhibit a satisfying model.

## Cycle126: computed checked output plans

`GeneralDictionaryComputedOutputPlans` joins key/role-checked visibility, canonical child emission and actual output-binder localization through one declaration lookup. Its head-only remaining predicate cannot supply output meaning. Unsupported output interpretation defers the whole package; source frames, head elaboration and candidate selection remain explicit.

`GeneralDictionaryComputedTransactions` builds Transactions.Valid from per-node lookup success and complete child roots. Its source witness is uniform across all models of one batch; output provenance is tied to the same visible declaration as the child plan. `GeneralDictionaryComputedOutputExamples` checks actual visibility, key/role mismatch, repeated target preservation and nonidentity source maps. This does not supply the missing terminal output interpretation or complete role semantics.

`GeneralDictionaryBinderOnlyBoundary.built_root_outputs_empty` proves that the binder-only interpreter cannot complete a finite output-bearing tree: every output requires a real canonical producer child with an output, so finite induction forces all roots output-free. This is an implementation boundary, not language rejection. The earlier conditional transaction statement is not an end-to-end output-bearing completion result.

The additive `GeneralDictionaryVariableTerms` accepts explicit input-variable RHSs only at literally identical captured endpoint IDs; it selects no interval midpoint. `GeneralDictionaryVariableCompatibility` proves old successful packages unchanged. `GeneralDictionaryVariablePlans` and `GeneralDictionaryVariableTransactions` use that concrete interpretation under the same checked key/role/child plan. `GeneralDictionaryVariableMaterialization` proves build iff independent input-field equality and actual RHS denotation at every located output. `GeneralDictionaryVariableOrder` proves exact package equality under visible/where reordering at fixed state/frame/inputs. `GeneralDictionaryVariableExamples` retains unequal-interval/default/compound deferral and nonidentity source regressions.

`GeneralDictionaryTerminalFixture` supplies a checked terminal input-alias declaration and a two-level computed tree with repeated root outputs. Its ordinary transaction has a concrete common model, and all models equate each root target with the producer and singleton input source. Full dictionary evidence still explicitly assumes both declaration-head interpretations; the supplied root head is not derived from its nominal declaration head.

`GeneralDictionaryVariablePreparation` takes a finite recipe with no output vectors, computes every package, and checks complete child occurrences. Success plus a head-only recursive certificate produces a uniform all-model source witness. It does not discover candidate keys, solve heads, allocate identities, or saturate a state. `GeneralDictionaryPreparationExamples` runs the real two-node tree and rejects partial materialization with missing/extra/wrong-identity children, missing keys or unequal terminal input captures. `GeneralDictionaryVariableRealization` proves computed RHS meaning for every compatible interval/output capture realization; deriving that realization from matching is still separate.

`GeneralDictionaryVariableHeads` computes the head vector from actual positional variable patterns and exact captured source IDs, starting from HeadlessInputs. Its exactness and every-realization meaning hold only for this explicit supported relation; nominal/compound heads defer. `GeneralDictionaryHeadExamples` proves terminal variable-head success and nominal/unequal/absent-source deferral. It is not wired into a headless whole-tree recipe yet. No source materializer here selects candidates or bypasses the approved requirement to wait for every unnamed argument's lower head.

### Cycle127: complete recipes with actual variable heads

`GeneralDictionaryHeadlessPlans` computes both positional heads and associated
RHS terms from the same checked visible declaration. `GeneralDictionaryHeadlessPreparation`
uses a recipe with endpoint/target positions, chosen keys and children, but no
head or output terms and no external recursive head proof. Successful preparation
constructs a fixed source dictionary witness valid in every model of the one
recorded batch. `GeneralDictionaryHeadlessExactness` proves an iff with an
independent recursive materialization judgment. `GeneralDictionaryHeadlessOrder`
preserves the whole prepared result, dictionary and recorded state under allowed
visible/where reorderings at fixed source inputs, including failures.

`GeneralDictionaryHeadlessFixture` and `GeneralDictionaryHeadlessExamples` give
a checked binary variable-headed producer and unary terminal leaf, nonidentity
source localization and repeated output targets. A concrete joint model prevents
vacuity. Missing/extra/wrong-identity child recipes and unsupported captured
heads defer. No candidate resolution, capture discovery, known-head guard,
nominal/compound/default semantics, saturation or general B4 completion is claimed.

`GeneralDictionaryHeadlessRealization` constructs compatible binder values from
supported checked heads for every source assignment. `GeneralDictionaryHeadlessSourceEvidence`
then supplies an independent actual variable-declaration Instance, without local
term packages or arbitrary meaning predicates. The fixed dictionary is valid in
all joint models; the binder values may vary with each assignment.
`GeneralDictionaryHeadlessSemanticOrder` transports arbitrary source Evidence
under visible/where reordering, including evidence not produced by this compiler.
`GeneralDictionaryHeadlessSourceExamples` demonstrates the exact limit: compatible
unequal endpoint identities can satisfy Instance while the partial compiler defers.
`GeneralDictionaryHeadlessCandidateBoundary` records that the freshly integrated
partial candidate range still requires empty root outputs, so it does not yet
certify the already materialized output-bearing dictionary fixture.

`GeneralDictionaryHeadlessLocations` computes all demand endpoint and output-target
slots, with exact source-membership coverage and completeness from Linked.
`GeneralDictionarySourceRecipe` therefore needs only occurrences, selected keys
and finite child shape; source positions and all term vectors are computed.
Its all-model source-evidence theorem leaves frames/captures/allocation and
chosen keys explicit. Missing source identities defer instead of allocating.

Cycle128 adds exact reconstruction of complete source obligation trees from raw
selected-key dictionaries. The checked registry computes every descendant
occurrence; missing and extra children defer. Localization and preparation
preserve the complete source tree, connecting the original raw payload to one
fixed actual-source witness in every model of the recorded batch. Fixed-input
registry reordering preserves the full optional result. Captures, allocation,
root and selected-key payload remain inputs; readiness and general B4 are open.

Cycle128's dictionary equations and independent declaration Instance also use
arbitrary full nominal assignments. A real nominal73 fixture supplies one joint
model. The dictionary-only full-state transaction retains descriptors, source
ownership and all old model obligations, while recording every head/RHS equation.
The compiler's pattern range is still variables; nominal values in captured
sources do not constitute general nominal head/RHS materialization.

The nominal-candidate dictionary adapter computes Frames from the actual checked
registry and existing inspection reports. Given per-node Survivor evidence at
one fixed Context, it reconstructs the unique complete source witness of a raw
payload. It does not construct that recursive evidence or propagate child states.

Cycle129 item5 adds computed nominal frame/reconstruction/preparation order invariance at fixed Context and an exact syntactic slot-transport certificate for full nominal Models. The target snapshot and distinct type/row maps remain supplied; no allocator, general Step, full materialization or general B4 completion is claimed.

Cycle129 second checkpoint composes exact slot reindexing through whole finite raw preparation and dictionary recording. The complete source dictionary and full nominal model set are retained; target snapshots and global frames are supplied, success only is monotone. Strict growth, mixed type/row nominal descriptors, repeated outputs/batches and nominal-source registry order have separate regressions.

Cycle129 final: five further modules join exact raw preparation through a strict
mixed nominal extension, conditionally preserve Fresh with CoordinatesBound,
and exhibit a nonvacuous normalized-view/readiness boundary. An actual newly
represented reserved ID88 changes raw preparation from none to a complete tree
with repeated output obligations and full nominal evidence, while remaining
RootPending. Eighteen modules and the final public theorem count are inventoried
in `notes/handoff/dots-cycle-129-theorems.md`. General B4 V3 remains 12/12 unfilled;
no source allocator, candidate Survivor or driver-order equivalence is claimed.

## Cycle130: recursive candidate dictionary adapters

`GeneralDictionaryRecursiveReadback` derives source frames from the recursive
inspection report, including repeated capture merges, and reconstructs the exact
full source tree from raw payloads. Candidate derivability remains an input.
`GeneralDictionaryRecursivePreparation` retains that tree through the existing
partial supported-variable compiler and proves its declaration evidence in all
models of the explicitly recorded transaction state. This is not validity in
all models of the original state and does not fill V3 evidenceNode.

`GeneralDictionaryRecursiveEvidence` defines a model-indexed source-instance
certificate with actual declaration, full child emission, recursive branch
equations and readiness guards, independent of candidate selection or execution.
It is inspection-mediated and retains partial translation coverage. The generic
`GeneralDictionaryRecursiveObstruction.no_evidenceNode_of_output_sound` shows
that the current V3 all-state node field is false for any evidence respecting
the fixture's explicit associated output. Completing Step alone does not fix
that field's missing final-state scope. General B4 remains unproved, 12/12 fields
unfilled. `GeneralDictionaryRecursiveEvidenceReadback` reconstructs one exact
source tree independent of which supplied model validates that same payload.

The final source-instance certificate retains constructor Metadata coherence.
`GeneralDictionaryRecursiveEvidenceFacts` exposes exact branch constraints and
proves observed values fit repeated nonpoint captures and their variable children.
`GeneralDictionaryRecursiveObstructionEvidence` gives the concrete source
Evidence counterexample and an exact output-equation criterion.
`GeneralDictionaryRecursiveRecordingExamples` records that declared equality as
two ordinary subtype atoms: the refined full models are nonempty, strictly
contained in the original models, and exactly the models of the fixed leaf's
source Evidence. This does not implement Step or change selection semantics.
`GeneralDictionaryRecursiveOrder` and `GeneralDictionaryRecursiveSemanticOrder`
prove fixed-context computed-frame, reconstruction, preparation, branch and
independent semantic Evidence invariance under checked visible/where reordering.
The same source witness and the same full assignment are retained.

- Cycle220 target checkpoint: V8 sharing-conflict diagnostic and generic bridge skeleton. This is not an unconditional EvidenceNode proof.

- Cycle220 concrete checkpoint: actual repeated-variable head equations, conflict rejection, same operational Step, twelve operational laws, and the full Statement conditional only on the unchanged EvidenceNode. GroundCopy218 is rejected; prior default/join evidence and selection are retained. EvidenceNode remains OPEN.

- Cycle220 follow-up: SafeKnown gates sharing rejection; pending and ambiguity are exactly preserved from V7. Reachable non-repeated head captures preserve selection. Separated aggregate support (in particular singleton captures) proves a genuine common-head amalgamation fragment, not general EvidenceNode.

- Cycle220 tight raw support: private propagation depends on old semantic sources and the current declaration capture endpoints, not unused reserved registry keys. This is a single-transition support lemma, not historical freshness.

- Cycle321 (I-56 declarative dictionary soundness): observable support is
  separate from ordinary truth and structural recurrence. Source constructor
  walks, normalized visible fields, shared actual-name occurrences, invariant
  nominal endpoint readback, and compiled ordered where/output rows give
  same-model evidence for a source-rule fragment. Ordinary fresh where names
  extend each old model without changing its old names. Approved whole-source
  local normalization/propagation and existing-state provenance remain open;
  no solver, executable or termination result is asserted.
