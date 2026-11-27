# dots-main cycle 467: 実 compiler の準備、既発行 address の転送、相の境界 (G04)

道具: モデル不明、Lean 4.35.0; 委譲: モデル不明、1回、task /root/yulang302_resume（追加委譲なし、Codex thread なし）

- 開始 2026-11-27T14:33:47.102Z、通常終了 2026-11-27T15:23:50.552Z UTC（実経過 50 分台）。前回 C466 は監督統合 b59bd47e0f229f7e1013b35a67b95365abfe9dfb で採用済み（Lean 85f87b20954706e7ea3bcad282c81eab300d51b3）。終了時の監督参照 b59bd47e0f229f7e1013b35a67b95365abfe9dfb、I-89/I-90 ACTIVE、STOP なし。
- **G04 は未完、24 行中 20 行残り。** C467 science 66673c863877840af6ca98d8cca8a766f6336f74、Lean tree caebfa827aa0c0ab1e84fc87818b2a7353ecfb6b。旧 compiler の真正な ordinary capture から次の実 C360 準備までを有限に接続し、別の実 C361 経路では既発行の完全な address を受信相で読める。未発行の inline/bound 点の真正な I65 native issuer を新規生成する producer は未接続。言語の可否、raw graph、累積 checker の Bool は変えない。

## I-89 の三条件に対する結果

1. **独立判断と保存・反映（部分）**。検査済み外部 GD・実単一可視 original head について、有限な既存 source 走査で漏れない declaration ordinal と FrameKey、C332 実 capture table/元 binder/ordinary 行を得る。C360 の独立した Prepared（実 pre/where 行・保持）を本物の prepare と相互照合。既存の別経路 C361 は実 Direct/Port/Received の独立 receipt を actual reader に戻す。この二つを同じ発行とみなさない。
2. **finite data-only（部分）**。readUsingOldCaptureTable が同じ旧 capture の実 spans を本物の C360 prepare に渡す。keep/fallback/targets は既存の別入力。checkForwardedInActualReceiver は C361 実 compiler world と別途与えた同一 ordinary/既存 ledger/元 grant を照合する。どちらの読取も新しい issuer/OriginRoute は書かない。明示 name map の普通の相の比較も、元の箇所で保持すべき観測ごとに既存 Bound349 data を有限再現する。
3. **同じ State の正確さ・健全性・具体化（部分）**。実 C361 old parent の完全な Write・既存 route を exact receiver world 中で読み、全同じ Fit で nativeSyntax と実記録 code の解釈が得られる。既発行だけの条件付き定理であり、未発行の G04 の元 inline/bound 座標を具体化しない。G04 point head、通常の native prepare、associated-output installer、old grant の transport は別々。

## 主な追加定理

| モジュール（GeneralDeclarativeI65I74…467） | 範囲・結果 |
| --- | --- |
| PreparationAddress / InstallPhaseIdentity | compile_none_at_unrequested_ordinal、prepared_without_outputs_cannot_produce_native_value: 任意の実 Prepared/output wire/version、元 request にその ordinal が無ければ none。compilation_returns_exact_requested_associated_output_address、exact_compiled_address_at_prepared_source_and_model: 成功時だけ実元出現・宣言・source id・要求 output/固定先/owner/typed route を保存する。exact_installed_origin_checks_the_actual_returned_ordinary、every_data_wire_declines_a_different_actual_compiler_phase、real_release_of_current_board_uses_no_fresh_scope_in_a_true_fit: C465 は実 install の ordinary を直接比較するので、違う相は全 wire false。正例の全同じ Fit の旧 code/nativeSyntax を読む。 |
| ActualHeadFrame / PreparedExecution / CapturePreparation | a_single_visible_compiler_head_has_exactly_its_own_unfiltered_source_index: 実 singleton head の filtered index と unfiltered ordinal を同定。native_preparation_replays_exact_independent_record: 実 Prepared の有限再生。actual_preparation_wire_iff_old_source_and_native_compiler_record、using_old_capture_table_has_only_the_exact_bound_layout、using_old_capture_table_replays_any_exact_independent_output: 実入力捕捉と実 port prepare、旧 spans と exact raw ordinal を保存・反映。発行や solver 合成は主張しない。 |
| ExistingForwardedAddress / ExactForwardingReplay / ReceivedPhaseReplay | receiving_compiler_body_keeps_the_exact_parent_address_and_output、existing_forwarded_address_same_state_semantics: C361 の actual child/receiver は既存 board と既存 Write を保持し別件を発行しない。independent_direct_source_position_replays、independent_exact_forwarded_port_replays、independent_exact_receiver_execution_replays: 元 source/operand number・release・子の実該当 compiler を有限再生。one_existing_forwarded_receiver_iff_finite_data、same_fitting_receiver_reads_old_physical_code_not_fresh_assignment: 同じ author environment、実返戻相、既存元 ordinal/route の独立条件との iff・全同じ Fit の健全性。 |
| PreparationFootprint / PreparationTagScope / CheckedPreparedRetraction / CheckedPreparationObservations / PreparationBoundReplay / PreparedBoundRetraction | raw_cycles_at_original_footprint_depend_only_on_restricted_alias、ordinary_retraction_of_collapsing_appended_atoms: 与えた元 shape owner/payload/root と実旧 ordinary generator を保つ場合だけ exact raw K2 同値。original_lower_constructor_knowledge_preserved_at_all_pinned_names: 固定すべき tag owner は graph footprint より広い。exact_finite_preparation_retraction_check、finite_literal_bound_wire_is_equivalent_to_independent_bound、projected_preparation_has_finite_wire_exactly_for_independent_old_bounds、checked_projected_preparation_preserves_original_raw_k2_and_tags: 同じ実 rows・interval、元名を保つ実 append と旧 Bound の有限再生なら、固定された元位置の raw K2/Knows を両向きに保存する。全相の同一性・全名の K2・新 native authority ではない。 |

## 実対照

- 原占有 [71,2]／宣言 218／全 source ordinal 0 の C466 正例（実 FitsFull）をそのまま使い、target 7/raw 3 と実 spans から C360 prepare が成功する。生成 ordinary equations は一致し、8/9 が 7 と相互 subtype という二つの関係が実新相の条件。全旧 ordinary model は新しい二点だけを調整して延長できるが、変えないと実反例がある。raw Alias(8,7),(9,7) と slot8 の Knows は増え、この実例で raw K2 は両相とも 5 のみ。出力のない実 original request ではあらゆる C360 native emission wire/version が none。欠落 GD・誤 job/arg も exact 別対照。
- 真正な C360 install/release 正例に反射律等式 999=999 だけを足すと全 ordinary Models が同じで同じ core Fit もあるが exact snapshot は違う。旧 C369 authorization は保持された既存 native row/route に成立し、同じ板を別途供給した C465 phase-origin read も成立する。**実 install を再演する C465 強検査**は全 wire 不成立。古い定理の結論を異なる「実相が同じ」に置き換えない。
- 真正な C361 receiver の span (116,101,117) で既存 Write は 101 だけ、116/117 に実 native write・元 route は無い。actual receiver 合格、旧 ordinary と同じ ordinary かの誤判定、反射律行追加、issuer/元 ordinal/grant/宣言番号/operand の誤りは別々に不合格。実モデルが存在する。この例は受信後の既発行 associated output で、G04 の未発行 point の発行例ではない。
- その実 receiver transition は元 101/112 で exact retraction に合格する。116→112 と 117→113 を投影しても新辺の一部は異なる元端点になり、旧 112→101,101→113 の正しい物理 atom ordinal を読んだときだけ合格。誤/wire 欠落/移した root116 や syntactic collapse のみは不合格。これで原観測を保っても旧 exact phase での native read は不合格。別の inline variant 最小例では raw graph footprint のみの K2 保存から Knows 保存は従わない。

## 次・Yulang2・検証

- 次: (1) 実 compiler の inline/bound child 発行イベントが持つ元 head の実位置、型付き物理座標、issuer と release stamp を同じ production phase に結ぶ、(2) 既存 C360 associated-output id/target や C361 forward の証明を流用するなら、発行イベントと旧 raw の番号・同相入力を明示して混同しない。今周は新規言語の決定・質問ノート・graph write・canonical branch なし。G05/G10、G08、G06/G07、G20/G21、GD は別。一般完全性・主型性は未証明。
- Yulang2: spec §4/6.2/6.3（roles 2732b1d…）、既存 C331/C332/C360/C361 原典、および work/dots-audit@55574b60… の x-oracle X8–X11 を照合。X10/X11 は実機で再帰 record head の正しい K2 に到達した証拠ではなく、新 native head issuer も未観測。新規 Yulang2 実機は実行していない。
- immutable Git bytes を Lean 4.35.0 `lean --trust=0 -DwarningAsError=true` で、production 14（`-o`）、独立 standalone Audit 20、末尾 14 import の focused replay（監査者と worker の焦点テスト）。穴・新公理・native_decide なし。公理照合 73 件（標準集合の部分集合 68、公理なし 5）。明示 guarded #eval 5 群、別に kernel decide +kernel。全 Lake/Rust/tools/verify-lean.sh は未実行。
- 新規 Lean 34、aggregate 末尾 14 import、設計2、心拍、報告の **39 paths**。旧 production 7,917 と Audit 2,369、spec/tool/config 不変。expected-parent 非 force の work/dots-main のみ。+10/+20/+30/+40 と通常 +50。復旧なし、使用量枠不明、終了前空き 525M。
