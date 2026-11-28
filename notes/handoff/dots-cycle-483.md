# C483: 元の中間位置ごとに、著者根拠と型商の経路を分けて検証

## 今回の範囲と結果

- C481 の平坦な入口と互換証明は開幕時点で統合済み。+10 に C482 の既存 Lean tree も正確に採用されたことを確認した。今回の既存定義変更・削除は 0。I-97 の削除例外は開いておらず、G05 以降や現行 `check_full_flat` の追加タグには進んでいない。
- `paired_actual_constructors_pull_the_exact_selected_slot_to_the_same_ordinal` と `every_paired_actual_position_keeps_its_own_return_status`: 同じ元 State・位置表の二点が正規型として等しく、実 constructor の両 Hop が同じ Slot を選ぶなら、実 graph の子の番号は一致し、任意の有限対経路の各対で型商の自点回帰が一致する。物理 site の同一、元構文の選択、著者権限までは導かない。
- `checked_interior_compares_a_literal_child_without_transferring_source_authority`: 既存の named 位置に対し、先行の著者 Read カードの実 raw row と、異なる物理表示を使う旧 geometry を別々に検査し、安全な同型の親から同じ **一つの StepWire** で続ける。著者側の選択ごとの元の全 FitsFull 下での独立な型付き Walk を保ち、元 Pose・compiled child・両旧座標を固定する。型の等しさは K2 bit の照合にしか使わず、pending 側を著者証拠にしない。
- `readRootedInterior` と `checkScopedInterior483`: C482 の実 prechecked head・正確な最初の authored/raw ordinal・全実引数の root safety から、既存の named field を通って有限の対付き suffix を読み、両方の proper prefix の安全、終端の exact Site と同じ K2 bit を確認する。過去の `readRoute` と**同じ元の report** を返す。requested report は occurrence、宣言／引数 ordinal、original Pose、compiled path、物理位置、符号をすべて照合する。`rooted_report_fields_point_to_real_original_declaration_and_ast` が元 declaration と元の atSource を反映する。有限再生は各 selected hop の個別検証と既存の signed geometry を前提とし、任意の raw から著者表を復元する定理ではない。
- 実例: 出力なしの元 Fit をもつ raw1 の著者側と raw2 の pending-only 側で再帰部分の展開が異なる。rooted 版は実 path field30→field40→field50、元 Pose [payload,payload,payload]、raw2 の既存 path [field40,field50]、K2 true を返す。実際の著者側の対応座標は raw1。間違った著者座標、元 Pose、全引数ガード、初期 author ordinal は失敗する。短い中間一辺の exact tuple は Lean kernel でも確認、二辺の full report は guarded 実行、同じ元 Fit と pending 非著者は kernel で証明した。別の実例では二つの元 field と別々の子 binder が同じ raw child に到達するが、Pose の取り違えは通らない。raw target だけから両方の元 Pose を復元できない。
- **G04 は未閉鎖、24 行中残り 20。** C480 の qualified event-wise `G04Producer` は証明済みで、runtime compiler をここで要求し直していない。残りは、局所 route が受ける prior authority を現行の入口について独立に結び、I-93 の signed report を exact 分類・全 FitsFull 健全性・witness の保存反映ごと flat の新枝として接続すること。現行 `FullProblem` は State と Request で、局所検証が別引数で受ける `PriorPhase` の著者表・完了 association・保存順の正確な根拠をそれだけからは取り出さない。また今回の rooted adaptor は prechecked named-field 到達後の同じ選び方の対経路であり、どの source でも同じ witness を作れるとは示していない。

## 引継ぎ・仕様と実機

次は (1) 独立に型付けした source event と正確な元 route の照合、(2) その event の選ばれた各中間点の別々の著者根拠、(3) 要求の全実引数の独立な完全閉コーン、と分けて再現できる範囲を詰める。内部の検証では、既存の書かれた経路と同型な完全閉コーンから幾何だけを再生できても、pending 行を著者として照合できない実例も確認した。これは今回公開した Lean の件数には含めない。受理・拒否の変更や raw 枝の追加ではない。保留の意味論判断を作ったものはない。
開幕時に確認した `yulang3@0315b43a872293f96f5918ec171f7e1c6b49e5a0` は C481 同期と inbox の更新履歴で、仕様の新規決定はない。X8–X11 の既存 Yulang2 記録はこの型商実機を実証しておらず、再実行もしていない。

道具: モデル名不明、Lean 4.35.0、GitHub; 委譲: モデル名不明、1 回、task /root/yulang302_resume（追加委譲・Codex thread なし）

## 追加の対象 Audit と主要な確認対象

- `lean/Audit/Cycle483I74OrdinalPath.lean`: `exact_full_ordinal_path_lifts_at_the_same_each_child_position`、`corresponding_chosen_ordinal_nodes_agree_in_every_return_predicate`。
- `lean/Audit/Cycle483I74ChildOrdinal.lean`: `paired_actual_constructors_pull_the_exact_selected_slot_to_the_same_ordinal`、`actual_hop_uses_the_unique_requested_slot_at_a_real_graph_ordinal`、`actual_constructor_description_has_exact_ordered_slots`、`actual_constructor_slots_are_distinct`、`raw_position_reads_exact_literal_child_at_its_original_ordinal`。
- `lean/Audit/Cycle483I74InteriorCorrespondence.lean`: `paired_selected_children_have_equal_regular_observations`、`every_paired_actual_position_keeps_its_own_return_status`。
- `lean/Audit/Cycle483I74PairedFocusedHop.lean`: `paired_exact_pose_selects_the_same_subpattern`、`paired_focused_hop_keeps_exact_pose_geometry_and_authored_meaning`。
- `lean/Audit/Cycle483I74AuthoredInterior.lean`: `checked_interior_compares_a_literal_child_without_transferring_source_authority`。
- `lean/Audit/Cycle483I74AuthoredInteriorActual.lean`: `actual_interior_retains_one_original_fitting_state`、`actual_distinct_old_child_sites_have_one_exact_signed_answer`。実行ガードを含む。
- `lean/Audit/Cycle483I74AuthoredInteriorReplay.lean`: `independent_finite_interior_checks_replay_the_exact_child`。
- `lean/Audit/Cycle483I74PairedInteriorSequence.lean`: `paired_exact_pose_selects_the_same_compiled_child`、`every_visited_paired_edge_stays_at_the_literal_coordinates_and_authored_pose`、`the_paired_quotient_signs_follow_the_independently_checked_path`。
- `lean/Audit/Cycle483I74SignedInteriorPath.lean`: `paired_path_retains_the_independent_source_typing_at_each_read_origin`、`signed_interior_is_at_the_exact_ambient_path_with_source_side_unchanged`。
- `lean/Audit/Cycle483I74SignedInteriorTerminal.lean`: `equal_finite_selection_replays_the_exact_ambient_terminal`、`signed_interior_terminal_is_the_same_physical_site_and_same_quotient_sign`。
- `lean/Audit/Cycle483I74RootedInteriorReport.lean`: `rooted_interior_keeps_the_original_full_report_and_old_author_typing`。
- `lean/Audit/Cycle483I74RootedInteriorActual.lean`: `actual_rooted_interior_has_an_original_fit`。実行ガードを含む。
- `lean/Audit/Cycle483I74AuthoredInteriorSafety.lean`: `finite_paired_source_prefixes_are_safe_at_exact_selected_nodes`、`every_nonterminal_original_author_site_in_the_rooted_suffix_is_safe`。
- `lean/Audit/Cycle483I74SignedInteriorReplay.lean`: `validated_local_components_replay_a_finite_interior_wire_at_the_same_sites`、`validated_local_components_and_old_sign_replay_the_exact_signed_interior`。
- `lean/Audit/Cycle483I74TwoFieldsSameRawChild.lean`: `old_actual_root_has_two_successor_positions_with_one_node`、`actual_matches_one_original_model`、`no_raw_target_only_function_recovers_both_written_poses`。実行ガードを含む。
- `lean/Audit/Cycle483I74RootedInteriorOriginalPose.lean`: `original_ast_location_replays_the_exact_full_geom_trail`、`rooted_report_fields_point_to_real_original_declaration_and_ast`。
- `lean/Audit/Cycle483I74ExactScopedInterior.lean`: `exact_scoped_interior_check_replays_the_same_rooted_read`、`exact_scoped_interior_reports_the_original_signed_site_with_no_extra_authority`。

## 検証と公開

- Lean 4.35.0、対象だけを `lean --trust=0 -DwarningAsError=true` で厳格確認。production 14、独立 Audit 17、名前付き検査 35（許容標準集合のみ）、guarded 実行 3。集約は対応する import 14 行の追記のみ。権威相対 Lean 32 パス、全 35 パス（設計・報告・HB を含む）。I-94 の追加行違反なし。既存 C482 の旧 production・Audit を変更していない。全体 `verify-lean.sh`・Lake build、Yulang2 実機は dot では実行していない。
- 実開始 `2026-11-28T06:29:34.000Z`。+10 `d3fdd47cb8571ce789c85dc5b76ad93dc7dd1b03`、+20 `89ce6efb7f5875369f0a8f06dfbc923d486d01e9`、+30 `660668a1925358709b27e4cc4abfc1935a4fba9f` で Lean 凍結、+40 `2b5b31b7c5b4e6b7d9b2674d1201f0dc6afed8d2`。凍結 tree `d813729b3b2329b9c6eed75c2daca8fec27f3873`、正確な権威祖先 `71c6e21fec7c279cab8984dc0ec7f6d89cc75598` と I-97 inbox を確認。次回は最新の inbox と統合の先頭を最初に読む。
