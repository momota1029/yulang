# Yulang dots cycle 381 — I-66 S01: 実ソースイベントと同じ状態の権限

## 結果

固定の `dictionary_sound` と [C380 の I-66 一覧](../design/dots-cycle-380-i65-step1-skeleton.md) は変更していない。今回の一般 S01 は未証明。Lean で次を示し、途中で公開した。

1. `GeneralDeclarativeI65SourceEventTrace381.lean` の `event_classification_unpacks381`: 既に独立な source-event 規則が与えられている場合に限り、同じ有限診断木・子順・元の `Summarizes` と明示の event trace が得られる。`root_event_no_diagnostic_recovery381` は、条件を満たす別イベント二つが同じ選択節点と同じ子木に射影されるなら、診断だけで元の出現を復元できないことを示す。これは一般の source rule の実装ではない。
2. `GeneralDeclarativeI65NativeAuthority381.lean` の `retained_physical_origin_of_install381` と `no_erasure_of_native_authority381`: 実 install と現在状態・元ルートの保持を与えると、実盤面の完全な書込み・active owner/版を保持する。**同じ状態・同じ盤面・同じ書込み**でも、同じアドレスへの許可がある独立表とない独立表では exact release が異なる。権限を捨てた述語は両者と一致できない。2 表の許可差は仮定として明示し、許可を作らない。両者がある一つの実プログラムで発行されることも、候補が言語として拒否されることも主張しない。
3. `GeneralDeclarativeI65PinnedNativeRead381.lean` の `bound_read_fixes_literal_write381`、`pinned_origin_exact_release381`、`unpinned_endpoint_does_not_authorize_actual_context381`: 元の `AuthorizedEndpoint` の存在には world/gate を忘れる箇所があり、実際の gate が拒む場合でも別の明示された gate で存在しうる。同じ world **と** gate、実保持 slot を固定すれば、origin の同値でなく完全な実書込みと exact release を復元できる。全称定理の仮定や実言語の受理規則は増やしていない。
4. `GeneralDeclarativeI65WrittenJoinEvents381.lean` の `actual_written_join_scope_unpacks381`: C357 の実 `Rule.join` を使う宣言済み共変 unary join の範囲で、元の選択済み宣言、出現、子の需要順を保つ。C357 の `Joined` は same-tag の丸ごと捕捉を扱う限定形で、任意の source/capture/診断の実装ではない。
5. `GeneralDeclarativeI65WrittenJoinInversion381.lean` の `invert_actual_C357_at_written_join381`: 独立に得た caller-visible singleton と authored join head（本文実行、モデル、compiler/checker 結果、既選択 event は含まない）の下で、実際の C357 局所導出を反転して、その導出の書かれた実選択・元子を得る。普通用の coverage は同じ constructor で source mode と矛盾することのみに使い、旧 `Local` や C334 の受理へ橋を作っていない。
6. `GeneralDeclarativeI65ActualJoinTrace381.lean` の `actual_C357_join_selected_summary_trace381`: 上の *head 条件と実際の C357 局所導出が各節点に備わる* 有限の join-only 木では、親と各子の literal な `Request`・宣言 ID・順序を変えず、実 event trace と選択要約を得る。モデル仮定なし。すべての C357 分岐に head 条件が揃うことや言語の候補展開/拒否の完全性は示していない。

## S01 の正確な残り

C365 の `State` は `current, modes, origins, routes`、`Current` は `environment, ordinary, visible`、`Origin` は slot・issuer path・endpoint。実 release の完全アドレス、active 版と独立 grant を正本の状態から返す接続はない。C368 の `no_erasure_of_ready_authority` は普通側の authority を状態と同一視できないこと、C361 の `reading_the_value_cannot_recover_current_release` は値が同じでも owner を失えば読めないことを扱う。C381 の cut は **盤面を変えないまま gate を分ける**。これらはモデルで author/permission を逆算する手を排除する。

次の小単位は、原始ソースが本当に与える普通 provenance と、実盤面・同じ版に結ばれた独立の release 情報を、入口で一度だけ確定して各節点へ渡すこと。正本の状態表現に原始情報を保持するか、保持済みの入力から実 manifest を一意に戻す独立な接続を示す必要がある。どちらも今回の C365 からは示していない。既存の `Origins350.Attached` は ordinary 行が現在の等式にあることだけを保証し、`released` の出所は別。`NativeSnapshot360.commits_exact_snapshot` は実 commit の ordinary snapshot を固定するが、独立 grant を生成しない。この二つは attachment の部品として使えるが、片方をもう一方の代用にしない。各節点で都合のよい world/gate を存在量化したり、成功済み `Receipt` や診断から選択を作ったりしない。上で証明した投影と scoped C357 反転は、その現実の source rule を実装した後に使う。

## 残り（I-66、状態ラベルは据え置き）

- S01 未証明 — `classifies_unpacks_actual_source`
- S02 一部 — `selected_source_inversion`
- S03 一部 — `selected_mixed_k2_priority`
- S04 一部 — `elected_occurrence_has_general_head`
- S05 一部 — `selected_actual_ordered_capture`
- S06 一部 — `selected_ordinary_literal_receipt`
- S07 一部 — `selected_typed_actual_owner_and_retention`
- S08 一部 — `ordinary_or_typed_node_assembly`
- S09 一部 — `general_local_meaning`
- S10 未証明 — `selected_frontier_to_general_node`
- S11 一部 — `lower_selected_general`（tree/forest を返す一補題）
- S12 一部 — `general_tree_sound`
- S13 未証明 — `general_meaning_to_dictionary`

**未解決 13 件 = 未証明 3 + 一部 10。** S01 の scoped な部品を検証したが、元の全称 S01 は未証明。I-65 step 1 未完、step 2/3 未着手、S1/S2 未完、C 後回し。停止性・旧 `Local` 対応・旧 C334 接続・fixture 追加は対象外。

## 検証と公開

- 正本 `integration/m1-final` `18ced8754c55d0fa4923a653d2f9f7d742908e16`、inbox `b99fbb19f8c0c8c05abcd09f4cf3f44cfd4de26e`（I-66）。roles/inference も開始時に取得。開始 `2026-11-24T00:30:30.278Z`。前周 `073fdca4e4f011197efa089e2ef69c9df3175fd1` と canonical heartbeat を確認。
- Lean 4.35.0。6 modules を直接 `lean --trust=0 -DwarningAsError=true -o …` でチェックし、同条件で各独立 `lean/Audit/Cycle381*.lean` と合成 import を実行。すべて exit 0。26 宣言に標準の `propext`・`Classical.choice`・`Quot.sound` 以外なし。公開したソースと Audit の正確なバイト列 を取得し直し、別のローカル出力先で同じ検証を再実行した。固定 source の依存 4008 ファイルは integration の Git blob と source bytes が一致。新規 12 ファイルの改行・末尾空白・禁止トークンも確認。全体 Lake、全体 verify、Rust は未実行。
- 検証済み技術 pin `b2735df53305d4547536f257d5dfcad5dd8720b5`。全 15 パスのみ（新 module 6、独立 Audit 6、barrel 1、心拍 1、報告 1）、`work/dots-main` のみ expected-head non-force。barrel は C380 の完全な元バイト列を保持し、正確な 6 import を追加。凍結 2 パスは metadata のみ照合。質問ノートなし。使用量の枠は不明。
- 最終照合開始 `2026-11-24T01:20:50.049Z`。開始から約50分。ここで当周の作業を終えた。
