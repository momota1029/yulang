# Yulang dots cycle 382 — I-66 S01: 実ソース入力と権限を同じ状態に留める

固定の `dictionary_sound` と [C380 の残件一覧](../design/dots-cycle-380-i65-step1-skeleton.md) は変更していない。実ソース原始観測を、普通側の出所表と native 側の同じ物理状態・独立 grant に結ぶ部品を証明した。一般の `Classifies` または候補の受理・拒否は今回も示していない。

## 証明済みの部品

1. `OrdinaryAttachment382`: `ordinary_attach_present_iff382` と `exact_ordinary_attachment_cannot_authenticate_release382`。実 `Origins350.attach` の成功は現在の普通等式に authored/produced 行があることの検査。両行リストが同じで、供給された完了表だけが異なる二つの場合はともに attach できるが、直接の作者行がなく、片方の表にある完了済みの支持経路がもう片方では一つも完了していなければ差が出る。単一 owner の一意性は仮定していない。
2. `CommitAuthority382`: `exact_snapshot_commit_source382` は実 `NativeSnapshot360.commit` から前の普通 snapshot、直後の compiler stage、実 write と active 版を結ぶ。`committed_source_needs_its_exact_gate382` は保持された元行と literal route の条件下で read が**既存の完全アドレスの grant**と同値であることを示す。`earlier_exact_gate_survives_other_commit382` は別 target の実 commit を越えて、同じ gate で読めるか否かが不変であることを示す（同じ元行・経路の保持は入力）。
3. `SourceBoundary382`: 一つの供給済み context に普通 ledger、実 world、正確な current 等式、独立 gate を保持する。`ordered_primitive_boundary_exact382` は、直接 authored、完了済み ordinary 出力、exact native release の原始観測を、引数リストの順序と各出現を保持した形で得る。存在の定理であり、消した実イベントの一意復元でも分類器でもない。
4. `CarryBoundary382`: 実 commit の growth 証拠で**同じ** ledger と gate を次の snapshot に付け直す。同じ manifest を使う場合の構成であり、実行器があらゆる commit 後も manifest を変えないという主張ではない。`existing_primitive_list_commit_keeps_actual_route_order382` は既存の証拠を運び、普通の direct/completed の別・実 owner、typed の slot/経路の添字、リスト順序を保持する。`actual_where_row_does_not_create_authority382` は、実 where 等式が次の普通 snapshot にある一方、独立した author/完了がなければ支持つき入力にはならないことを示す。等式を K2 グラフから消す主張ではない。
5. `LiteralBoundarySources382`: `actual_two_endpoints_and_native_share_literal_source382` は、実 `SourceEndpoint359.Read` の literal 又は authored open-spine 由来の lower/upper の行を順に保持し、同じ context での exact native release と連結する。中心の read、モデルの同値、選択成功を前提にしない。第三要素は別に指定された typed 読みであり、端点照合そのものに中心読みを必須にするものではない。元の author 表と境界の author 表は明示的に同一。
6. `CommitLiteralBoundary382`: `mixed_endpoints_after_actual_commit_iff_full_grant382` は上の両端点と実 commit の新しい保持 write の列が存在することと、**外から与えられた actual gate の完全アドレス許可**との同値。`mixed_commit_read_not_recoverable_from_state_world382` は、同じ実 commit・前後 state・world・元の普通 author・literal read keys に対し、与えられた独立 gate の許可差を落とした述語では両方と一致できないことを示す。別 gate の発行や、ある言語プログラムの採否は主張していない。native 側は既存 C360 の `Write/Code` の範囲であり、任意の型/行出力を追加したわけではない。

## 一般 S01 に残るところ

C365 の `State` は、普通 `Attached` の行所属や native commit の整合性だけから、実際の独立 completion/release manifest を一意に戻せる構造になっていない。今回の context は明示入力であり、任意の gate に本物のお墨付きを与える constructor ではない。次は、正本の宣言的入力から同じ author/active version/manifest を一度だけ絞れる原始接続を実装又は証明し、その**同じ**境界を実 source rule の各節点に渡す。C365 の固定仕様が要求する observable typed source state の表現上の課題であり、全称定理へ新しい premise を足して解決しない。各節点で都合のよい gate を存在量化しない。既存の診断、compiler/receipt 成功、モデル、同じ見かけの output 値を逆向きに使わない。C349 の `Problem` は caller の source bundle・普通 state・demand を持つがこの gate を持たない。C363 の `openCurrent` も gate は別の入力で、内部で発行しない。これらだけでは固定 `State` に実 manifest が付いたことにならない。commit の普通 snapshot 一致から、compiler の元 caller 環境と現在の可視宣言表が同じとも推論しない。その照合と歴史的 writer の範囲は原始ソース側で保持する。任意の source 診断規則は依然必要。

## 残り（I-66）

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

**13 件未解決 = 未証明 3 + 一部 10。** S01 の固定全称文は未証明。I-65 step 1 未完、step 2/3 未着手、S1/S2 未完、C 後回し。停止性・旧 `Local`・旧 C334 への橋・fixture 追加なし。

## 検証と公開

- 正本 `integration/m1-final` `d0fb274b1c5fd43b7592b615bfddca311be0be46`、inbox `b99fbb19f8c0c8c05abcd09f4cf3f44cfd4de26e`（I-66）、roles/inference と開始前 heartbeat を取得。開始 `2026-11-24T01:30:36.058Z`、前周 `1dfd1e4d4e8adfb6493354d68be361e71450f211`。検証済み技術 pin `3a49f3efb52b4fb286a4b1f74bee8bf0b37294f2`。
- Lean 4.35.0 の `lean --trust=0 -DwarningAsError=true`: 6 module の直接チェック、6 独立 Audit、合成 import を実行。31 監査項目は標準の `propext`・`Classical.choice`・`Quot.sound` のみ。exact Git bytes を別の出力先に取得して再計算・再実行。依存元 4023 source bytes を integration の Git blob と照合。新規 12 ファイルの改行・末尾空白・禁止トークンも確認。全体 Lake、全体 verified CI、Rust は未実行。
- 変更は 15 paths（Lean 6、独立 Audit 6、barrel 1、心拍 1、報告 1）のみ。完全な既存 barrel の bytes を保持し、新規 import 6 行だけを追加。I-57 凍結2パスは metadata だけ照合。`work/dots-main` のみ expected-head non-force と exact 読み戻し。質問ノートなし。使用量の枠は不明。
- 最終照合開始 `2026-11-24T02:20:55.563Z`。開始から約50分。次工程へは移っていない。
