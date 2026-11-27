# dots-main cycle 465: 実 native compiler の相と元 issuer を照合し、producer の不足を切り分け (G04)

道具: モデル不明、Lean 4.35.0; 委譲: モデル不明、1回、task /root/yulang302_resume（追加委譲なし、Codex thread なし）

- 開始 2026-11-27T12:33:14.199Z、通常終了 2026-11-27T13:23:16.915Z UTC（実経過 50 分台）。C464 は開始時の `8a74c6c26ba7b695c85550cac13bec53b4fe6fbb` に採用済み。work・integration の Lean tree はともに `05407bd89f307a66a79d32eccb7bc48b76d7b955`。途中の I-90 は報告記法の更新のみ。最終監督参照 `48860cda68cb582a359fe20aa9722265d31295a9`。
- C465 の検証済み science は `e3f325ac59f9430e7499468e8ec2ae5e20b41ffd`、Lean tree `e5da8c0f485146b2ad97944b868898fa4ca196b8`（work 側。C465 の監督採用を主張しない）。**G04 は未完、24 行中 20 行残り。** 既存ソース、canonical checker・witness・raw graph・compiler への組み込みは変更なし。新しい verdict や spec の選択はしない。

## I-89 の三条件と今回示した範囲

1. **独立判断と保存・反映（限定した照合）**。任意の実 `Prepared`、old Native360 の実 compile と ordinary stage、供給された board/grant に対し、有限 replay は同じ本物の `Described/Compiled`・install・exact stage と、すでに ledger にある元 ordinal・`OriginRoute`・完全な `ExactRelease` に対応する。issuer・physical slot・node が同じだけでは release に代えない。辞書の選択・発行器ではない。
2. **data-only 検査（既存の field evidence を読む補助）**。I-89 の単一 actual visible 候補と既検査の GD 表の下で、実 field witness の元 path・raw row ordinal・元 issuer の一覧内 ordinal を同時に固定する。exact full write の検査を同じ論理位置で通った場合にだけ元 report をそのまま返す。既存 report の raw rows と pinned 対の第一成分は完全一致。物理 slot 一意性なしでも元 ticket を入れ替えない。同一 wire・report において先に作った slot-unique 補助は、pinned 版に旧一意性条件を足したものと同値。旧入口はどれも変えていない。
3. **同じ State と具体化（照合の範囲まで）**。独立な supplied phase/actual field 条件から、狭い補助の有限データを実際に得る。成功なら任意の同じ `FitsFull` モデルで、その元 nativeSyntax と同じ assignment における board write の値、実 terminal の旧 raw K2 と exact literal source を保つ。ただし一般の inline/bound head/capture に必要な新しい issuer・coordinate・native origin/route を compiler が生成することは示せていない。この欠けた前提を外部から仮定したものを G04 の完成には数えない。

## 主な定理と対象（健全性・完全性は上記の照合に限る）

| モジュール（`GeneralDeclarativeI65I74…465`） | 定理とこの周の意味 |
| --- | --- |
| NativeProducerGrammar / NativeProducerNodeCheck | `literal_compiler_grammar_is_exactly_the_image`、`compiler_node_is_injective`、`concrete_nonvariable_ordinary_source_is_never_native360_emission`：任意の old Code/Endpoint で実 compiler の像を exact に特徴づける。 `checked_compiler_node_recovers_exact_endpoint`：任意の code/node の data equality は文字通りの endpoint 等式と同値（point と interval を同一視しない）。補助、反例。 |
| NativeProducerPhaseOrigin / NativeProducerInstall | `finite_phase_origin_check_iff_literal_placed_active_row`、`actual_producer_and_same_phase_placement_iff_finite_data`：同じ ordinary snapshot・実元行/route・供給した exact grant・実 compile/install を指定した全入力に対する双方向。 `actual_phase_origin_ordinal_and_native_view_hold_in_every_same_fit`、`checked_installed_origin_is_really_the_original_compiler_payload`：健全性。 |
| NativeProducerSameHop / NativeProducerMergedReceipt / NativeProducerScopedField | `every_supplied_phase_hop_is_exactly_the_literal_physical_owner`、`exact_single_candidate_phase_field_has_finite_wire`、`actual_existing_compiler_and_field_have_finite_same_phase_witness`：既検査の GD・単一 visible・既存の actual head field と実 current install を組み、有限 witness と照合。 `phase_owner_and_report_share_actual_original_row_in_every_fitting_model`：同じ State における健全性。 |
| NativeProducerInlineBoundary / NativeProducerNoField / NativeProducerClosedBoundary | `a_real_inline_step_needs_an_origin_outside_all_native360_writes`：現行の四 inline lane は nonvariable ordinary の元 payload 行が必要。 `no_prechecked_field_receipt_on_a_sole_native360_origin_list`、`compiler_owned_field_needs_an_origin_outside_the_native360_image`：全 origins が旧像にあるなら、その表・state の全 field wires に対して none（inline に限らず、任意の既存経路）。現在の全 state がこの像だとは仮定しない。 |
| PreviousCompoundProducerBoundary / PreviousOrdinaryMaterialBoundary | `existing_literal_write_projection_has_exact_source_fragment`、`an_actual_associated_receipt_projects_iff_its_code_is_literal`：C394 の任意の実出力は元 output/slot/本文と結びつくが、old write 射影には bare/tagged nominal とその限定した再帰 args が必要。 `actual_old_assembly_keeps_allocations_and_available_sources_separate`：任意の実旧 C332 assembly で追加普通行は出るが、元判定を運んだ available source にはならない。ordinary Models の保存先は **named augmented** state。補助、反例。 |
| NativeProducerPinnedTicket / NativeProducerPinnedField / NativeProducerPinnedCompatibility | `field_reader_pins_shared_literal_ticket_ordinals`、`pinned_phase_check_is_exact`、`same_existing_report_checked_at_exact_ordinal`、`pinned_report_keeps_the_issued_origin_and_cycle_in_every_fit`：任意の受理した既存 witness を保ったままの、元 ticket ごとの exact read・当該相の照合と all-FitsFull 健全性。 `successful_head_reports_have_exact_pinned_raw_row_projection`、`pinned_phase_and_slot_unique_compatibility_is_exact`：元の報告の raw 行と前の補助を保つ。 |
 
## 実対照

- 既存の実 `NativePipeline360.run false` から actual prepared/live output/board を使った。保持済み発行行を fixture に別途供給した正例は、物理 slot 101 と真正な移動元 107 の両方で成功。別 ordinal、origin 欠落、route の欠落・issuer 違い、別 ordinary stage、grant 欠落、version 違い、二重 install を個別に落とした（全て kernel 証明）。
- 旧 C332 の実 `NestedExample332` は新規の普通の 16,17 と exact capture 列を実際に作る。それらが新しい available source origin にならないことを示した。
- 実 C464 系の同一報告・同一具象 `FitsFull` 上で、同じ物理 slot に別々の issuer [402] と [499] の二つの元行を置く。対応する二つの旧 wire はともに成功し、同じ path/raw rows/terminal でも最初の物理・元 ordinal 対は (3,0) と (3,3) に分かれる。両 issuer を混ぜた二対照は失敗する。どちらの inline owner もいかなる旧 Native360 write で代用できない。失敗は **現行証拠の支援範囲**であり、Yulang 言語の拒否ではない。

## 何が未証明か、次の橋

- (1) actual head/capture の元位置付き構造・型 projection と、同じ真正なコンパイル相が **座標・完全な address/issuer・保持 native origin と route を同時に発行する**ところを結ぶ。(2) その発行結果を C464 の exact raw cut と C463 の論理・物理位置/既検査 GD に構造帰納で接続する。この二つから初めて I-89 の一般 G04 witness を得る。既存の C401 typed associated-RHS・C332 ordinary allocator・Native360 exact release はそれぞれ別の足場。値の等しさ、新しい ordinary 枝、または別の出力 receipt から issuer は作らない。
- 候補走査・曖昧性前の K2 の優先は G05/G10、残余 join は G08。open tails G06/G07、一般 nominal mode/kind/multiarg G20/G21、GD は既指示どおり別。主型性や一般 NFR は未証明。意味論の追加選択・質問ノートなし。詳細は `notes/design/dots-cycle-465-source-and-placement-boundary.md`。
- 非公開の確認（公開計数に含まない）: 実旧 C360 fixture は出力指定だけを除いても普通の prepare と同じ行が残るが、同じ demand 上の native compile は出力指定が無ければ全 wire で不可能。version/宣言または出力 ordinal を忘れた同じ origin が、真正な board release を含意しない実対照。構造的 typed associated-RHS を古い同じ evaluation に保って projection できる断片は、actual head での発行をまだ含まない。別の旧 `InlineGround331.certify` は真正な source-only read を指定すると実 C332 新規行に旧 `Supported` の source provenance を付けられるが、I65 の物理 native origin/issuer/route は発行しない。実 C332 の捕捉行は exact-empty 終端で、幅終端との置換は raw K2 と fitting assignment の両方を変え得るため採用していない。

## 検証・公開

- Lean 4.35.0: immutable Git の exact byte から、production 15 を `lean --trust=0 -DwarningAsError=true -o … Yulang/…lean` で焦点ビルド、standalone Audit 18 を `lean --trust=0 -DwarningAsError=true Audit/…lean` で独立実行。worker 側の read-only `lean --trust=0 -DwarningAsError=true --stdin` も全 18 PASS。公理 57 照合のうち標準集合の部分のみ 53、4 公理なし。実 kernel 対照と守られた `#guard_msgs/#eval` 1 群。sorry、新規 axiom、native_decide なし。Audit import は全て Yulang.*。全体 Lake/Rust/`tools/verify-lean.sh` は実行していない。
- Yulang2 との照合: §6.2/6.3、既存 native compiler/phase 原典、監査 `work/dots-audit@55574b60` の `x-oracle.md`（X8–X11）と `y2-claims-record-role-cycle-3.md` を確認。X10/X11 は正しい再帰 record head の K2 への到達を実機で確立していない。今回の origin/issuer ledger と同相の照合はその監査でも未観測で、Lean 内の定理を Yulang2 実挙動に読み替えない。この周は Yulang2 実機を走らせていない。
- 差分は新規 Lean 33、集約の末尾 15 import、設計 2、心拍、報告、合計 **38 paths**。旧 production 7,886・旧 standalone Audit 2,328、既存 spec/tools に変更なし。expected-head・force=false の `work/dots-main` のみ。+10/+20/+30/+40 は実時刻で確認。復旧なし、使用量上限不明。終了前空き 645M。
