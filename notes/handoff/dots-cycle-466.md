# dots-main cycle 466: 実旧 head compiler の生成座標と native 発行の境界 (G04)

道具: モデル不明、Lean 4.35.0; 委譲: モデル不明、1回、task /root/yulang302_resume（追加委譲なし、Codex thread なし）

- 開始 2026-11-27T13:31:01.872Z、通常終了 2026-11-27T14:21:05.527Z UTC（実経過 50 分台）。C465 は開始時の監督統合 968cb04d43501ada1567de133f3a855f345ed118 に採用済み（work と同じ Lean tree e5da8c0f485146b2ad97944b868898fa4ca196b8）。最終監督参照 968cb04d43501ada1567de133f3a855f345ed118、I-89/I-90 ACTIVE。
- **G04 は未完、24 行中 20 行残り。** C466 science d8851213fd29edd100ba282d312117d7402fad55、Lean tree 85f87b20954706e7ea3bcad282c81eab300d51b3。実旧 compiler の source/capture 位置と実生成の普通行をつないだ。真正な I65 native issuer の発行はまだ出ない。一般の inline/bound producer、正準 checker、言語の判定は変更しない。

## I-89 の三条件と確立した断片

1. **独立判断と保存・反映。** 外部 GD の検査済み表、実単一可視 head について、旧 NestedDecode332.normalized → NestedMaterial332.assemble の生成した普通行、元 capture、元 head argument を結ぶ。旧 source-only Read が本物なら別手続き InlineGround331.certify は、新規普通行を本物の旧 Supported source として扱う。これは complete native address/issuer と別。preserve だけで新規行を認証しない。
2. **有限 data-only replay。** 元の head 位置と job 番号を渡すと、実旧 source index（外部で裏づけ済み）を使って生成し、exact 実行関係と同値。ordinary append 座標は厳密に「旧 equation 数 + job 番号」。join-free の既存 scope に限り、原文の生きた binder を正規化前へ引き戻し、別の binder と取り違えない。
3. **同じ State・健全性・具体化。** 真正な旧 receipt、別途供給した同じ post ordinary snapshot・完全な Native360 board write と既存 release・期待 endpoint を有限 guard で照合できる。任意の同じ post FitsFull で exact raw row、既存元 route、nativeSyntax と board code の解釈を得る。新しい物理 origin/issuer/route を発行せず、旧から全モデルを運ぶとも言わない。この前提なしに一般 G04 witness を作る条件は未達。

## 主要定理（範囲を限定）

| モジュール（GeneralDeclarativeI65I74…466） | 主な定理と寄与 |
| --- | --- |
| OrdinaryCaptureOrdinals / WrittenBinderCoordinates / CompiledCaptureCoordinate | no_created_ordinary_row_is_lost_by_the_ordinal_adapter、actual_allocation_receipt_links_exact_old_capture_to_exact_new_raw_ordinal、original_normalized_capture_path_and_raw_allocated_row_share_one_old_compiler_read：任意の支持つき旧 Read/assemble と job の同一出現を、exact が保存された raw 行と normalized AST binder に照合。補助・健全性。 |
| OrdinarySourceGrounding | actual_legacy_certificate_can_add_support_but_plain_transport_cannot：任意の実 assembly・真正な source-only Read・実出力行に旧 certify と rooted source trail。ordinary Models の比較先は旧名付き拡張状態。legacy_supported_proof_does_not_recover_discarded_native_ledger：native 台帳がなければ旧 source を得ても現行 field receipt は出ない。 |
| ReadOldCaptureReceipt / ReadyHeadCaptureReceipt | exact_old_capture_execution_has_data_only_receipt、previous_compiler_receipt_requires_the_actual_request_and_prechecked_head、ready_head_receipt_preserves_actual_source_identity_and_physical_coordinate：与えられた同じ source view で有限実行 iff、実 GD/単一可視 head と同じ元位置・物理座標。 |
| ScopedHeadCompileAtPose / ExactHeadCompilerReceipt | original_head_keeps_every_literal_query_address、one_actual_source_head_pins_legacy_assembly_and_modern_written_binder：実 head の exact compiled/source pose。両 compiler が成功する場合は同じ binder code。no_legacy_materializer_receipt_can_begin_at_a_modern_only_head_pose：modern-only の部分木があれば同じ head 全体の旧経路は none。受理／拒否の定理でない。 |
| UnshadowedLiteralCapture / LiteralCapturePullback / CapturePoseRoundtrip | literal_whole_fragment_has_finite_check、real_ready_capture_binder_lifts_back_before_normalization_without_changing_raw_row、source_pose_rebase_is_a_left_inverse_to_the_same_pose：任意の旧 covered/非 join の生存 path で exact 原文と逆照合。shadow を正しく飛ばし、二つの path を同じ元位置へ潰さない。 |
| CaptureLedgerErasure / CaptureKeepsExistingCoordinates / StableCaptureAcrossKeep | both_same_state_snapshots_have_the_same_compiled_ordinary_capture_data：同じ ordinary snapshot・registry・modes・実 request・同じ旧 source index を固定すると、native ledger/route に差があっても全 Option allocation は同一。an_actual_ready_capture_avoids_all_supplied_placement_addresses、two_actual_ready_allocation_runs_sharing_only_keep_are_same_literal_capture：既存 keep に指定した stored origin slot と route logical/physical を避け、同じ捕捉を守る。 |
| LexicalHeadProjection / CaptureNativePlacement | actual_emitted_capture_slots_project_the_same_original_typed_head_value：同じ actual capture table と独立に供給した型付き B6 lexical tree 上、ordinary syntax と全 assignment の exact 値。型 binder の authority や発行者ではない。comparison_with_the_existing_issued_phase_is_exact、an_authentic_capture_and_existing_placement_share_the_same_post_model、no_existing_native360_placement_has_a_nonvariable_ordinary_payload：供給済み既存発行に対する有限 exactness と same-post 健全性、現行 code 像の境界。 |

## 実対照・残り

- 実旧 C332 の ordinary raw ordinals 3/4 に物理 16/17、元 capture ordinal 2/3 と別々の literal binder path を生成。旧 source-only certificate は両行に成立。存在しない job は none。
- 真に fitting な実 prechecked head で、ordinary capture は target 7/raw ordinal 3。GD 欠落、元行のない source view、誤 head index/job を個別に退ける。既存 C464 の検証済み**供給済み** raw 投影 4→6→7 を加えても、同じ保存 native ledger に 7 の本物の route がなく、既存 inline field は開けない。その actual payload は普通の非変数 record {40: var 5} であり、あらゆる旧 Native360 write/phase/ordinal との exact 発行照合が false。
- 真に fitting な declared unary covariant head（key 20）は exact modern head を持つが、旧 materializer が全 wire で失敗。別の実 fitting shadowed head は生きた binder 3 の [tail,payload] を原文 [tail,tail,payload] に戻し、消えた binder 999 を使わない。
- 物理 7 に Bool native cell が既にある supplied variant も同じ具体 FitsFull を持つ。空 keep はそれを見ず target 7、明示 keep は同じ元 capture に target 8 を選ぶ。keep で既知列を守るだけで、全参照の freshness は未主張。異なる端点を同じ物理 7 に連言しても fitting model はない（上書きしない）。
- 次は実元 capture の構造と、その実 compiler 相が発行する**完全な物理 address/issuer と native origin/route**を同時に生成する真正な経路、およびその有限証拠。C332 普通の採番、C401 lexical 読み、C464 supplied raw cut、C465 existing exact release だけでは揃わない。新しい意味論、質問ノート、言語の拒否判定なし。G05/G10、G08、G06/G07、G20/G21、GD は別。一般 NFR・主型性は未証明。

## 検証・公開

- Lean 4.35.0、immutable Git bytes で production 16 を lean --trust=0 -DwarningAsError=true -o … Yulang/…lean、独立 Audit 23 を同じフラグで物理 focused replay。worker read-only --stdin 対照 PASS。公理 74 照合（標準集合のみ 74、公理なし 0）。守られた #guard_msgs/#eval 5 群と kernel proofs。Audit import は Yulang.* のみ。sorry、新公理、native_decide なし。全体 Lake/Rust/tools/verify-lean.sh は実行していない。
- Yulang2: spec §4/6.2/6.3、既存 source/ordinary compiler 原典、監査 work/dots-audit@55574b60 の x-oracle X8–X11・record-role cycle3 を参照。X10/X11 は再帰 record head の正しい K2 到達を実機で確立せず、今回の I65 issuer は監査で未観測。新規の Yulang2 実機実行なし。
- 39 新規 Lean、16 行の末尾 import だけ、設計2・心拍・報告、**44 paths**。旧 production 7,901・Audit 2,346、不変 spec/tools。expected-parent 非 force の work/dots-main だけ。+10/+20/+30/+40、実時刻の +50 解放。復旧なし、使用量枠不明、終了前空き 618M。
