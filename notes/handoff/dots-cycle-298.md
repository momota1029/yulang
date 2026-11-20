# Yulang dot 作業報告 第298周

- 2026-11-20 22:30 JST の回、実作業開始 13:33:24 UTC。
- 前周の公開 pin: `ede85106aec8640cd3ff1e3370f02e72f4f10fb1`。
- standing orders と inbox マーカーを統合側で再読し、I-54 の B4（observer/compiler → 据付前 source → 実 install 子）の順に対応。Rust の CST / authority には戻っていない。作業先は `work/dots-main` のみ。

## 今回閉じた点

1. **実 source を有限の質問へコンパイルした。** 過去と現在の等式・alias class を、既存の順序付き列挙からそのまま残す。型と effect 行の参照添字を独立に充填でき、その外の任意の値は判定を変えない。C287 の型添字 `[0,1,2]`・行添字 `[0]` の例では、型をすべて保ったまま row 0 だけ変えると raw 制約の真偽が変わる。この例は C287 の局所 symbolic fixture であり、B4 の ground initialization からの到達性は主張しない。
2. **候補ごとの有限証跡を実 Plan 列挙に合わせた。** 受け取った有限回答を検証し、被覆された具体入力では肯定・否定とも元の判定と一致する。未知は否定として扱わず保留する。列に重複があっても消さない（重複の対照は人工例、実 C252 の列は単一候補）。有限なのは参照箇所と供給された回答であり、型・行の値域や全解を有限化したわけではない。
3. **実際の raw refresh → install を最後まで追えた。** C252/C271 の実到達 source で、raw recognition が変わる一歩を projection には出ない更新として表し、更新後の状態から候補を再コンパイルして実 install を検証した。従来の直接 install と raw assignment の `Models`、leaf payload、最終 projection は一致する。固定したこの projection で弱く到達する厳密な後続は、残り計画の空リスト一つだけであることも証明した。
4. **実 nonleaf install で生成された子まで検証した。** C277 Display の実 parent install の生成子について、型添字 `[0,1]`、effect 行なしの局所回答から親子を合わせた `Models` と payload を保つ。親は `.node 1 [.node 3 []]`、子は `.node 3 []`。補完割当が raw model なら、実生成された子の Evidence を `EvidenceAt` に渡して親の Evidence を再構成できる。元の具体回答は任意の埋め草でモデルを保ち、この親子合成が成立する。この実到達点で子の `Current` を全項目構成し、`Installable` と同時に `Committed` であることを確認した。別の raw 子 install にはさらに非コミットが必要で、この実到達点は halted。任意深さの `EvidenceNode` 再帰は未証明。
5. **有限の弱い後続と raw 停止は別だと切り分けた。** 固定 raw 代表から出る strict projection の候補は残り計画の部分列に限られ、代表を一つずつ選ぶ窓は高々 `2^n`。一般の代表選択は古典的で、実行版は実証済みリストを入力する。C239 には弱い後続が空でも raw が発散する実例がある。対応範囲で raw accessibility に必要十分なのは、全 raw 到達先における silent-step accessibility。一般停止・任意の証跡自動発見は示していない。

## 検証と凍結

- Lean 4.35.0、既存キャッシュを再利用した分離再ビルドで **36 モジュール**。11 本の独立監査で **全 183 定理**を `--trust=0` で確認し、新しい仮定は利用していない（標準の `propext`、`Classical.choice`、`Quot.sound` のみ許可）。旧監査24本も再実行し、4 つの実行検査は保存出力とバイト単位で一致。焦点・既存バレル末尾と import の一対一対応も確認。
- 骨格の旧比較は `work/dots-audit` の `55574b6052ef1534fd0fc36d6d3617ebede59a0e`（X1 の子 Display 使用は局所的に一致、X2 の増大 where 受理は旧 lowering の別挙動）。この回に Yulang2 / Rust / 完全 Lake ビルド / CI を実行したとは主張しない。仕様・既存 Lean kernel・Rust は変更なし。

資料: [実行可能な質問](../design/2026-11-20-cycle298-b4-executable-witness-program.md)、[型・行の有限参照](../design/2026-11-20-cycle298-finite-type-and-row-frame.md)、[弱い後続と silent 区間](../design/2026-11-20-cycle298-weak-exit-window.md)、[列挙順を保つ回答検査](../design/2026-11-20-cycle298-aligned-plan-answers.md)、[定理目録・検証ログ](../verification/cycle298/)。

次は、実際に生成された C277 子の `Current` を基準に、まず同じ状態の parent 選択や別の実到達子に対象を広げる。この実例で別の child install は不可能なので、それ自体が必要な場合は非コミットの生成子を持つ別の到達例へ移る。有限 source 質問から raw 探索が必ず進むとは仮定しない。

## 主な定理の適用条件

- `GeneralRebaseExecutableJournal298.compile_exact`: 任意の raw 状態と加工写像について、新旧 journal コンパイラは項目も順番も一致する。`GeneralRebasePackedSource298.source_question`: 任意の registry・root のもとで B4 到達性を持つ source と任意の質問・補完割当について、元の充足割当が存在することと有限の欄へ縮めた回答の存在は同値。
- `GeneralRebaseAlignedScan298.scan_exact`: 状態・候補列・部分的 head 回答・reject/joint 回答の全ての選び方について、列を保った注釈走査と旧走査の結果が一致する。回答の中身を自動で発見する主張ではない。
- `GeneralRebaseRefreshInstall298.exact_two_steps`: 固定した実 C252/C271 source の同じ候補について、raw refresh と実 install が存在し、前者の projection は不変、後者の projection は旧 install と一致。全割当について install 後の `Models` を保つ。`GeneralRebaseRefreshPayload298.same_models_and_payload`: 同じ候補の据付可能な effect に限り、全割当・payload について `Models ∧ Evidence` が等価。
- `GeneralRebasePackedNonleaf298.model_and_tree_packed`: C277 の固定生成親子について、全割当・補完割当と任意の親子 payload に対し、局所欄から補完しても親子同時の関係が変わらない。`GeneralRebasePackedNodeCompose298.parent_of_answer`: 任意の有限回答と補完割当について、それが raw model なら子を経て親の evidence が得られる。`no_second_raw_step` は全ての次状態候補について、この実到達点からの raw source step を否定する。
- `GeneralRebaseWeakWindow298.target_codes_exact`: 任意の verified local program family・owner 列・output pool・B4 到達済み source・結果の残り事実列について、有限窓の出力に入ることと、raw な弱い遷移でその事実列に到達することは同値。`GeneralRebaseSilentFactor298.Source.necessary_and_sufficient`: 任意の registry・root・owner 列・output pool・状態について、この境界の raw accessibility と、全 raw 到達先での silent accessibility は同値。

静的検査は `bash tools/verify-lean.sh . <基点> --no-build` を前周と中間再読した統合の正確な木それぞれに対して実行し、全文を [static/](../verification/cycle298/static/) に保存。実行検証は [verify-focused.sh](../verification/cycle298/verify-focused.sh) および各独立監査を `lake env lean --trust=0 -j 1 -M 3200 -DwarningAsError=true` で再実行したもの。I-54 の 1 は局所 source と候補列の有限参照の完全性まで、2 は実 refresh と一般の silent 障害の切り分けまで、3 は既存実 nonleaf の生成子から親へ構成を一段通したところまで。言語仕様の選択は生じなかったため質問ノートは追加していない。使用量枠は不明。

前周の木 `9d83154824158606f2b1ab1188a2e5b6acd263d8` と統合 `930f732bc7f6eb41a350515e2af602e18e1d981c`（木 `b3a93e76ffc1f6caa739abe72a6c5f48a5ffb41c`）で静的比較 PASS。開始時の統合 `3d17bf3001770ac8dea4cea935dbd1ef82ede594` から監督役の進展はあったが、standing orders / inbox の blob は不変。時間の上限・承認待ち・環境停止による中断はこのサイクルでは発生しなかった。

後継の厳密な候補は [Current → EvidenceNode の残り条件](../design/2026-11-20-cycle298-next-evidence-target.md) に整理した。まず `GeneralNominalVersionedMixedEvidenceReduction235.InhabitedAvailable` のうち C277 の生成子に限り `GeneralRebaseGeneratedCurrent298.current` を示した。仮の leaf effect は raw site を追加せず任意の focus における request を維持し、位置の検査、alias の choice、共通モデルが揃う。一般化は `GeneralRebaseCompiledSelection277.picked_child` に相当する選択情報とこれらの各項目を分けて調べる。raw 子 install を試す場合は前もって非コミットを確認する。無条件の `GeneratedChildren` に必要な強い `Available` とは分ける。

- 最終報告書の固定時刻: 2026-11-20T14:23:27Z（経過 50.05 分）。前周からの変更 86 ファイル（完了心拍・報告を含む）。
  書き込み後に固定 pin で報告と完了心拍を読み戻す。
