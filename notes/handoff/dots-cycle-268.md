# Cycle 268: 実 source の V8 診断と、管理遷移を含む弱進捗

公称・実開始 **2026-11-19 07:30:00 UTC**。最終取りまとめ **2026-11-19T08:20:00Z**（50.00 分、55 分上限 08:25:00 UTC）。出発は 267 最終公開 `499b87919b44c2d2acb8b573236a4b171bd92a32` と同一 tree。integration `1b113cfd93bd7ab89ccb1e4b29653dfd5f655775` を開始・公開時に照合し、ACTIVE、I-51〜53、凍結範囲を確認した。作業先は `work/dots-main` のみ。次枠は先取りしない。

## 達成した範囲

1. **V8 Local 判定（健全性・条件つき完全性）**。 `GeneralRebaseDiagnosticCompiler268.sound` は実 registry・journal・生成済み focus から、未知を区別する部分的な判定を計算し、確定結果が宣言的 V8 Local に一致することを示す。 `.exact_of_complete` は独立な各回答の健全性、組み上がった判定の全域性、既存の source-side 範囲の下で iff。未判定の `none` は言語の `.pending` と区別。 `GeneralRebaseConsensusDiagnostic268.known_k2` は非 pending の既知 K2 を、merged/sharing が未知でも安全に拒否できる（両分岐が同じ拒否）。言語の優先順位は変更していない。
2. **K2（健全性・構造部分の完全性）**。有限 Fin-slot 上の直接辺と非空循環を旧構造述語と iff で照合した。意味辺は正・負・未知の答えから下限グラフと上限グラフを作り、下限の循環で肯定、上限の非循環で否定。元の Versioned RootK2/CandidateK2 の raw および centered 枝に接続し、後者は実 source から列挙した完全な構造 Plan の検査位置を走査。有限 Origin 窓の肯定は実循環に戻せるが、否定には独立の循環被覆またはモデルなしの証明が要る。一般の Origin 有限支持・意味辺決定は未証明。
3. **Inspection・output・sharing・merged（健全性・構造部分の完全性）**。登録済み site、alias、同じ中心列・role、検査結果と fresh から計算できる範囲を分離し、意味論的 SameInputs と head 適合は独立入力とした。Output/sharing は現在の Frame 候補を列挙し、各 query が同じモデルにおける複数条件の同時成立を判定する。 `GeneralRebaseMergedSlices268.bounded_iff` は任意の許可された atoms/classes 列を membership 同値な有限 journal の部分列に取り直せると証明した。重複や並べ替えを許した元仕様と iff。Merged class がない場合は列挙しない。ある場合の全列挙は指数的で、各部分列の拡張前後のモデル存在は依然独立入力。
4. **実 compound-where install（補助・実例）**。 `GeneralRebaseCompilerFixture268.actual_run` では aggregate な RootK2/CandidateK2/Inspection/Output/Merged/Sharing 判定を入力にせず、元 journal から宣言と順序付き子を選び直した。raw K2 は既存 rank 減少定理の負の辺情報から有限グラフで計算し、full Origin 非循環、head、joint effects、sharing の低層事実には既存の別証明を使用。 `.actual_generated_install` はその確定判定を前周の構造選択と独立の joint/novelty 証明に接続し、実旧カーネルの一歩と据付け後のモデルを得る。一般の意味論ソルバを開発した、という主張ではない。
5. **管理遷移の反例・弱進捗（停止性の範囲と旧 Step との対応）**。 `GeneralRebaseStutterPlanBoundary268.no_exact_factor` は reachable 238 の refresh/reobserve 前後で固定ライブ射影が等しいのに厳密な構造 Plan 表が異なるため、その表を射影だけで復元できないことを示す。 `GeneralRebaseStutterInfinite268.no_finite_support` は実際の 239 反復で、どの固定 basis でもある時点から無限個の異なる具体 stutter 到達状態があることを示す。したがって具体状態の有限全列挙を退けた。これらは有限な振る舞いの商や、同じ射影で strict successor を持つ・持たないの完全分類を反駁しない。
6. **有限な弱ステップと再計算（停止性・条件つき対応）**。 `GeneralRebaseWeakProgress268.wellFounded` は任意有限長の stutter の後に strict 1歩を置く弱関係の整礎性を固定 basis の残数から示した。任意の旧有限経路は strict 回数を保った弱経路と末尾 stutter に分解できる。 `GeneralRebaseWeakTerminal268.terminal_iff` は弱終端と「元のすべての有限な後続経路で射影が不変」の iff。 `GeneralRebaseStutterKeys268.visit_exact` と `GeneralRebaseKeyedWeakObserver268.step_iff` は、領域上で各代表からの stutter 持ち上げと各代表に対する strict 提案の健全性・網羅性を満たす有限キーがあれば、局所弱遷移を有限探索で正確に求める。 `GeneralRebaseKeyedWeakScheduler268.recomputed_completion` は basis 支持・領域保存の下で具体状態を選び直すたびに再計算して上の弱終端へ達する。証明の存在証人を実行可能な concrete state chooser にしたわけではなく、元の非停止の反復を停止に変えてはいない。

## 検証と公開

- **新規ライブラリ 36 モジュール、固有の名前付き宣言 301 件**（定理数ではない）。Lean 4.35.0、trust 0、警告エラー化で焦点ビルド。新規監査9本を各々独立に再実行して exit 0、標準公理のみ。 [再監査](../verification/cycle268/final-audit-recheck.txt) と [各構成・ログ](../verification/cycle268/)。
- [integration 基準の静的差分ゲート](../verification/cycle268/diff-gate.txt) と [前サイクル基準の静的差分ゲート](../verification/cycle268/prior-cycle-diff-gate.txt) exit 0、`git diff --check` も成功。I-51: 監査は Yulang.* のみを import。I-53: 各新モジュールの barrel import は各1行。旧 Lean ソースは barrel 追記のみ。凍結中の specs、plan、Audit.lean、README は無変更。全体 `lake build --wfail`、全体公理ゲート、CI、Yulang 実機はこの周では未実施（焦点ビルドと既存の依存キャッシュを使用）。
- 検証済みの途中 tree は `901e9e74`、`0e116e37`、`d3eb1216`、`7607d48e`、`dd1ac7d5`、`bd5a6bfa`、`0aa45e51`、`5737ee66`。開始および10分刻みの心拍と、最終 tree の照合で進捗を記録。ディスク空きは後半約55 GB。利用量の枠は不明。

## Yulang2 との照合と次の境界

既存の監査・証明から引き継いだ K2/判定順・238/239 の回帰例に対して Lean 上で確認。この周で Yulang2 実機による新規照合なし。新しい言語仕様の決定や、元 Step の停止性、主型性、B4 の全体実装は主張しない。

次は (1) 意味論の正負の回答を具体的なソルバ／独立に検査できる証明証人から供給し、有限 Origin 被覆の十分条件を実際の reachable 記録で検証、(2) 反例を避けつつ代表ごとの弱対応を保証する有限キー、または同じ source からの具体証人付き探索を実装、(3) mixed-time packet、Permitted、Frame/EvidenceNode と、弱終端と source 全体の診断の関係をつなぐ、の順。設計と前提の所在は [設計メモ](../design/2026-11-19-cycle268-local-diagnostic-probes.md)。
