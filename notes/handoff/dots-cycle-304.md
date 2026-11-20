# C304: deferred ladder の全実経路と、一般 B4 observer の条件

## Ladder の完全な結果

- `GeneralDeferredLadderEarlyExact303.exact_next`：任意の深さ `n`、早期の相 `k ≤ n`、合法な terminal-source refresh の証明書について、実カーネルの次の状態は輸送した list install の結果に限り、実際にその一手がある。未使用の空 record 形状を足した refresh もこの定理で覆う。
- `GeneralDeferredLadderClosed304.classification / initial_acc / halted_outcome`：初期 deferred ladder `before n` からの**実 raw 遷移すべて**について、到達経路は最大 `n+2` 手で、`Acc` が成立。どの合法な refresh がどの相で選ばれても、停止した経路はちょうど `n+2` 手で辞書は同じ。停止状態の全モデルで根の辞書の証拠が成立し、観測表を読む実行器は燃料 `n+2` 以上でその辞書を返す。無限個の refresh 後者があり得ることとは矛盾しない。
- `GeneralDeferredLadderControlBridge304.executable_exact / executable_halt`、`GeneralDeferredLadderControlCover304.every_control_realized / all_nodup`：raw 行の個数と terminal-source の既知性から相を計算し、`2(n+2)` 個の抽象状態を重複なしに列挙。実到達状態から、実 raw 後者の**像**が有限 successor 列とちょうど一致。列の各相は実経路で到達できる。異なる raw 状態を等しいとはしていない。

## 一般の B4 に使える結果

- `GeneralMixedDiagnosticLocal304.local_iff` と `GeneralMixedDiagnosticCompiler304.compiler_exact / recursive_iff`：任意の registry・需要について、現在の head view（文脈・raw/centered 行・辺・alias・全モデル）と、履歴モデルおよび各出力クラスの履歴上での意味が一致すれば、V8 の全局所診断と再帰診断木は同じ。既存の実行版入力が証明済みかつ complete なら同じ実行器を使える。C280 archive 置換がそれらの仮定を満たす場合を接続した。
- `GeneralMixedDiagnosticSliceCounterexample304.head_view_alone_insufficient`：同じ head view、同じ空の全モデル集合でも、merged-output conflict は異なり得る。これは任意の journal に対する閉じた反例で、共通の初期状態から両方が到達可能とは主張していない。
- `GeneralMixedDiagnosticReplayStep304.actual_install` と `GeneralMixedDiagnosticReplayTrace304.exact_trace`：全クラスの出力要求の所属を変えない実 install なら、開始時の選択 ID・head view・履歴 slice が対応し、移送先が実到達であれば、有限 install 列を同じ手数で移送できる。各移送先の履歴に対するキャッシュ健全性を別に使う。実例では明示出力要求が空でなく、以前のモデルが実際に除かれる。
- `GeneralNominalTotalLocation304.arguments_total / status_reindex` と `GeneralNominalPendingReindex304.pending_exact`：相互 refinement の下で引数位置の成功・失敗をともに移送し、スロットの「不在／未解決／既知」を区別して保存する。input pending も有限の引数走査で正確に読める。0 と 1 の位置を実際に交換した例では、同じ source の引数位置が `(0,0)` から `(1,1)` に移る。

## 検証、残り

I-54（統合 `e2ad1d61f9de979dd8259877c7940501b6ea5d98`）を読み直した。36 新規 Lean モジュール（C303 で未公開だった8草稿を含む）、36個の独立監査と159宣言、対象限定 `lake build --wfail`、全監査 `--trust=0 -DwarningAsError=true` が通過。実行例は13件（幅広形状で最初の一手3件・全経路5件・有限制御4件・スロット交換1件）。C302 の独立監査7件・230宣言も別に再実行した。全体ビルド、Rust、CI は未実行。利用枠は不明。仕様の変更・意味の質問なし。

[検証コマンド・全ログ](../verification/cycle304/) / [全モジュール](../verification/cycle304/module-list.txt) / [全監査対象](../verification/cycle304/audited-declarations.txt)。主要成果を含む中間公開 `d158a6ac1024211bfa6e488c6073937ef0dcd6f2` では、ローカル検証済み差分の全104パスを GitHub から取得した tree と blob ID で照合し完全一致した。

次に、(1) 相互 refinement より強い観測一致から、任意の再索引に対する消去済み recursive report の同値を作る、(2) 実際に増えた出力要求が保存済み effect を再活性化する場合の slice を証明する、(3) C279–281 の有限な棄却割当を実 compiler に接続する。現段階は**一般の混合 raw 停止性・完全な B4 compiler・一般の EvidenceNode の証明ではない**。[次の設計](../design/2026-11-20-cycle304-next-general-observer.md)

静的差分検査は、今回の統合先・手元の前サイクル・GitHub の前サイクル公開ピンの3基準で通過（[出力全文](../verification/cycle304/static/)）。旧 C240 の任意追加検査は依存不足／時間上限で完了扱いにしていない。

開始: 2026-11-20 19:31:50 UTC。検証・公開を含め約50分。
