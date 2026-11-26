# C430: I-77 の監査依存を除く

C428 の対象七件から他の Audit import を除く。MixedSibling と C429 修復版 Forest はそのままにし、対象が再利用する本物の source fixture / fixed wire / 選択証明データだけを、衝突しない namespace の production helper に置く。BodyReplay の共有 readback は公開名を保って production に移す。旧 ordinary rival も同じ保存済み fixture から再生し、候補選択・K2・要求順・固定結果を読み替えない。

新しい局所規則、R15、公開 dispatch、固定定理、spec、凍結ファイルには変更なし。対象七件の元の監査ターゲット30件は保持。対象監査は production-only `LEAN_PATH`、空の作業ディレクトリからそれぞれ実行（Lean 4.35、trust0、warningAsError）。広い統合は exact Git replay 後に判定する。