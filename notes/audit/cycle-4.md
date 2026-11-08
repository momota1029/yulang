# Audit cycle 4 — recovery and regression confirmation

開始2026-11-08T14:25:12Z。ユーザー最新指示の25分上限を優先。最新integration `890e7bf1d` のstanding orders/inbox A-1 ACTIVE/max12を読み、前cycle3のrunning心拍と報告欠損を検出した。復旧を優先し、古い未公開成果を上書き・廃棄しない。

## 復旧と実行

- `git fetch origin integration/m1-final` と `git fetch origin refs/heads/work/dots-audit:refs/remotes/origin/work/dots-audit`。
- cycle3ローカルcommit80e0d0455とremote59e00c3bを比較。cycle3由来の差分だけを選び、別担当のls-recovery文書などを混入しない。
- 保存済みruntime-cycle-3ログから539実行記録、主張表38行を復元。cycle3報告とcrashノートを作成。
- 既存旧Y2binaryで `--no-prelude run --print-roots` を3回、各20秒上限で実行。direct=11、higher actual=22、higher eta=11、すべてexit0、合計約0.010秒。ソース/コマンド/出力全文はruntime-cycle-4-recovery.md。
- 新しい文書上の主張は追加せず、既存F1-11の再現性を確認。新しい意味論選択・質問ノート追加なし。既存質問のcycle3追記を復元。

## 公開・制限

公開先はwork/dots-auditのみ。notes/audit、既存質問ノート、必須心拍/crash記録以外を書き込まない。Lean/spec/実装は無変更。Lean buildは対象外・未実行。以前のログを再実行済みと偽らない。cycle3の停止原因/消費枠は不明。

次の一手: F1高階ordinary strictness喪失のdynamic demand trace、record whole-spread返値のprojection境界のsource/constraint provenance、実機で表現不可のXの代替観測を順に進める。これらは今回未実施。

最終公開ファイル数・照合・所要時間はcompleted心拍に記録する。

## 14:52 UTC 以降の短い復旧追記

この報告自体を保全した。全ログの公開復旧完了を意味しない。未公開の大きなログを含む原本は local `1794212d8` に残る。最新の保全範囲は `2026-11-08-short-recovery-checkpoint.md` を参照。
