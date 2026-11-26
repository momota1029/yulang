この周に閉じた C の行: なし。

# C429: C427 の Audit 3 件を I-76 に合わせて修復

開始: 2026-11-26 00:30:57.000 UTC、報告は開始から50分経過後。対象は I-76 の Forest / Readback / Visits のみ。C15 の受理や新しい R15 は作っていない。

- 元の入力・graph・宣言順、既存の実行版へ渡す wires、選ばれた同じ親子の再現に必要な共有定義を `Yulang.GeneralDeclarativeI65I74StructuralWhereAuditSupport429` に移した。SameRole の元 Audit は変更せず、補助データは別 namespace、既存 Readback の外向き定義名は保持。3件の元テスト・証明本体と公理表示19件は byte-for-byte 一致。C427 の他4 Audit は blob まで不変更。
- 監査はそれぞれ `Yulang.*` だけを明示 import。Lean 自身の header parser による検査で確認。修復前の元3ファイルは同じ条件で exit 1（`unknown module prefix`）、修復後はすべて exit 0。
- 保持したチェック: 元の二つの where 子の順序・同じモデルでの辞書、元の capture と compound 行、順序・候補の取り違えを弾く readback、根と実際に訪れた候補の K2、および照合しない field の閉路と同じ label の見落とせない閉路の違い。

## 検証

Lean 4.35.0 `--trust=0 -DwarningAsError=true`。exact Git bytes から対象 production 14本を再コンパイルし、14 import の同時読み込みも exit 0。Audit は production のみの `LEAN_PATH`、毎回新規の空 cwd、peer Audit olean 無しで一つずつ単独実行。

| C427 Audit | 終了コード | 公理表示 |
|---|---:|---:|
| Core | 0 | 9 |
| Forest | 0 | 8 |
| Ordered | 0 | 6 |
| Readback | 0 | 6 |
| SameRole | 0 | 7 |
| Spec | 0 | 9 |
| Visits | 0 | 5 |

公理は50件すべて標準のみ（`propext`、`Classical.choice`、`Quot.sound`）。既存 R14 の公開入口を使う元 projected-spec Audit も同じ production-only cache で exit 0（10件、変更なし）。技術差分は修復3、helper1、barrel 末尾追記1。凍結ファイルは blob ID のみ確認。全体ビルド、Rust、NoFalseRejection、停止性は実行していない。

## 統合に渡すもの

修復の immutable pin `794194e76370c26d2a967d8f535b7661e2e8a162`。 [C427-only 再現・統合手順](../design/dots-cycle-429-i76-supervisor-replay.md) blob `8bad080a65b4b87135a1f8ea2854146073f6a94a`。基準 `34ece1698e5b8369f08e8d22e028a78d900e1594` の上に C427+C429 の21 blob と14行の barrel 追記だけを投影すると、root tree `20fa37d2305da048331b7275190e6b836a987ffb`、Lean tree `a45ba5ec2327014fc9d2f0d383cda8ec2c26236f`（Git `mktree` と `diff-tree` でも A21/M1 を独立確認）。`work/dots-main` 本体と違い C428 は入り込まない。最終読戻し `34ece1698e5b8369f08e8d22e028a78d900e1594` では対象21 blob のうち同一のものは 0 件で、C427 の統合採用はまだ確認していない。

C428 の既存ファイルは無変更で別 cache の依存順回帰を通過（7 production、9 Audit、標準公理43表示）。これは peer Audit が見える互換性試験で、単独監査ではない。 C428 の監査7件は依然 I-76 非適合。該当ファイルを変更しておらず、C428/公開 R15 の統合完了を主張しない。

**C の残り: 8 行（C15–C22）。**
