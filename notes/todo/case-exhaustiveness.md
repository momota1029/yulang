# case 網羅性検査 TODO

出典: notes/design/2026-07-02-parting-assessment.md §3（Claude Fable 5、ユーザ承認済み）。

## 問題

case 式の網羅性検査が存在しない（2026-07-02 時点、リポジトリ全域に
exhaustiveness への言及ゼロ）。constructor 名の打ち間違い・列挙漏れが
型エラーではなく**実行時 match 失敗**になる。公開後、初心者が最初に
踏む地雷になる。

## 方針: 完全性を狙わない

Simple-sub の構造的部分型の下で完全な網羅性検査は難しく、
不健全な近似で塞ぐと偽陽性が推論の信頼を削る。狙うのは
**保守的な検査**: 「確実に漏れている」と言える場合だけ診断を出す。

判定できる条件（これがすべて揃う case だけ検査する）:

1. scrutinee の型の下界に、宣言済みの閉じた constructor 集合
   （enum / error / act operation payload / struct）が確定している。
2. 上界側に構造的な穴（record 型との合流など）がない。
3. arm に guard がない（guard 付き arm は「覆う」と数えない）。
   parser pattern（`~"..."` / `rule { ... }`）も失敗可能なので、guard 付き arm と同じく
   「覆う」と数えない。

条件を満たさない case は検査対象外とし、**何も言わない**
（「検査できない」を警告にしない。ノイズになる）。

## 診断の形

- 不足 constructor を列挙する: `case は point::origin を覆っていません`。
- タイポ検出を兼ねる: arm の constructor 名が scrutinee 型の集合に
  存在しない場合は、その場で「未知の constructor」診断
  （網羅性以前にこちらの方が価値が高い。先に実装してよい）。
- 診断は type-checker-diagnostics の既存計画（notes/todo/type-checker-diagnostics.md、
  notes/diagnostics/type-checker-plan.md）の語彙・range 規約に合わせる。

## 実装位置

- 情報源は infer / poly が既に持つ bounds（CompactBounds の Con 集合）。
  **新しい解析を足すのではなく、確定済み bounds を読むだけの pass** にする。
- lowering の case desugar 位置で arm の constructor 集合を記録し、
  finalize 後に bounds と突き合わせる。推論の途中に検査を挟まない
  （.rules: 推論内に diagnostics 分岐を撒かない）。

## 段階

1. **未知 constructor 診断**（網羅性の前段。タイポ即検出）。
2. 閉じた enum / error に対する不足 constructor 警告。
3. act operation / struct への拡張。
4. 警告をエラーに昇格するかの判断（公開後のフィードバックを見てから）。

## 完了条件

- showcase / examples / std が新しい偽陽性ゼロで通る。
- 意図的に一本消した fixture が正しい不足名を報告する。
- 検査対象外の case（開いた型）が沈黙する fixture。

## やってはいけないこと

- 網羅と言えない場合に「多分大丈夫」で沈黙ではなく警告を出すこと（逆。沈黙が正しい）。
- 検査のために推論の bounds 表現へ保護機構を足すこと。
- match 失敗の実行時エラーを消すこと（検査があっても最後の防衛線として残す）。
