この周に閉じた C の行: C08 / X6 前半。単独候補 `R :{tick 'a,tick 'b}` を選び、二つの binder が同じ実 payload `int` の全体を捕捉します（`dictionary_sound_R8`、`PlainMerged416.check_sound`）。

## 実装と証明

- [仕様 6.3 / X6](https://github.com/momota1029/yulang/blob/efb4a2de77af97ac26192fc5abfe651ef3e982f9/spec/06-roles.md#L111-L117) の単独候補です。元の `R :{tick int}` の一つの variant と payload slot を読み、元の二つの名前を同じ実 point に捕捉しました。別々の arm や、名前付き nominal として扱っていません。正規化は同じタグ一つ、実構造の検査位置も根一つです。元の binder 名、タグ、候補の序数、捕捉位置は同じ入力で別の証人に替えても変えられません。
- 対象は、元の点入力、全可視候補が一つ、実 int 行、空 where・出力、元 variant 根に保持済みの同名自己 join 行がある範囲です。現行の元構文の `SourceHead` では、この原式を読むために実 join 行が必要です。自己 join が型の適合モデル・raw alias・構造観測・K2 と実の根検査を変えないことは別証明済み。実行時に元 State へ行を足していません。この行を持たない実例も型には適合しますが、固定の元構文の導出がなく、現行 checker は false です。
- 単独の実例で選択が true、同じ State に実適合モデルがあり、全適合モデルで固定の辞書と元の報告を検証しました。raw 根 K2 は従来の拒否を優先、旧入口は不変です。元順を替えた正例、偽の二 arm、同じ int 型の別位置、別タグ、元の join 行なし、fallback のみの role を対照検査しました。ground 候補の追加は、どちらの順でもこの分岐では未対応です（C09 の曖昧性は判定しません）。checker の false は言語の拒否ではありません。

## 検証と公開範囲

- [固定実装](https://github.com/momota1029/yulang/tree/469bce31ca2b00cd6ce5bfc0cdd4383736df0fca/lean)（Lean tree `d25f04c174965a212b0b9f84308c82f92e0412f3`）。固定コミットの Git 実バイトを SHA と照合して別ディレクトリに復元。Lean 4.35.0、`--trust=0 -DwarningAsError=true` で C416 10 モジュール＋独立監査 4 本、C415+C416 21 モジュール＋独立監査 10 本を再生、両方 exit 0。C416 39 宣言の独立監査は公理依存なし、または標準の `propext`、`Classical.choice`、`Quot.sound` のみ。
- C408 を基準に C409–C416 の公開範囲 68 モジュール・独立監査 45 本を別に厳密再生し exit 0。最新入口のローカル結合試験は旧例を含む 11 正例 true・6 対照 false。同じ例の元行・binder 順と宣言位置を組み合わせた 24 件では元 payload を保持し、誤った単一添字 25 件はすべて false。別 arm の値が同じになる実適合モデルも作り、型の一致では別名を捕捉できないことを確認しました。いずれも全体ビルドではありません。
- `work/dots-main` のみ。C415 `f828406c9ca864016153ff324c2b065e8ab611fe` から 20 パス（ソース 10、独立監査 4、追記のみの import barrel、設計記録 3、心拍、報告）。凍結二ファイルは内容を読まず blob ID を照合、I-65 固定声明・型を変更していません。全体ビルド・Rust・パーサ・一般完全性・停止性は対象外。
- 最終確認時の `integration/m1-final` は `efb4a2de77af97ac26192fc5abfe651ef3e982f9`、`integration/types` は `1b9361bb6dfca0642ee7d7e149e2e224bff535c0`、I-74 を含む Inbox は `b99a214965f1e236ab62e6cffa13b77b617543cb`。C415 までの Lean tree の完全一致を確認済みです。C416 の実装はこの報告時点では work/dots-main です。
- [検証表](../design/dots-cycle-416-c08-verification.md)・[残行一覧](../design/dots-cycle-416-c-coverage.md)。次は C09 / X6 後半。

- 最終照合開始 `2026-11-25T12:22:20.310Z`（50 分経過）。

**C の残り: 14 行（C09–C22）。**
