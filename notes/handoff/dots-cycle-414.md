この周に閉じた C の行: C06 / X4 前半。元の `R {x:int,..'a}` で tail が本当に未解決なら、候補を落とさず保留します（`dictionary_sound_R6`、`OpenTail414.check_sound`）。

## 実装と証明

- [仕様 6.3 の X4](https://github.com/momota1029/yulang/blob/87a10414e952d07b61376aa8b0c6dc45df54cfaf/spec/06-roles.md#L106-L109) の前半だけを扱いました。元の点要求と、著者が書いた open record の根・`x:int` の行・未束縛の tail slot を確認し、著者による role 行とその表の整合性をチェックし、全可視候補が `impl R {x:int,..'a} where 'a:R` 一つであることを読み戻します。tail の出現名と宣言の binder 名は別です。保留は読取り失敗ではなく、実際の出現と普通の行・alias・区間・origin・native 行・route の不在から導きます。ここでは二つの普通行だけ、単一の点引数、where 一つ、出力なしに限ります。
- R5 の選択を変えず、新規局所規則は `other .pending []` だけです。R6 の `DictionarySound` と、同じ State・同じ固定 `DictionaryEvidence` の `check_sound` を証明しました。新しい実行入口は証人の添字や根 K2 検査用データから実情報を照合し、木も最終結果も pending、書込みなしという正確な結果だけを確認します。以前の分岐は委譲し、既存の成功した選択木、where 順、書込みは R5 と同じです。
- 保留中の新規 where 子生成はありません。元の where は、書かれた正規化済みの head より小さいことを確認しましたが、任意の tail 代入による縮約や選択は行いません。実際に決まった record の引き算と残部の捕捉は C07 に残しています。
- 実 X4 は保留。異なる証人でも元の出現・宣言・節・field・tail を付け替えられません。元の同じ State は、空 tail と、観測上異なる（別 field を持つ）tail の両方に適合し、同じ保留の証拠を持ちます。同じ State の完了済み出力をこの tail に向けても、取り出せるのは同じ tail の変数参照だけで、残部を新たに決める根拠にはならないことも証明しました。実行対照では既知 tail・alias・区間・元の tail 定義・別の候補や where・実 role 宣言がなく fallback arity だけの入力・非点引数・出力要求は新分岐で false。実際の raw 根 K2 は従来の分岐で拒否が確認でき、新分岐は false（実行値 `[true, false, true]`）。これらの false 自体は言語の拒否を意味しません。

## 検証と公開範囲

- [厳密検証コードの固定ピン](https://github.com/momota1029/yulang/tree/7e65e94347471a35428fa91c7a31d1f3c7d9052c/lean)（Lean tree `0baabd2e36fb2ed89017867219848a6a9c28ee97`）。Lean 4.35.0、固定コミットの実ファイルを SHA と照合した別ディレクトリで `--trust=0 -DwarningAsError=true`。C414 の 11 モジュールと独立監査 7 本、および C413+C414 の 22 モジュールと独立監査 15 本を再生し、双方終了コード 0。C408 を基準に C409–C414 の公開範囲 47 モジュール・独立監査 35 本も別に再生し、終了コード 0。新しい公開入口で旧例も含めた結合試験は 8 正例 true・2 対照 false。C414 の 49 の宣言の監査依存は標準の `propext`、`Classical.choice`、`Quot.sound` の範囲。未証明の宣言や新規公理なし。
- 変更は `work/dots-main` のみ、C413 完了点 `c0d196062f79a96dcf6ff2a39c005a0bc31c2c66` から 24 パス（ソース 11、独立監査 7、追記のみの barrel、設計記録 3、心拍、本報告）。I-57 の二ファイルは内容を読まず blob ID の一致のみ確認、I-65 の固定声明・定義は不変。全体ビルド、Rust／パーサ、一般の完全性・停止性は未検証・対象外。
- 最終確認時の `integration/m1-final` は `87a10414e952d07b61376aa8b0c6dc45df54cfaf`、`integration/types` は `1b9361bb6dfca0642ee7d7e149e2e224bff535c0`、I-74 を含む Inbox は `b99a214965f1e236ab62e6cffa13b77b617543cb`。C413 までの Lean tree の完全一致を確認済みです。C414 の実装はこの報告時点では work/dots-main です。
- [C06 の検証表](../design/dots-cycle-414-c06-verification.md)・[残行一覧](../design/dots-cycle-414-c-coverage.md)。次は C07 / X4 後半。

- 最終照合開始 `2026-11-25T10:21:35.051Z`（50 分経過）。

**C の残り: 16 行（C07–C22）。**
