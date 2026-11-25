この周に閉じた C の行: C10（`dictionary_sound_R10`、`RigidRival418.check_sound`）。同じ元の `R :{tick int}` に対する二つの実可視候補を調べ、`str` を要求する候補を型の根拠で除き、plain 合流の宣言だけを選びます。

## 実装と証明

- [仕様 6.2](https://github.com/momota1029/yulang/blob/2d470a6a0f6dace69f35b878010726a9cdd6711f/spec/06-roles.md#L51-L76) の非重複なら共存する場合。掲載の `Display (list 'a)` と `Display (list int)` 自体は重なり得るので、不一致としていません。今回の具体化は `R :{tick 'a,tick 'b}` と `R :{tick str}` のみ。どちらの順でも、元の int payload の全体を plain 側の二 binder に捕捉して、その実宣言を選びます。
- 型資料の根拠は実 payload と同じ番地にある元 int 観測と、その実 rival をコンパイルした str です。単に read が失敗したから除くのではありません。任意の fitting model で variant 全体が str head の部分型でないことを証明。生の rival 行があると構文上の head が作れる条件まで特定し、元の型資料の独立したチェックとは別にその矛盾を除きます。この検査範囲で rival の `SourceHead` がないことはモデルなしでも示しました。
- 根と実際に入る payload の生 K2 を先に検査し、入らない実ループは妨げません。元の C09 の本物の重複は「曖昧」のまま。R10 の追加はこの選択規則だけで、既存の入口を変更せず、元の実 State・Request と同じ State の全 fitting model の `check_sound` を保持します。旧資格だけを使う有限導出は、where 子や完了 producer も含め、元の書き込みのまま R9 に戻せます。

## 検証

- 固定技術版 `c69cc84bcfdb818a81d0a9fbc2fb1b11de2eaa6e`、Lean tree `337d03eaeb8037b3e76c2a92ac4302b2c3a936fa`。[手順と対照](../design/dots-cycle-418-c10-verification.md)。公式 Lean 4.35.0 の `--trust=0 -DwarningAsError=true` で独立 **10 source / 3 audit**、C417 合同 **20 / 7**、C409–418 の scoped 連鎖 **88 / 52** を正確な Git blob から再検査。すべて exit 0、42 個の追加監査は標準公理のみ。
- 追加モジュールは Source・Rule・Replay・Report・Entry・Priority・NoHead・Locator・ModelFree・Restriction、監査は Core・Spec・Boundary。barrel に十 import を追加しただけ。凍結二パスは内容を開かず blob ID を確認し、report/heartbeat まで含め対象全 **19 パス**を照合しました。
- 両宣言順と両順ごとの六つの元行順、偽書き込み・同型の別 slot・生の矛盾・候補の真の重複・根/実到達点 K2 の対照を通しました。同じ宣言キーの型を変える対照では選択と曖昧を区別。旧入口込みの 27 分岐と 32,768 番地の対照、到達外に実再帰がある fitting model での辞書も確認しました。
- 最終確認時の `integration/m1-final` は `2d470a6a0f6dace69f35b878010726a9cdd6711f`、`integration/types` は `1b9361bb6dfca0642ee7d7e149e2e224bff535c0`、I-74 の Inbox は `b99a214965f1e236ab62e6cffa13b77b617543cb`。C417 までの exact Lean tree 一致を確認しました。C418 の実装はこの報告時点では work/dots-main です。

## 範囲・次回

- 実一点の同一タグ、実可視二候補、元 int と自己 join の行を保持、where と関連出力なし。検査器は元行を作りません。範囲外の false は言語の拒否ではありません。全リポジトリビルド、Rust、solver の完全性・停止性は実行・主張していません。質問なし。利用量の枠は不明です。
- 次は C11。実入力がある associated type で、元の型つき RHS を同じ出現・元宣言・出力番号・固定先へ結びます。`Index str int` の例の `char` は現在の `Inference.Base` にないため、型を置き換えたり空入力の既存部品を完了と数えたりせず、仕様にある対応可能な元の例を選びます。

- 最終照合開始 `2026-11-25T14:21:54.173Z`（50 分経過）。

**C の残り: 12 行（C11–C22）。** [一覧](../design/dots-cycle-418-c-coverage.md)
