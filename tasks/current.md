# 現在のタスク: yulang2 — spec 駆動の推論パイプライン再実装

2026-06-08 ごろから、主戦場は新世代パイプラインの実装に移った。
旧 `yulang-*` pipeline は行き当たりばったりに決まった実装が多く、納得のいく土台に
なっていなかったため、仕様を `spec/` に先に固めてから書き直している。

- 新世代: `crates/sources` → `crates/infer` → `crates/poly`、入口は `crates/yulang2`
  - `sources`: ファイル収集と CST 入力
  - `infer`: CST から poly IR と型情報を作る作業 crate（推論中に増える状態はここ）
  - `poly`: 最終的に読まれる構造と解決結果だけを持つ
  - `yulang2`: 薄い CLI（`dump-poly <path>` / `dump-poly-std <path>`）
- 旧世代: `yulang` CLI にぶら下がる `yulang-*` 群。**動く oracle として保守**。
  infer は 2026-06-07 に全テスト解決済み。新世代の都合で改造・削除しない。

作業規約は `/.rules`（= `AGENTS.md`）と `crates/.rules` を見る。
旧実装は仕様ではない。挙動が食い違ったら spec と手計算で正解を確かめる。

## 仕様（実装の根拠）

- `spec/2026-05-31-effect-variable-subtractable.md` — stack 重みによる effect subtraction
- `spec/2026-06-02-role-system.md` — role 制約と discharge
- `spec/2026-06-04-method-selection.md` — ドット選択
- `spec/2026-06-06-invariant-type-sandwich.md` — 不変型と sandwich
- `spec/2026-06-06-syntax-design.md` — 表面構文（parser 実装から抽出）
- `spec/2026-06-07-principal-monomorphization.md`

spec に無い判断をしたら、コードでなく spec か `notes/design/` に追記する。

## 現在地（2026-06-12）

型推論が通るか通らないか、というところ。直近で入ったもの:

- stack-weight effect subtraction（floor 正規化、`pop(u32::MAX)` 番兵、residual の
  hash-cons、self skeleton、注釈付き local effect の `LocalEffect::Stack` view）
- role 述語の compact simplification への取り込み、impl method の role demand 解決
- std-free smoke tests（inference / handler / handled effect call）
- yulang2 dump での act operation の型付け

既知の残り（メモリ・daily note より）:

- role 偽サイクル修正の残差: simplify 側の変数マージ
  （タプル impl の 3-var union、`list int` の Eq）
- 旧世代側で「なんか重くなる」系の退行を並行追跡中
  （monomorphize / runtime-lower。コンパイル時か実行時かは未切り分け）

## 確認の回し方

- `cargo test -q -p infer` / `-p poly` / `-p sources` / `-p yulang2`
- `cargo build -q -p yulang2 && timeout 60s ./target/debug/yulang2 dump-poly-std examples/showcase.yu`
- 全 stash した素の base で workspace 全体の `cargo test` を回さない
- 日々の作業ログは `notes/progress/daily/YYYY-MM-DD.md`

## 次にやること

1. 型推論を最後まで通す（dump-poly-std が examples / lib/std で型エラー 0 になるまで）。
2. ビルドスクリプトを作る（未着手）。
3. 旧 infer のテスト群を新世代へ移植し、oracle と突き合わせる。
4. その先で旧世代の monomorphize / VM との接続を考える。

## 守る不変条件（旧 roadmap から引き継ぎ）

- 型が決まらないから Top 相当へ逃がす処理は入れない。
- path / module / fixture 名の文字列比較で型を決めない。
- 再現ケースだけを通す局所分岐ではなく、一般規則として説明できる修正にする。
- infer に不動点計算のような重たい反復を足さない。まず一回の線形パスで設計する。
- テスト期待値を実装出力に合わせて書き換えない。

## 外側の予定

- 相談先の先生への研究相談（effect row subtraction の切り出し）は、
  **実装完了＋型エラー 0 になってから**送る。素材は `notes/effect-inference-overview.md`。
- 2026 年 7 月以降は忙しくなる予定。12 月のアドベントカレンダーが公開目標。

## 旧 roadmap

2026-05-25 起点の post-native roadmap（monomorphize / runtime type surface、
static analysis speed、parser combinators、host IO、native backend の退役整理）は
`tasks/done/2026-05-25-post-native-roadmap.md` へ退避した。
そこに残る TODO は、新世代が旧世代の領分へ届いた時点で必要なものだけ拾い直す。
