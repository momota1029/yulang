# effect-aware エラートレース TODO

出典: notes/design/2026-07-02-parting-assessment.md §6（Claude Fable 5、ユーザ承認済み）。
関連: notes/todo/diagnostics-docs.md、notes/todo/type-checker-diagnostics.md。

## 問題

継続ベースの VM では、素朴なスタックトレースが論理的な呼び出し構造と
一致せず、エラー時の表示が意味不明になる。エラーが複数の handler を越え、
undet / accept の分岐の中で起きたとき、ユーザに必要なのは:

```text
error: io_err::not_found "config.toml"
  performed at: examples/app.yu:12  (file::load)
  under handlers: [mock_fs @ test.yu:4, logger @ app.yu:3]
  branch: undet #2 of 5 (opened at app.yu:8)
```

つまり「**どの operation が・どの handler 群の下で・どの分岐で**」の三点。

## 鍵となる事実

evidence VM はこの情報を**実行時に既に持っている**:

- marker / AddId が handler の系譜を追跡している（hygiene 機構）
- provider env が「いまどの能力の下にいるか」を持っている
- source range は poly / lowering が保持している（LSP hover が既に使う経路）

欠けているのは解析ではなく **diagnostics 表面への配線**だけ。
新しい追跡機構を足す話ではない。

## 方針

1. エラー（未 catch の error effect / trap / capability failure）の表面化時に、
   その時点の marker 系譜 + provider env + 分岐 id を「effect trace」として
   構造化して吐く。
2. 表示は diagnostics 側の責務（.rules: 主処理で表示文字列を組み立てない）。
   runtime は構造化データを返し、CLI / LSP / playground が同じものを描画する。
3. **通常実行のコストをゼロに保つ**: トレースはエラー表面化時に
   その場の継続・handler 状態から構築する（常時記録しない）。
   継続木に情報が既にあるから、これは可能なはず。
   常時記録が必要になる粒度（「エラーの 3 perform 前に何をしていたか」）は
   record/replay（notes/todo/record-replay.md）の領分に送る。
4. 分岐 id は structured-concurrency / record-replay と同じ識別子空間を使う。

## First slice

1. 未 catch error effect の表面化時に「performed at + handler 系譜」を出す
   （分岐 id は後回し）。
2. capability failure（host act 未登録）に同じ形を適用する
   （FFI 実装と同時期にやると一貫する）。
3. LSP diagnostics の related information に handler 系譜を載せる。
4. 分岐 id の表示（scheduler 実装後）。

## 完了条件

- 3 段の handler を越えるエラーの fixture で、performed 位置と handler 系譜が
  正しく表示される。
- 通常実行（エラーなし）の代表ワークロードが計測誤差内で不変。
- CLI / playground / LSP が同じ構造化データを共有している。

## やってはいけないこと

- 常時トレース記録を hot path に乗せること。
- runtime 内で表示文言を組み立てること。
- Rust の backtrace をそのまま見せること（ユーザの世界の語彙で出す）。
