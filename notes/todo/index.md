# Yulang TODO 索引

このディレクトリは Yulang の作業バックログ。`tasks/current.md` より広い範囲を扱う。
公開後しばらくは、言語機能を広げるよりも「触った人が詰まらない」ための作業を優先する。

## 公開準備の主戦場

今やるべきことは「公開して触れる状態」を作るための順番で見る。

1. `testing.md`
   - playground で見つけた regression と最近直した effect/thunk/specialize2 境界を fixture 化する。
   - public examples を CLI / wasm / Rust test のどこで固定するか決める。
   - 以後の refactor、release、realm/band 統合の前提にする。
2. `diagnostics-docs.md`
   - parser / type / runtime error の位置と原因を分かるようにする。
   - expected / actual の出自を source range と related information で出す。
   - playground / CLI / LSP が同じ診断情報を共有する。
   - 詳細な型チェッカー計画は `type-checker-diagnostics.md` と
     `../diagnostics/type-checker-plan.md` に置く。
3. `language-server.md`
   - LSP の diagnostics、hover、related information、型表示を安定させる。
   - `yulang-editor` を playground と LS の共有 editor surface にする。
   - `.list` などの巨大型や内部 evidence が hover に漏れないようにする。
   - Zed dev extension から `yulang server` を使う導線を保つ。
4. `release.md`
   - cargo 前提の起動・配布から離れ、binary/std/playground/LS artifact を release 単位にする。
   - `yulang install std`、cache 互換、Zed/LS binary discovery を release smoke として固定する。
5. `static-analysis-speed.md`
   - playground / CLI の初回 latency と warmed latency を見える形にする。
   - compiled-unit cache を std 専用特例ではなく source dependency surface として育てる。
   - realm/band と source dependency SCC を cache unit として扱う。
   - type surface audit と cache validation が hot path を壊さないようにする。
6. `yumark.md`
   - syntax parse 済みの Yumark を value model、lowering、runtime、表示へ接続する。

この流れに効く作業だけを直近の `tasks/current.md` に移す。

## 保留中のトラック

次は重要だが、公開直後の主戦場ではない。主戦場を進めるために必要になった時だけ戻す。

- `testing.md`
  - diagnostics / runtime / VM compare の fixture 化。
  - 公開 example を regression に写す。
- `language-surface.md`
  - `error` sugar、`result`、casts、optional records、references。
  - 今は diagnostics / LS / runtime surface を詰めるために必要な範囲だけ扱う。
- `host-filesystem.md`
  - host capability と filesystem API。
  - `error` と diagnostics の語彙が固まってから public contract を決める。
- `parser-combinators.md`
  - parser combinator API。
  - error handling と parser diagnostics が安定するまで広げない。
- `native-backend.md`
  - 2026-05-25 に active workspace から外れた archived track。
  - 将来の execution backend を再開する場合は、VM/runtime semantics と
    type surface audit が落ち着いてから新しい track として切る。

## 近い優先順位

1. playground regression と recently-fixed bug を小さい fixture に落とす。
2. `yulang-editor` の token classification / diagnostics / hover を playground と LS の共有面にする。
3. cargo を介さない release smoke を作る。
4. realm/band と compiled-unit cache の実装単位を `sources` / CLI / cache manifest に接続する。
5. phase timing と counters を入れ、intern / cache / Rowan cost の順に測る。
6. Yumark の value model を決め、syntax から runtime までの最初の thin path を作る。

## 運用ルール

- `tasks/current.md` は短く、実行寄りに保つ。
- 大きめの保留案はこのディレクトリに置く。
- TODO ファイルには設計全体を重複させず、design note へのリンクを置く。
- TODO が実装作業になったら、具体的な次の一手を `tasks/current.md` に移す。
- 直近の作業が 3 本柱から外れる時は、なぜ今必要かを TODO 側に一文で残す。
