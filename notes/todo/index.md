# Yulang TODO 索引

このディレクトリは Yulang の作業バックログ。`tasks/current.md` より広い範囲を扱う。
公開後しばらくは、言語機能を広げるよりも「触った人が詰まらない」ための作業を優先する。

## 公開後の主戦場

今やるべきことは 3 本に絞る。

1. `diagnostics-docs.md`
   - parser / type / runtime error の位置と原因を分かるようにする。
   - expected / actual の出自を source range と related information で出す。
   - playground / CLI / LSP が同じ診断情報を共有する。
2. `language-server.md`
   - LSP の diagnostics、hover、related information、型表示を安定させる。
   - `.list` などの巨大型や内部 evidence が hover に漏れないようにする。
   - Zed dev extension から `yulang server` を使う導線を保つ。
3. `native-backend.md`
   - VM を oracle にしたまま native 対応範囲を増やす。
   - value-lane / CPS repr / effectful control の差を小さくする。
   - README の Native Backend Progress と実装状態を一致させる。

この 3 本に効く作業だけを直近の `tasks/current.md` に移す。

## 保留中のトラック

次は重要だが、公開直後の主戦場ではない。主戦場を進めるために必要になった時だけ戻す。

- `testing.md`
  - diagnostics / runtime / native compare の fixture 化。
  - 公開 example を regression に写す。
- `static-analysis-speed.md`
  - playground latency、compiled-unit cache、phase timings。
  - 診断や evidence を増やす時の hot path 防衛。
- `language-surface.md`
  - `error` sugar、`result`、casts、optional records、references。
  - 今は diagnostics / LS / native を詰めるために必要な範囲だけ扱う。
- `host-filesystem.md`
  - host capability と filesystem API。
  - `error` と diagnostics の語彙が固まってから public contract を決める。
- `parser-combinators.md`
  - parser combinator API。
  - error handling と parser diagnostics が安定するまで広げない。

## 近い優先順位

1. LSP に出るエラーの range / related information / hover を実用水準にする。
2. 型エラーの expected / actual それぞれに出自を持たせる。
3. hover の型表示を public projection として安定させる。
4. native の value-lane と CPS repr Cranelift の未対応差分を小さい VM compare で潰す。
5. 上の作業を支える fixture と README / docs を足す。

## 運用ルール

- `tasks/current.md` は短く、実行寄りに保つ。
- 大きめの保留案はこのディレクトリに置く。
- TODO ファイルには設計全体を重複させず、design note へのリンクを置く。
- TODO が実装作業になったら、具体的な次の一手を `tasks/current.md` に移す。
- 直近の作業が 3 本柱から外れる時は、なぜ今必要かを TODO 側に一文で残す。
