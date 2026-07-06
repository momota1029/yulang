# Yulang TODO 索引

このディレクトリは Yulang の作業バックログ。`tasks/current.md` より広い範囲を扱う。
公開後しばらくは、言語機能を広げるよりも「触った人が詰まらない」ための作業を優先する。

## 公開準備の主戦場

今やるべきことは「公開して触れる状態」を作るための順番で見る。

### 次の contract slice

- `contract-v1-file-resource-priority.md`
  - Contract v0 は `stable-core` として閉じたため、次の完成線は
    **Contract v1: File / Host Resource Contract** とする。
  - file resource の mock / native / unsupported host contract を先に閉じ、
    host act FFI、diagnostics parity、release artifact、server in-process driver へ進む。

### 既存の公開準備 track

0. `yulang-hardening-phase.md`
   - 2026-06-23 の `ref.update` / directed stack weight 修正を境に、しばらくは新機能より solver hardening を優先する。
   - invariant doc、public signature golden test、opt-in metrics、stable/nightly playground 運用を同じ流れで扱う。
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
6. `performance-localization.md`
   - 高速化を「意味論税の局所化」として整理する。
   - release gate、compiled-unit cache、generalize restart、runtime ScopeState、
     replay frontier、direct-style island の順番と撤退条件を固定する。
7. `yumark.md`
   - syntax parse 済みの Yumark を value model、lowering、runtime、表示へ接続する。
8. `research-consultation.md`
   - Yulang の型推論・effect system を研究相談へ持っていくための短い資料、メール、実例を整理する。
   - 現在の入口は `notes/research/consultation/`。

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
- `ffi.md`
  - Yulang にはまだ FFI がない。遅い言語の escape hatch として将来必須だが、
    まず host capability / effect boundary として設計し、native ABI 直結は後段にする。
- `parser-combinators.md`
  - parser combinator API。
  - error handling と parser diagnostics が安定するまで広げない。
- `research-consultation.md`
  - 研究相談向けのメール・短い技術資料・what-is-new を整える。
  - 公開準備の外側だが、solver hardening の理論的位置づけを言語化するために近い。

## 置き土産トラック（2026-07-02、Claude Fable 5 評価より）

出典は `notes/design/2026-07-02-parting-assessment.md`（ユーザ承認済み）。
それぞれ独立の TODO ファイルに詳細がある。**時間制約があるのは最初の二つ**——
FFI registry / serve の実装より前に設計を確定しないと後付けが高くつく。

- `record-replay.md` — 決定的記録再生。**registry manifest に operation 列番号と
  分岐 id を最初から入れる**（実装は後でよいが、識別子設計は registry と同時）。
  2026-07-03 時点で、compiler-produced host manifest の
  `hash` / `column` / `symbol` と、Evidence VM scheduler の
  branch-local operation instance id / child spawn lineage は固定済み。
  record / replay 実行モード、記録ファイル、replay host は未着手。
- `structured-concurrency.md` — accept 分岐のキャンセルと死の規則。
  **serve 実装（FFI 指示書 実装順 5）より前に決定文書を書く**。
- `case-exhaustiveness.md` — 保守的な網羅性検査。前段の「未知 constructor 診断」
  は type-checker-diagnostics に合流させてよい。
- `deriving.md` — with: ブロックの derive。io 仕様の Wire が死文化する前に。
- `property-testing.md` — undet を探索器にした property testing。
  1〜3 slice は std だけで書けるはず（dogfooding 価値あり）。
- `effect-trace.md` — effect-aware エラートレース。diagnostics-docs と同じ流れで。
- `deterministic-parallelism.md` — 地平線トラック。実装は急がないが、
  「Yulang の並列は決定的」という定理は研究相談・公開文書で今すぐ使える。
  他の全 TODO への制約（定理の前提を崩す機能を足さない）としても働く。

## 退避済み track

- `archive/notes/todo/native-backend.md`
  - 2026-05-25 に active workspace から外れた native backend track。
  - 将来の execution backend を再開する場合は、この旧 TODO を戻さず、新しい track として切る。

## 近い優先順位

1. `yulang-editor` の diagnostics / hover を playground と LS の共有面にする（token classification は共有済み）。
2. Rowan cost の counter を追加し、intern cost の計測を設計段階から実装に進める（cache 側の timing は実装済み）。
3. Yumark の value model を決め、syntax から runtime までの最初の thin path を作る。

## 運用ルール

- `tasks/current.md` は短く、実行寄りに保つ。
- 大きめの保留案はこのディレクトリに置く。
- TODO ファイルには設計全体を重複させず、design note へのリンクを置く。
- TODO が実装作業になったら、具体的な次の一手を `tasks/current.md` に移す。
- 直近の作業が 3 本柱から外れる時は、なぜ今必要かを TODO 側に一文で残す。
