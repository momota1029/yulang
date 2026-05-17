# 現在のタスク: post-core roadmap

Yulang は、"この言語は成立するか" から "実用的な scripting language になれるか" へ
進むだけの core language / runtime 機能を持ち始めた。

現在の作業は、主に 4 つの track と横断的な継続作業で整理する。

広い backlog:

- `notes/todo/index.md`

完了履歴:

- `tasks/done/2026-05-14-native-backend-history.md` — Track 1 のここまでのマイルストーン
- `tasks/done/2026-05-14-host-filesystem-history.md` — Track 3 の parser/lowering 特例削減

## Track 1: Native Backend

native backend は、experimental release に向けた gate を切る段階に入った。
ここでいう release は「interpreter を置き換える」ではなく、`yulang run --native`
を明示的な subset 付きの実験的実行系として外へ出せる状態を指す。

設計参照:

- `notes/design/native-backend-plan.md`
- `notes/design/cps-effect-lowering-plan.md`
- `notes/design/native-value-abi-plan.md`
- `notes/design/native-cps-mainline-plan.md`
- `notes/design/native-direct-style-islands.md`
- `notes/design/source-realm-band-plan.md`
- `docs/native-backend.md`

方針:

- native 実行の本線は effects backend（内部実装は CPS representation）に寄せる。
- user-facing な実行入口は `yulang run --native` とする。将来的に native が標準に
  なったら、interpreter は `yulang run --interpreter` 側へ寄せる。
- フル機能の native 化は、CPS を遅い実行方式として固定するのではなく、
  effect-aware CPS IR を最適化してから Cranelift の JIT / object / executable
  へ落とす形に寄せる。
- 最適化の中心は known continuation の direct jump 化、administrative
  continuation / thunk の除去、effect evidence による handler / delimiter
  frame の静的消去、非 escape closure / continuation / thunk の stack / SSA 化、
  pure な CPS continuation subgraph の direct-style / SSA island 化、
  call-site の型 / effect / handler evidence が具体化した高階制御 pattern の
  specialization とする。std の loop / fold / nondet helper / handler wrapper は
  代表的な hot path だが、optimizer は std module path や関数名に依存しない。
- pure-subset backend は effect-free speed-checking path と boxed `VmValue`
  helper の供給元として扱う。
- `select_native_backends` は pure-subset coverage と structured unsupported reason
  のために残し、user-facing な native run は effects executable path を本線にする。
- VM / interpreter は behavioral oracle のままにする。native code は置き換えではなく、
  VM の横にある明示 opt-in backend。

現在の実装:

- `yulang run --native` と `yulang native` は effects backend へ入る。
- CPS repr Cranelift は `RuntimeValuePtr` / `ClosurePtr` / `ThunkPtr` /
  resumption pointer を ABI lane として持ち、handler / resumption payload に
  non-scalar value を通せる。
- tuple / record / variant / list / string / boxed scalar / closure / thunk /
  resumption の prototype heap handle は effects path で表示・選択・呼び出しの
  regression がある。
- source-defined algebraic effects、multi-shot resumption、`std::undet`、
  `std::junction`、mutable refs、finite/open range `for` + `last` / `next`、
  `sub` / `return` は covered source regression で native と VM を比較している。
- recursive handler / resumption chain が tuple を返す場合、handler arm の
  thunk result は `apply_closure` / direct-call reification 後にも force され、
  block tail の scoped abort は loop boundary で消費される。`5` だけが漏れる
  症状と pointer-looking integer leak は解消済み。
- native root pretty print は runtime-shaped roots の Debug projection へ寄せた。
  unit / bool / tuple 内 unit も covered path では interpreter 表示と揃う。
- CPS optimizer は bounded fixpoint で forwarding continuation、空 returner、
  literal bool branch、known closure apply、small pure direct callee、dead pure
  value statement、unreachable continuation を消す。pure successor continuation を
  Cranelift block に吸う direct-style island codegen の入口もある。
- pure-subset backend は effect-free speed check / boxed `VmValue` helper /
  backend debugging path として残る。

release gate:

- `RUSTC_WRAPPER= cargo test -q -p yulang-native`
- `RUSTC_WRAPPER= cargo test -q -p yulang --test native_cli`
- `RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_undet_once_open_range_guard_through_cps_repr`
- `RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_junction_method_undet_once_through_cps_repr`
- `RUSTC_WRAPPER= cargo run -q -p yulang -- run --native --print-roots examples/03_for_last.yu`
- `RUSTC_WRAPPER= cargo run -q -p yulang -- run --native --print-roots examples/04_sub_return.yu`
- `RUSTC_WRAPPER= cargo run -q -p yulang -- run --native --print-roots examples/06_undet_once.yu`
- `RUSTC_WRAPPER= cargo run -q -p yulang -- run --native --print-roots examples/07_junction.yu`
- `RUSTC_WRAPPER= cargo run -q -p yulang -- run --native --print-roots examples/10_effect_handler.yu`
- `RUSTC_WRAPPER= cargo run -q -p yulang -- run --native --print-roots examples/showcase.yu`

2026-05-18 時点の gate 状態:

- `yulang-native` と `yulang --test native_cli` は通る。
- `runs_undet_once_open_range_guard_through_cps_repr` は `:just 3` に届く。
- `runs_junction_method_undet_once_through_cps_repr` は `:just 18` に届く。
- CLI smoke でも `examples/06_undet_once.yu` は `just (3, 4, 5)`、
  `examples/showcase.yu` の final root は `just 18` で VM と一致する。
- native release gate は、documented experimental subset について通過。

release 後に残すもの:

- 一般的な returned/stored effectful thunk coverage。
- prototype heap handle から安定 native runtime layout への移行。
- unsupported native root を VM へ戻す fallback policy。
- package/cache/build workflow と native artifact lifecycle。
- 型 surface / monomorphize strictness。これは native release blocker ではなく、
  Track 4 側の処理系健全性作業として進める。

近い形:

```text
runtime/core IR
  -> pure debug control IR / effect-aware CPS IR
  -> closure/environment layout
  -> Cranelift IR
```

現在の距離感:

- まだ Yulang 全体を実行する処理系ではない。
- `yulang run --native` は experimental subset として外へ出せる距離にいる。
- Go module/package よりの source identity として realm / band を採用する。
  realm は versioned distribution boundary、band は realm 内の import /
  namespace / build unit。band identity は resolved realm + band path で決まる。
- source から runtime IR / effect-aware CPS / CPS repr / ABI lane / Cranelift JIT
  まで通る実行可能パスはできている。
- 当面は VM を oracle にしたまま、native 対応 root と diagnostic を増やす。

直近 TODO:

- native に残す bug / scary note を `solved` / open に仕分ける。
- native experimental release を切る直前に
  `docs/native-experimental-release.md` の release gate を再実行する。
- tag / publish 手順が必要なら、native は `experimental` と明記して出す。
- release 後は、型 surface audit と monomorphize strictness を優先 track に戻す。

これまでの主なマイルストーン (CPS lowering / CPS repr Cranelift JIT / value-lane Cranelift /
dynamic handler frame / guard stack / finite nondet など) は
`tasks/done/2026-05-14-native-backend-history.md` に退避。

## Native Release Follow-Up

`docs/native-backend.md` を public status、`tasks/current.md` を次の作業 queue とする。
細かい履歴は `tasks/done/2026-05-14-native-backend-history.md` と
`notes/progress/daily/` に寄せ、ここには release 判断に必要な項目だけ残す。

直近の順番:

1. native scary notes / bugs を open と solved に仕分ける。
2. release 直前に `docs/native-experimental-release.md` の gate を再実行する。
3. tag / publish 手順では、native は `experimental` と明記して出す。
4. その後、型 surface / monomorphize strictness の作業へ戻る。

## 重要な制約

- VM は behavioral oracle のままにする。Native code は置き換えではなく、VM の横に追加する。
- 現 VM は nondet continuation の clone cost が大きい。playground/docs examples では
  無限選択を早めに絞り、VM 参照化は native backend / control IR 作業と一緒に扱う。

## Track 2: Parser Combinators

parser combinators を Yulang 側から使える capability として実装する。

設計参照:

- `notes/design/parser-dsl-desugar.md` — `rule { ... }` / `~"..."` の desugar 方針（lower3 で展開、`~"abc": () -> [parse] ()`）

直近 TODO:

- public parser result と error type を定義する。
- minimal combinator kernel を実装する。
  - `item`
  - `satisfy`
  - `map`
  - sequencing / bind
  - choice
  - repetition
  - token/string matching
- cut / commit と error merging の挙動を決める。
- 最初の API が nontrivial なものを parse できるようになってから examples を追加する。

重要な制約:

- compiler parser はまだ書き直さない。library parser API を先に独立して試す。

## Track 3: Host / Filesystem Semantics

host capabilities、特に filesystem behavior を安定させる。

設計参照:

- `notes/design/error-handling-plan.md`
- `notes/design/std-fs.md` — std::fs 最小設計（open/close を露出せず、path + byte range で毎回読み書き。path はバイト列）

現在の実装:

- `std::console` は `print` / `println` を持つ。
- `std::fs` は暫定 native-host surface として存在する。
  - `read_text: str -> opt str`
  - `read_text_or_throw: str -> [fs_err] str`
  - `write_text: (str, str) -> bool`
  - `exists: str -> bool`
  - `is_file: str -> bool`
  - `is_dir: str -> bool`
  - `error fs_err:` prototype と手動 `Throw fs_err`
- `std::prelude` は `fail` を parser/lower 特例ではなく `prefix(fail)` operator として export する。
- 現在の `fail` は effect operation を前置で読ませる暫定 no-op。generated data-value `fail` は未実装。
- `not` は parser builtin から外し、`std::ops` の operator export として扱う。
- `return` / `last` / `next` / `redo` は parser builtin から外し、prelude の operator export として扱う。
- `+` / `-` / `*` / `/` / 比較演算子は `std::ops` に operator export を置き、lowering bridge も外した。
- `!=` は lower 特例から外し、`std::ops` の ordinary operator wrapper として扱う。
- `lazy` operator header を追加した。lazy operator は operand をすべて unit thunk として受け取る。
- `and` / `or` は lower 特例から外し、`std::ops` の `pub lazy infix` operator として扱う。
- list の末尾取得は `xs.last` を優先し、`last xs` という関数呼び出し互換は持たない。
- native CLI / basic host はこれらの request を処理する。
- wasm / playground は filesystem request を unresolved のまま残す。

直近 TODO:

- `result` の導入 / 安定化より先に error handling design を進める。
- 正確な `std::fs` API は unstable として扱う。
- API 拡張の前に error handling を決める。
  - `opt`
  - `result`
  - structured host-request errors
  - effect-style error operations
- `enum` / `error` の `from` entry で generated `Cast` を作る仕様を決める。
- `fail err` を typed error effect の user-facing surface として設計する。data constructor と same-name effect operation の文脈解決もここで固める。
- `std::undet` の branch rejection は `reject` として扱い、error の `fail` と分ける。
- `die` / `warn` / `say` の最小 std surface を決める。
- `io_err::raise` のような generated aggregation handler を、role ではなく error namespace の関数として設計する。
- parser/lowering の特例削減を続ける。
  - 残る本丸は primitive family table を persistent compiled-unit artifact metadata から渡すこと。std source へ専用 metadata を足す方向にはしない。
  - これまでの完了済み撤去項目は `tasks/done/2026-05-14-host-filesystem-history.md` に退避。
- text read/write が落ち着いた後に、最初の directory API を決める。
- browser examples を作る前に playground capability policy を決める。

重要な制約:

- native-only filesystem behavior が wasm / playground でも portable に見えないようにする。

## Track 4: Type Surface / Monomorphize Strictness

native release 後に戻る主作業。今の問題は「単一化そのもの」だけではなく、
runtime / monomorphize の出入口に残る型 surface を網羅的に置換・投影・監査できて
いないこととして扱う。

設計参照:

- `notes/bugs/type-substitute.md`
- `notes/bugs/type-monomorphize.md`
- `notes/bugs/type-monorphized-refactor.md`

方針:

- `Expr.ty` / pattern ty / binding scheme / evidence / handler residual /
  thunk effect / adapter / coercion など、runtime へ残る型 surface をまず列挙する。
- 置換、runtime projection、residual audit が同じ surface list を読む形へ寄せる。
- fallback-to-old-`expr.ty` は telemetry を通して理由付きにし、monomorphized 出口で
  strict に落とせるようにする。
- 型推論・monomorphize の途中に path / module / fixture 名依存の分岐は入れない。

直近 TODO:

- `type_surface.rs` 相当の collector / folder / audit entrypoint を足す。
- collector と substituter が同じ site set を覆う parity test を入れる。
- poison type test で `ApplyEvidence`、`HandleEffect`、`ThunkEffect`、
  `AddId.allowed`、nested pattern bind などの漏れを見つける。
- `YULANG_STRICT_MONO_RUNTIME_TYPES=1 RUSTC_WRAPPER= cargo test -q -p yulang-runtime`
  の失敗を surface site ごとに分類する。
- `substitute_type` の推移的置換、recursive binder capture、effect row matching は
  `Subst` / free-vars / row matcher の責務として切り出す。

## Ongoing: Static Analysis Speed

最近の performance work は、引き続き playground の目標と揃っている。

現在の参照:

- `notes/design/static-analysis-speed-plan.md`
- `notes/design/partial-compilation-cache-plan.md`
- `notes/bugs/type-substitute.md`
- `notes/bugs/type-monomorphize.md`
- `notes/bugs/type-monorphized-refactor.md`

現在の checkpoint:

- principal-unify は default monomorphize route。
- specialization body rewrite は queue 化され、target ごとに profile される。
- block rewrite は redundant pre-walk を避け、`showcase` の monomorphize time を大きく減らす。
- compiled-unit artifacts は syntax / namespace / typed / runtime surfaces を持つ。
- wasm は std compiled-unit artifacts を embed し、source std を fallback として使う。

次 TODO:

- Track 4 の type surface audit を先に通し、strict residual 型を見つける入口を作る。
- typed-surface import の role / impl / effect fidelity を広げる。
- compiled-unit manifest validation を厳しくする。
- persistent cache を user dependency SCCs に一般化する。
- `bench/static_analysis_bench.sh` を代表性のある benchmark として保つ。

## Ongoing: Diagnostics and Examples

言語が experimental な間は、examples を public contract として保つ。

TODO:

- playground examples を CLI からも runnable に保つ。
- feature behavior を説明できる程度に安定してから examples を追加する。
- parser / type / runtime errors の user-facing diagnostics を改善する。
- ordinary user paths で internal monomorphize / runtime errors を露出しない。

## Ongoing: Testing

Yulang code から小さい regression test を書ける形を作る。

次 TODO:

- Yulang-facing test API の最小形を決める。
- fixture 置き場と CLI runner の入口を決める。
- examples のうち重要なものを regression test に写す。
- diagnostics golden は必要な範囲だけ固定する。
