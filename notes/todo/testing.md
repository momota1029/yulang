# Testing TODO

目的: Yulang の言語機能、標準ライブラリ、host capability を小さな単位で確かめられるようにする。
Rust 側の regression test だけでなく、Yulang code から自然に書ける test 体験も育てる。

## 目標の形

```text
Yulang test file
  -> compile / infer / run
  -> assertion result
  -> compact diagnostics
```

## 最初の設計上の問い

- test は通常の Yulang program として書くか、専用 syntax を足すか。
- assertion failure は value-level result、error effect、trap、test runner 専用診断のどれにするか。
- type error / parser error / runtime error を expected failure としてどう書くか。
- CLI、wasm playground、Rust fixture test のどこまで同じ test file を共有するか。
- examples をそのまま regression test にするか、test 用 entrypoint を別に持つか。

## 最小 API 候補

- `assert: bool -> unit`
- `assert_eq`
- `assert_some`
- `assert_none`
- `fail_test: str -> unit` など、typed error `fail err` と衝突しない名前
- test case を名前付きで集める仕組み

## Fixture と golden test

- `tests/yulang/cases.toml` を public contract manifest とする。runtime / diagnostics /
  runtime error / public signature / public example / standard API / release expectation の
  小さい `.yu` fixture は、可能ならここへ登録する。
- manifest case は fixture path、case kind、compact expected output、contract tags を持つ。
  現在は Rust CLI test が読む。将来の `yulang test` / playground / LSP canary も同じ
  manifest を読む前提にする。
- 未実装 API の TODO / ignored placeholder は manifest に置かない。manifest は current
  executable contract だけを表す。standard API / host capability の予定 case は、native
  host または unsupported host の public CLI behavior が観測できるまで spec / TODO に残す。
- 完全実行系の public regression は、Rust の内部 helper ではなく `yulang` CLI 起動を第一経路にする。
- CLI test は repo の `lib` を `--std-root` に渡し、isolated `YULANG_CACHE_DIR` で artifact cache の経路も見る。
- Rust の内部 helper は parser / lowering / inference の局所検査、fake std を使う型・効果 regression、
  embedded playground std route、LSP の range / hover / definition のような内部構造が必要な検査に絞る。
- 現行 CLI cache は source collection の後段にあるため、process ごとの std file read はまだ残る。
  これを消す本命は、CLI で複数 test file を一括実行する runner か、std realm / compiled-unit cache 側で扱う。
- parser / type / runtime diagnostics は、必要なものだけ compact golden として固定する。
- playground example のうち重要なものは CLI regression に写す。
- "infers but does not run" は expected limitation ではなく failure として追う。
- host capability を使う test は native-only / wasm-unsupported の区別を明示する。

## 2026-06-17 P0 regression set

playground 公開前に、最近壊れた境界を小さい fixture として固定する。

- list update:
  - `my $xs = [2 3 4]; &xs[1] = 6; $xs`
  - primitive `list` path の解決、ref_update payload union、VM boundary を同時に見る。
- nondet once triple:
  - `each 1..`, nested `each a<..`, `guard`, `.once`
  - playground std と通常 std の差、constructor display、range/int conflict を見る。
- labeled sub / callback residual:
  - `g: (int -> ['a & std::control::flow::loop::redo] any) -> ['a] int` のような上から押さえた型を再発させない。
  - `return` / `redo` / callback residual が shallow handler と同じ推論にならないことを見る。
- deep handler act method:
  - `std.control.nondet.nondet.#act-method:once` は `α [nondet; β] -> [β] opt α` 系で export される。
  - `[handled; 'e] -> ['e]` を普通の関数として forward した時に shallow handler 型へ潰れない。
- specialize2 function candidate effect variance:
  - 同じ arg/ret で `arg_effect` だけ違う関数候補。
  - 同じ arg/ret で `ret_effect` だけ違う関数候補。
  - effectful callback を pure expected へ渡すケースと、その逆。
- concrete subtype mismatch:
  - tuple length mismatch。
  - record required field missing。
  - polyvariant / enum constructor mismatch。
  - これらが coerce/runtime boundary ではなく subtype constraint として落ちること。
- optional record default:
  - `our box {width = 1, height = width} = width * height`
  - default field 間の依存が `int` 固定にならず、必要な role constraint だけ残ること。
- playground/editor surface:
  - `tok-type` / `tok-function` / `tok-property` の class drift を固定する。
  - CLI diagnostics と playground diagnostics が同じ原因を指すこと。
- public examples:
  - `examples/*.yu` のうち README に載せる run example を sweep する。
  - 初期 smoke script は `scripts/public-example-smoke.sh`。
  - console output は `stdout`、root 表示は `--print-roots` の surface として分けて見る。
  - attached impl example は type companion 内 role impl の regression として run sweep に含める。

## 最初の slice

- `tests/yulang/` のような小さい fixture 置き場を決める。
- `1 + 2`、関数呼び出し、variant、role method、effect handler の smoke test を置く。
- 上の P0 regression set から、既に Rust test helper で動かせるものを先に移す。
- `std::console` と `std::fs` は host policy が固まるまで smoke test を分ける。
- 既存 Rust test から同じ fixture を呼べるようにする。

## 2026-06-17 fixture harness first slice

- `tests/yulang/` を共有 fixture 置き場にした。
- `crates/yulang` の source route test から `tests/yulang/regressions/effect/*.yu` を読む helper を追加した。
- まずは callback residual / sub return / effectful parameter forwarding の regression を fixture 化した。
- `tests/yulang/support/fake_std/` を作り、処理系の surface path だけが必要な test は full std を読まない方針にした。
- 2026-06-21 に list update playground smoke を `tests/yulang/regressions/runtime/list_update.yu` へ移し、
  既存の playground std run / prefix comparison test から読む形にした。
- 同日、完全実行系の regression は `yulang` CLI 起動を第一経路にする方針へ切り替えた。
  list update fixture は `crates/yulang/tests/cli.rs` から `--std-root lib run --print-roots` で実行し、
  isolated cache に poly / control artifact が出ることも見る。
- 2026-07-01 に次を `tests/yulang/regressions/runtime/` へ追加し、`crates/yulang/tests/cli.rs`
  から repo `lib` std root と isolated cache で実行する CLI golden にした。
  - `nondet_once_triple.yu`
  - `optional_record_defaults.yu`
  - `attached_impl_pick.yu`
- 同日、`scripts/public-example-smoke.sh` だけに寄っていた代表 public examples の一部を、
  小さい table-driven CLI golden として Rust 側にも橋渡しした。
- 2026-07-01 後続 slice で、showcase を除く `examples/01_*.yu` から
  `examples/13_console.yu` までを Rust CLI golden に広げた。
  - `examples/13_console.yu` は `--print-roots` ではなく stdout contract として見る。
  - `examples/showcase.yu` は大きいため、shell smoke の contains check に残す。
- 2026-07-02 に public examples sweep を `tests/yulang/cases.toml` にも載せた。
  `examples/showcase.yu` は manifest でも compact contains check に留める。
  同日、重複していた Rust 側の inline public examples bridge は manifest runner へ統合した。
- 同日、`std::data::result` の `map` / `and_then` / `unwrap_or` を runtime fixture と
  public signature case の両方で manifest に載せた。standard API case は、実行挙動と
  公開型の両方が現在の public surface として観測できるものから追加する。
- 同日、`error E:` の基本 `fail (E::variant payload)` + `E::wrap` flow を
  `error_wrap_fail.yu` として manifest に載せた。`E::wrap` は runtime output と
  public signature の両方で、action 引数の effect row が保持されることを見る。
- 同日、`from` aggregation と `E::up` の最小 public flow も
  `error_from_wrap.yu` / `error_up_wrap.yu` として manifest に載せた。
  wider error の `wrap` は narrower error を `from` variant へ閉じ、
  `up` は narrower effect を wider error effect へ持ち上げる contract として見る。
- 同日、`error_display.yu` / `error_display_from_wrap.yu` を追加し、
  `error E:` から生成される `Display E` impl も public CLI manifest に載せた。
  通常 payload は variant label + payload display、unit variant は label、
  `from` variant は wrapped error の display へ委譲する contract として見る。
- 同日、`std::io::file` の native CLI host contract として、
  `read_text` / `write_text` / `exists` / `is_file` / `is_dir` を temp file
  を使う compact CLI test に載せた。これは default evidence VM 経路で
  host capability が unhandled effect にならないことを見る first slice で、
  range write、metadata、managed text ref (`open_text` / `open`)、scope-exit
  close/write-back、path payload display は後続の standard API contract として残す。
- 同日後続 slice で、`std::text::path` の byte conversion と `Display path` を
  `path_display.yu` と CLI missing-file display test に載せた。これにより
  generated `Display E` の path payload が user-facing error text まで届く。
  platform-native non-UTF-8 path behavior はまだ stable contract にしない。
- 同日後続 slice で、`std::io::file` の実行可能 first slice に対応する
  public signatures も manifest に載せた。
  - high-level: `read_at` / `write_at` / `read_text` / `write_text`
  - host predicates: `file.exists` / `file.is_file` / `file.is_dir`
  - typed failure boundary: `io_err.wrap`
- 同日後続 slice で、`open_text` / `open` / `open_in` の public signatures と
  temp file を使う CLI get/set regression も追加した。basic managed text ref
  は executable contract に入れる一方、metadata、directory listing、range
  writes、locking、explicit close / scope-exit write-back はまだ spec/TODO 側に残す。
- 同日、`tests/yulang/regressions/diagnostics/` を追加し、compact CLI diagnostics golden の
  入力を inline source から共有 fixture へ移した。
  - `type_annotation_mismatch.yu`
  - `unresolved_value_name.yu`
  - `unresolved_type_name.yu`
  - `top_level_mutable_binding.yu`
  - `unclosed_paren.yu`
- 同日後続 slice で、annotation builder が未対応の type syntax を debug dump ではなく
  compact diagnostic として出す canary を追加し、CLI / LSP / playground の
  code と range を固定した。
  - `unsupported_record_type_annotation.yu`
- 同日後続 slice で、`rule_lazy_quantifier.yu` を diagnostics fixture に追加した。
  - CLI summary、LSP diagnostic、playground diagnostic が同じ
    `yulang.unsupported-rule-lazy-quantifier` code と `*?` primary range を見る。
  - wasm playground diagnostics tests も共有 diagnostics fixture を読む形へ寄せた。
- 同日後続 slice で、`unclosed_paren.yu` を no-panic canary から parser recovery
  diagnostic canary へ強化した。
  - CLI summary、LSP diagnostic、playground diagnostic が同じ `yulang.syntax` code と
    EOF recovery range を見る。
- 同日後続 slice で、catch syntax の missing scrutinee / missing arm pattern /
  missing arm body diagnostics を primary range 付きの public contract にした。
  - CLI manifest は `catch` keyword / arm `->` range を固定する。
  - wasm playground diagnostics tests も同じ共有 fixture を読む。

## 2026-06-23 public signature golden first slice

- `crates/yulang/src/source/tests/case_02.rs` に、std public signature の canary を追加した。
- 対象:
  - `std.control.var.ref.update`
  - `std.text.parse.choice`
  - `std.control.flow.loop.for_in`
- public signature の ` = ` より左側だけを抜き出し、body 内の `#op:...` ではなく公開型そのものを検査する。
- これらの public signature では、`#...` / `AllExcept(...)` が出ないことを固定する。
- `ref.update` は、ref residual と callback residual が `['b, 'a]` として残ることも見る。

## 2026-06-23 public signature golden second slice

- std に依存しない data-position effectful function の canary を fixture 化した。
- 対象:
  - `tests/yulang/regressions/effect/data_position_effect_function_public_signature.yu`
  - `tests/yulang/regressions/effect/nested_data_position_effect_function_public_signature.yu`
- 見ている性質:
  - `box.handle` / `demo.cell.apply` の public signature に `#...` / `AllExcept(...)` が出ない。
  - handled effect family (`tick` / `pulse`) が public method signature に残らない。
  - ref residual と callback residual は `['b, 'a]` として残る。
  - nested module でも、名前や std path に依存せず同じ構造として通る。

## 2026-06-24 nested handler contract public signature canary

- `tests/yulang/regressions/effect/nested_handler_contract_public_signatures.yu` を追加した。
- 研究相談 brief / public docs の中心例を、runtime smoke だけでなく public signature として固定する。
- 対象:
  - `all_paths`
  - `total_amount`
  - explicit-contract `compose(f, g: _ -> [_] _, x: [_] _)`
- 見ている性質:
  - `all_paths` は `flip` だけを capture し、residual row を `['b] list 'a` として残す。
  - `total_amount` は `amount` だけを capture し、residual row を同じ形で残す。
  - explicit-contract `compose` は `g(x)` の surface effect を `f` に見せるため、
    public signature に `#...` / `AllExcept(...)` / `Empty` evidence を出さない。
  - test helper は module-qualified `pub "std.foo"` だけでなく、top-level `pub dN:name`
    の public signature も同じ経路で抜き出せる。

## 2026-06-24 public signature golden third slice

- `dump_public_signature_type` を追加し、公開 dump line の body を除いた型部分だけを exact に見る。
  role constraint 内の associated type equality (`item = ...`) を body delimiter と誤認しないよう、
  body は ` = e...` / ` = <missing>` で切る。
- `tests/yulang/regressions/effect/public_type_display_order_signatures.yu` を追加した。
- 対象:
  - `apply`
  - `twice`
  - `compose1(f, g: _ -> [_] _, x)`
  - `compose2(f, g, x)`
- 見ている性質:
  - 型変数名は表示上の初出順で安定する。
  - `SubtractId` は raw/global ID ではなく、その公開型内の初出順 `#0` で表示される。
  - `twice` / `compose2` の `#0[Empty]` evidence は消さずに固定する。
  - data-position / std public canary は `contains` ではなく exact public type として固定する。

## 2026-07-01 public signature golden fourth slice

- `std.control.var.ref` constructor surface を exact golden に追加した。
  - `update_effect` field が `[std::control::var::ref_update 'b; 'c] ()` として残る。
  - constructor result は `ref('a | 'c, 'b)` になり、field residual と session residual を
    public surface で失わない。
- `std.control.nondet.nondet.#act-method:once` と `#act-method:list` を exact golden に強化した。
  - `once`: `'a [std::control::nondet::nondet; 'b] -> ['b] opt 'a`
  - `list`: `'a [std::control::nondet::nondet; 'b] -> ['b] list 'a`
  - これまでの shallow collapse 否定だけでなく、deep handler の public 型全体を固定する。

## やらないこと

- 最初から property testing や snapshot 大量生成に広げない。
- diagnostics の全文を広く固定しすぎない。
- playground 専用 behavior を portable な test contract にしない。
