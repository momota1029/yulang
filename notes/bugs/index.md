# notes/bugs index (2026-05-18 native handler/display 整理後 更新)

「素直に書いたら動きそうなのに、実装上詰まった」snippet の履歴。

## 作業中メモ（2026-05-15 round-5 / 未コミット WIP）

round-5 の 5 snippet は、手元 WIP ではいったん全て期待出力まで到達した。

```text
role_method_in_for_body_pattern.yu                 -> [0] 4
handler_fn_missing_join_evidence.yu                -> [0] ["a"]
record_field_value_selection_selector_shape.yu     -> [0] true
callback_list_index_raw_type_stuck.yu              -> [0] 0
wrap_does_not_traverse_from_chain.yu               -> [0] "err: not_found"
```

ただし、この WIP は既存 VM 回帰を壊すので、まだ解決済みに移さない。

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-runtime vm_
```

で `vm_runs_std_undet_once_and_sub_return_roots` が落ちる。最小化すると
`std::undet.each` / `.once` 内の `std::range::fold` callback が絡む。

```yulang
use std::undet::*

({
    my a = each 1..
    my b = each 1..
    my c = each 1..

    guard: a <= b
    guard: b <= c
    guard: a * a + b * b == c * c

    (a, b, c)
}).once
```

現在の WIP では `principal_unify` 後に `a` / `b` / `c` が一度 `int` まで
固まるが、その後の role method selection で receiver が `Tuple([])` /
`unit` 側へ崩れ、`expected (), got int` になる。直接の失敗点は
`std::range::fold_from` / `fold_ints` の callback effect projection と、
そこから先の role receiver projection の食い違いに見える。

手元で試した方向:

- `handler_fn_missing_join_evidence` は、`handle` の join evidence が無い時だけ
  arm から消費 effect を読み、body が未精密な local value なら thunk expected
  を与えると通る。ただし広げすぎると `undet.each` の body value を `unit`
  に潰す。
- `callback_list_index_raw_type_stuck` は、list element へ function value を
  入れる時に effectful callback の境界を保持すれば通る。ただし local function
  value を wrapper 化する範囲を広げると `range.fold` の callback shape に
  干渉する。
- `principal_unify` / `types/substitution.rs` では function の `param_effect` /
  `ret_effect` を value precision ではなく effect precision で merge する必要が
  ある。片側だけ直すと `Never` が勝って `std::range::fold` の effect var が潰れる。

次に見る場所:

- `crates/yulang-runtime/src/monomorphize/pipeline/principal_unify.rs`
  - `project_closed_value_substitutions_from_type`
  - `project_closed_substitutions_from_type`
  - role impl candidate の receiver projection
- `crates/yulang-runtime/src/types/substitution.rs`
  - `merge_projected_type_precision` の function effect slots
- `crates/yulang-runtime/src/lower/lowerer.rs`
  - `Handle` lowering の missing join evidence fallback
  - local callback value の effect boundary preservation

現時点の判断:

- snippet 5件の表面だけを通す patch は作れる。
- `std::undet.each` / `.once` の既存回帰は 2026-05-15 に修正済み。
  full apply-spine の principal plan がある場合は、内側の単一 apply evidence
  由来の古い `unit` substitution で上書きしない。候補が open だけの
  `unit` substitution も concrete な根拠として扱わない。
- 次は round-5 snippet の regression test を戻して、同じ principal
  elaboration 経路で壊れないか確認する。

## 解決済み（2026-05-20 / playground sample 調査）

playground (`web/playground/src/main.ts`) にベタ書きされた 14 個の example を
`debug control-vm` と `run --interpreter` の両方で実行して調査。3 件が再現し、
commit `230e028` で全て解決した。snippet は `solved/` へ退避。

- B1 / [`solved/playground_tour_scc_type_leak.yu`](solved/playground_tour_scc_type_leak.yu)
  — tour 全体での型推論汚染（両 VM 共通）。後段 `render` の symbol variant が
  前段 `c * c` の TV へ漏れていた。tour の 5 ブロック全揃いでのみ再現。
- B2 / [`solved/control_vm_record_default_pattern_mismatch.yu`](solved/control_vm_record_default_pattern_mismatch.yu)
  — control-vm の record pattern named field default が `PatternMismatch`。
- B3 / [`solved/control_vm_once_open_range_expected_closure.yu`](solved/control_vm_once_open_range_expected_closure.yu)
  — control-vm の open-range `each` + `.once` が `ExpectedClosure(Unit)`。

修正後は 14 sample 全部が `debug control-vm` / `run --interpreter` 両方で
一致。詳細は [`solved/index.md`](solved/index.md) の 2026-05-20 エントリ参照。

副次的観察として、B1 のエラー表示で operator def 名が
`std::ops::#op:infix:==` と未短縮で出ていた。LSP の最短化と同じロジックを
diagnostic 出力（`crates/yulang-infer/src/diagnostic.rs` の format 経路）にも
当てたい、というのは別タスクとして残っている。

## 現在の未解決（2026-05-25 / YULANG_RUNTIME_FINALIZE=1 グラフ単一化）

新ランタイム `crates/yulang-runtime-finalize/` をデフォルト経路に通すと
(`YULANG_RUNTIME_FINALIZE=1`)、legacy `crates/yulang-runtime/` の
monomorphize では通る式が落ちる、もしくは出力が変わる snippet が出る。
`examples/` + `notes/bugs/` + `notes/bugs/solved/` の 80 件を両モードで
sweep して見つけたもの。

確認方法:

```bash
target/debug/yulang run --no-cache --print-roots notes/bugs/<file>.yu
YULANG_RUNTIME_FINALIZE=1 target/debug/yulang run --no-cache --print-roots notes/bugs/<file>.yu
```

### 残っている 1 件 (2026-05-25 夜 update)

現時点で未解決の YULANG_RUNTIME_FINALIZE=1 regression は無し
(2026-05-25 深夜の調査で最後の 1 件も解消、下記)。新しい regression が
出たらここへ戻す。

### 解消済み (2026-05-25 深夜, `crates/yulang-infer/src/export/principal.rs` の role-impl path seeding 修正)

「state binding を declare しただけで for の Fold::fold dispatch が漏れる」
と読めていた最後の 1 件は、実は state binding 関係なし。`for _ in [list]:`
の dead-code elim されない位置で list の Fold dispatch が落ちるのが本質
だった。

原因は `export_role_impl_graph_nodes` の def_paths seeding 順序。Fold は
`std::prelude` から `pub use` で再エクスポートされているため、
`std::list::&impl#337::fold` (canonical) と
`std::prelude::&impl#337::fold` (prelude alias) の両方が
user-observable paths に並ぶ。HashMap::collect の last-wins で
prelude path が `role_impl.members[0].value` に書き込まれていた一方、
`module.bindings` は canonical path でしか登録されていないので、finalize の
`role_method_candidates` で list の Fold impl が候補リストから消えていた。
range は HashMap の iteration order の偶然で canonical が勝っていたので
通っていた。

修正: `def_paths` を canonical paths から先に seed し、user paths と
all_binding_paths は欠落補完にだけ使う。

| 元 snippet | 状態 |
|---|---|
| [`solved/finalize_list_fold_dispatch_prelude_alias_path.yu`](solved/finalize_list_fold_dispatch_prelude_alias_path.yu) | `{ my $n = 0; for _ in [1]: 1; $n }` が finalize でも `[0] 0` |

### 解消済み (2026-05-25 夜, commit `26f50fe Fix finalize graph edge regressions` 周辺)

前 round で残った 3 件はすべて --no-cache の cold 経路で legacy と揃った:

| 元 snippet | 状態 |
|---|---|
| [`solved/finalize_handler_fn_state_leaks_effect.yu`](solved/finalize_handler_fn_state_leaks_effect.yu) | state binding + handler arm が finalize でも `[0] 1` |
| [`solved/finalize_record_default_field_show_empty_call.yu`](solved/finalize_record_default_field_show_empty_call.yu) | `f {}` で default 経由 + `.show` が finalize でも `[0] "80"` |
| [`solved/finalize_inline_wrap_conditional_fail_conflicting_bounds.yu`](solved/finalize_inline_wrap_conditional_fail_conflicting_bounds.yu) | inline `E::wrap: if cond: fail ... else: ...` が finalize でも `[0] err bad "x"` (cold 経路) |

同じ commit で、元の solved/ snippet のうち以下も追加で通るように:

- `solved/handler_fn_missing_join_evidence.yu` → `[0] ["a"]`
- `solved/record_alias_default_mix.yu` → `[0] ("x:8080", "localhost:22", "localhost:80")`

### 解消済み (2026-05-25 昼, commit `b92326e Close role associated types in runtime finalize` 周辺)

| 元 snippet | 状態 |
|---|---|
| [`solved/finalize_handler_fn_unannotated_arg_leaks_effect.yu`](solved/finalize_handler_fn_unannotated_arg_leaks_effect.yu) | handler-as-function (no state, no annot) が finalize でも `[0] ()` |
| [`solved/finalize_record_pattern_field_role_method_incomplete_graph.yu`](solved/finalize_record_pattern_field_role_method_incomplete_graph.yu) | `f { port: 8080 }` 経由で field 型が確定する形が finalize でも `[0] "8080"` |
| [`solved/finalize_callback_list_index_raw_incomplete_graph.yu`](solved/finalize_callback_list_index_raw_incomplete_graph.yu) | callback を list に入れて index_raw する形が finalize でも `[0] 0` |
| [`solved/finalize_error_wrap_fail_breaks.yu`](solved/finalize_error_wrap_fail_breaks.yu) | helper を annotate して `wrap` する形が finalize でも `[0] err not_found "missing"` |

同じ commit で、元の solved/ snippet のうち以下も追加で通るように:

- `solved/callback_list_index_raw_type_stuck.yu` → `[0] 0`
- `solved/native_error_wrap_basic_flow.yu` → `[0] ok ...` / `[1] err ...`
- `solved/wrap_does_not_traverse_from_chain.yu` → `[0] "err: not_found"`
- `solved/pattern_binding_vs_variant.yu` → `[0] "err"`

### サブ観察

- `solved/var_effect_leak_with_wildcards.yu` は `--no-cache` でも finalize
  側で **非決定的** に `ConflictingBounds` (`apply_effect#5`, `&entries#...` と
  `log str` row の衝突) を出す (連続 5 run で 2/5 が失敗、3/5 が通る)。
  fresh TypeVar ID 配置か hash-map iteration order 依存と思われる。snippet
  化はせず観察のみ残す。
- 上で解消した `solved/finalize_inline_wrap_conditional_fail_conflicting_bounds.yu`
  は warm cache 経路 (`YULANG_CACHE_DIR=...` で finalize 側だけ複数回温め
  た場合) では同じ `ConflictingBounds` が再出する場合がある。`--no-cache`
  cold 経路では通るので、これはランタイム単一化ではなくキャッシュ側の汚染。
  下の「2026-05-21 / キャッシュ汚染」と同枠。

メモ:
- 旧仮説 (state binding が for body の effect row を `&n` 行で広げて Fold
  receiver 型解決を狂わせる) は赤鯖。state は無くても `{ for _ in [1]: 1 }`
  だけで再現した。dead-code elim が効く位置 (top-level の `for ...; 0`) は
  再現しなかったので state が引き金に見えていた。
- 真因は infer の export で role_impl member path が `prelude` alias 側に
  上書きされていたこと。Fold が `pub use` で prelude に再公開されている
  role 全部が潜在的に同じ問題を抱えていたが、`module.bindings` への登録は
  常に canonical path なので、`bindings.get(member.value)` が None になる
  形で finalize 側だけが落ちていた (legacy runtime は別経路で role 解決を
  していたため見えなかった)。

## 現在の未解決（2026-05-21 / キャッシュ汚染）

`each` + role method `+` の式が、キャッシュ有無で出力がブレる。

```text
~/r/yulang> echo "([1,2].each + [1,3].each).list.say" | yulang run
error: cannot infer all runtime types needed for `std::ops::#op:infix:+`.
Add a type annotation that fixes the remaining type variable: 'a.
Source: binding type parameters.

~/r/yulang> echo "([1,2].each + [1,3].each).list.say" | yulang run --no-cache
[2, 4, 3, 5]
```

`--no-cache` では正しく `[2, 4, 3, 5]` に届くので、式そのものは型付け可能。
キャッシュ有りのときだけ runtime monomorphize の型変数 `'a` が未確定で残る。
同入力で出力がブレるので、substitution の不足ではなく realm / キャッシュ層
の汚染。2026-05-20 の `each` / `say` 切り分けと同じ系統。

副次観察: 診断の operator 名が `std::ops::#op:infix:+` と未短縮で出ている。
これは 2026-05-20 解決済みエントリ B1 の補足（diagnostic 出力の最短化、
`crates/yulang-infer/src/diagnostic.rs`）と同じ別タスク。

確認:

```bash
echo "([1,2].each + [1,3].each).list.say" | yulang run            # error
echo "([1,2].each + [1,3].each).list.say" | yulang run --no-cache # [2, 4, 3, 5]
```

## 現在の未解決（2026-05-17 / 非 native regression）

現時点では空。新しい非 native regression が出たらここへ戻す。

## 現在の未解決（2026-05-15 round-5）

round-5 の非 native snippet は 2026-05-16 時点で全て再現しない。新しい
非 native regression が出たらここへ戻す。

## 現在の未解決（2026-05-18 / native release gate blocker）

2026-05-18 の native release gate で一度 N11/N13 が未通過になったが、
同日中に解消した。現時点ではこの枠の open blocker はない。

- `std::undet` / `junction` 系の有限 `.list` / `.once` / `.logic` と
  `branch().list` は通常テストと `notes/bugs/solved/` の snippet で通る。
- open-range `.once` の guard 形も、VM / CPS eval / CPS repr eval / CPS repr JIT が
  `:just 3` に届く。
  ```bash
  RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_undet_once_open_range_guard_through_cps_repr
  ```
- `std::junction` + finite `each` + method call + `.once` の統合形も `:just 18`
  に届く。
  ```bash
  RUSTC_WRAPPER= cargo test -q -p yulang-compile runs_junction_method_undet_once_through_cps_repr
  ```
- CLI smoke でも `examples/06_undet_once.yu` は `just (3, 4, 5)`、
  `examples/showcase.yu` の final root は `just 18` で VM と一致する。
- recursive shallow handler + tuple return + block tail の系列は
  [`solved/native_recursive_tuple_handler_memory_unsafe.md`](solved/native_recursive_tuple_handler_memory_unsafe.md)
  に退避した。最終的には effectful `DirectCall` statement の後続 continuation を
  explicit `EffectfulCall` resume に正規化し、unit を runtime value として保持して解消。
- 古い調査ログは `native-scary/` と `render-sink-semantic-type-leak/` に残すが、
  現時点の未解決 snippet ではなく履歴メモとして扱う。

## 現在の未解決（2026-05-16 round-7 / 仕様 docs 順守の素朴な書き方からの収集）

`web/docs/reference/` を順に読みながら docs 通りに書いた snippet を
`yulang run --interpreter` と `yulang run --native` で比較し、
食い違いが出たものを 11 件記録した。round-6 の CPS lowering / undet 系より
広い範囲をカバーしている (display, ref, loop, error wrap, junction, for+if 等)。

**2026-05-17 再確認結果**: 11 件中 11 件は再現しない。2026-05-16 後半の
5 件 (list.show / sub:-for return / loop with / for-if var / for-range console) に加え、
self-rewrap handler / finite undet once+logic / junction all / mutable list ref も
VM と native で一致したため `solved/` へ移した。最後に残っていた
`error E:` + `wrap` の native stack overflow / free `Throw::throw` / garbage
表示も 2026-05-17 に `solved/` へ移した。

### compile-time reject / runtime crash

現時点では round-7 収集分に再現中のものはない。

### 既存 round-6 への補足観察

- round-6 で「`(branch()).list` は `[[1], [0]]`」とあるが、2026-05-17 の
  `native_undet_branch_list_returns_scalar.yu` 修正後は
  `(if branch(): 1 else: 2).list` も VM / native とも `[1, 2]`。
- `Ord::lt` / `Eq::eq` が free variable として CPS lowering に届く経路は
  まだあり、native は `"a" < "b"` / `(1, 2) == (1, 2)` を含むファイルを
  そもそも compile できない。VM 側は runtime で blocked になるだけ。
- `native_cps_lowering_unsupported.yu` の guard 最小再現は 2026-05-17 に
  `solved/` へ移した。

## 解決済み

[`solved/index.md`](solved/index.md) に退避した。snippet の `.yu` も
`solved/` フォルダに移動済み。

回帰確認は `solved/index.md` 冒頭の bash one-liner で全 snippet を VM /
native に流して、各ファイル冒頭コメントの期待出力と食い違わないか見る。
再発を見つけたら該当 snippet を本ファイル上の「現在の未解決」へ戻すか、
`solved/index.md` のエントリに「再発履歴」を付ける。

## docs に反映済み（2026-05-14）

仕様補足と事実訂正を `web/docs` に書き足した履歴。bug ではないが、初学者の
事故を減らすため docs 側へ追記したもの。

- **enum variant の短い名前は `use enum::*` 必須** — `reference/patterns.md`
  の表行と enum 節に追記。pattern 位置で use なしの `red` が silently に
  fresh binding になる注意も入れた。
- **inline type ascription は `as` を使う** — `reference/types.md` の Type
  variable 節の後に「`as` による inline ascription」節を追加。
- **record の `..rest` は全体を指す** — `reference/patterns.md` の Spread
  節を「`..name` は入力 record 全体を bind する」と書き直し、引き算を提供
  しない理由（型システム上十全には行えない）も添えた。
- **handler は shallow** — `reference/effects.md` の handler 節に
  「Handlers are shallow」サブセクションを追加。`run_console (k "42")` の
  ような自己再帰形で書く理由を明示。
- **`--infer` フラグ → `check` subcommand** — `cheat-sheet.md` /
  `guide/pitfalls.md` / `reference/functions.md` の旧コマンド例を
  `yulang check ...` に統一。
- **install.md の `cargo run` 例に subcommand 追加** — `cargo run -p yulang
  -- run path/to/file.yu` に修正、`check` の使い方も併記。
- **`std::ops::add` → `std::int::add` / `(1).add 2`** —
  `reference/operators.md` の「Calling an operator like a function」節を、
  存在しない path の代わりに role method 経由で書く形に修正。
- **`0..10` は閉区間** — `guide/cheat-sheet.md` と
  `reference/control-flow.md` の `for x in 0..10:` 例に「11 回反復、半開は
  `0..<10`」のコメントを足した。

## 確認方法

```bash
yulang run notes/bugs/<file>.yu
# または
cargo run -q -p yulang -- run notes/bugs/<file>.yu
```
