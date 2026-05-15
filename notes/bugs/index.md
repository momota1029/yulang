# notes/bugs index (2026-05-15 更新)

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

## 現在の未解決（2026-05-15 round-5）

### Effect / handler 系

- [`role_method_in_for_body_pattern.yu`](role_method_in_for_body_pattern.yu)
  — `for p in pairs:` の body 内で `case p: (n, just s) -> ... s.len ...` の
  ように nested pattern + role method (`.len`) を呼ぶと、`Len::len` が
  unhandled として外まで漏れる。同じ case を for の外で書くと通る。
  `wrap_inside_for_body_leaks_fail`（resolved）と兄弟で、`for` body 内に
  role-dispatch effect が積まれた時の row 解決に問題が残っている疑い。
- [`handler_fn_missing_join_evidence.yu`](handler_fn_missing_join_evidence.yu)
  — `my f comp = catch comp: ...` を annotation なしで書くと
  `missing join evidence for handle` で死ぬ。annotation 付きなら通る
  （cookbook の `cb06_log_handler.yu` 形）。「handler を関数に切り出す」
  最初の一歩が internal-meaning なエラーで止まる。

### Error 系

- [`wrap_does_not_traverse_from_chain.yu`](wrap_does_not_traverse_from_chain.yu)
  — wrap 自体は narrower error を `from` 経由で同時捕捉できるようになった
  が、`case res: err e -> e.show` の経路で `Display::show` operation が
  unhandled として漏れる。`error_display_impl_missing` /
  `error_display_from_chain_missing` の direct value `.show` は通るのに、
  `wrap` 経由で result に閉じた後の `e.show` だけ通らない。`fs_err` simple /
  `io_err` from-chain どちらでも同じ症状。

## 現在の未解決（2026-05-15 round-6 / `yulang run --native` との差分）

VM (`yulang run --interpreter`) と native (`yulang run --native`) で結果が
食い違うものを集める。既存の `native_*.yu` snippet と並べる。

### 表示 / 値の repr 系

- [`native_value_repr_in_tuple.yu`](native_value_repr_in_tuple.yu) —
  bool / unit / string が tuple / list / record の中で正しく表示されない。
  `(true, 1, "s", ())` が VM `(true, 1, "s", ())` / native `(1, 1, s, 0)`。
  variant も `:just hello` のように tag に `:` が付き、payload string が
  unquoted。format-only か repr 潰しか境界が曖昧。
- [`native_handler_result_value_collapse.yu`](native_handler_result_value_collapse.yu)
  — handler を関数化して list / tuple を返すと、native 側で値が `0` /
  空 tuple に潰れる。`["a"]` が `0`、`((), "hi\n")` が `(0, )`。VM では
  普通に出る。`native_effect_handler_tuple_result_prints_pointer.yu`
  （既存）と同じ家系。

### CPS lowering 未対応 / 値違い

- [`native_cps_lowering_unsupported.yu`](native_cps_lowering_unsupported.yu)
  — handler arm の `if` guard と labelled `for` の bare effect operation
  (`#loop_label:outer##with0::...`) が CPS lowering 未対応で
  `failed to compile native effects object` で止まる。VM では通る。
- [`native_serial_var_double_count.yu`](native_serial_var_double_count.yu)
  — `examples/02_refs.yu` がそのまま native で `(11, 21)` ではなく
  `(22, 22)` を返す。`my $x; my $y; &x = ...; &y = ...; ($x, $y)` の var
  serial 経路で、tuple element が両方とも同じ slot を引いてさらに二重に
  進んでいるような値。

## 解決済み（2026-05-14 時点で再現せず）

- [`handler_arm_tuple_payload_pattern.yu`](handler_arm_tuple_payload_pattern.yu)
  — act operation の payload が tuple のとき、handler arm で `op (s, n), k
  -> ...` のように個別 bind すると `cannot match a tuple pattern against ?`
  で落ちていた。現在は payload pattern の構造から runtime payload 型を作り、
  `s` / `n` を個別 bind できる。
- [`record_field_value_selection_selector_shape.yu`](record_field_value_selection_selector_shape.yu)
  — native source regression を足そうとした時、`my r: {ok: bool} = ...; r.ok`
  が field value selection ではなく `:ok Record(...)` のような
  selector-shaped な値/適用として出ていた。現在は record field value
  selection が native CPS repr path でも plain value として返る。
- [`callback_list_index_raw_type_stuck.yu`](callback_list_index_raw_type_stuck.yu)
  — `my hs = [h]; ((std::list::index_raw hs) 0)()` のように callback/function
  value を list に入れて取り出すと、`index_raw` の element type `a` が
  runtime type として固まらず、型が固まった後も native 側では inner `sub`
  に捕まっていた。現在は source-shaped forced CPS repr path で VM と同じ
  `0` を返す。
- [`var_effect_serial_collision.yu`](var_effect_serial_collision.yu) —
  同じ scope で `my $a = ...; for ...; my $b = ...; for ...` と var を順に
  開くケースが、現在は `(3, 3)` を返す。
- [`typed_effect_handler_inference.yu`](typed_effect_handler_inference.yu)
  — 型引数を持つ effect (`act state 'a:`) の handler が、`[state int]`
  から `int` に specialize されて現在は通る。
- [`var_effect_leak_with_wildcards.yu`](var_effect_leak_with_wildcards.yu) —
  handler 関数の型注釈に `_` を混ぜると、`my $x = ...` で開いた局所 ref の
  `&x::get` effect が `catch` の scope を抜けて program 最外まで漏れていた。
  現在は `((), [])` を正しく返す。
- [`lambda_pattern_unbound.yu`](lambda_pattern_unbound.yu) — lambda 引数に
  destructuring pattern (`\(x, y) -> ...`, `\{ name } -> ...`) を書くと、
  body で名前が unbound になっていた。現在は通る。
- [`my_destructuring_unbound.yu`](my_destructuring_unbound.yu) —
  `my (a, b) = (1, 2)` / `my { x, ..rest } = rec` / `my [first, ..rest] = xs`
  の destructuring binding が、現在は通る。
- [`list_map_method_unresolved.yu`](list_map_method_unresolved.yu) — list の
  companion method `.map` が解決できなかった。現在は通る。
- [`list_filter_method_missing.yu`](list_filter_method_missing.yu) — list の
  companion method `.filter` が解決できなかった。現在は通る。
- [`list_methods_undocumented_missing.yu`](list_methods_undocumented_missing.yu)
  — docs にある `xs.first` / `xs.rev` / `xs.sort` が stdlib companion method
  として登録されていなかった。現在は通る。
- [`result_methods_undocumented_missing.yu`](result_methods_undocumented_missing.yu)
  — result の `.map` / `.and_then` / `.unwrap_or` が companion method として
  登録されていなかった。現在は通る。
- [`lazy_operator_thunk_in_tuple.yu`](lazy_operator_thunk_in_tuple.yu) —
  lazy infix operator の結果を tuple 要素の位置に置いても、現在は force
  された値が返る。
- [`pattern_binding_vs_variant.yu`](pattern_binding_vs_variant.yu) —
  pattern binding 名が in-scope の variant constructor と一致するときも、
  現在は binding として通る。
- [`labelled_for_var_effect_collision.yu`](labelled_for_var_effect_collision.yu)
  — labelled for + var update で外側 loop の `last 'outer` の effect row が
  壊れていた。現在は通る。
- [`enum_curried_payload_unresolved.yu`](enum_curried_payload_unresolved.yu)
  — 複数 payload variant の `tree::node value left right` 分解が現在は通る。
- [`default_arg_method_recv_unresolved.yu`](default_arg_method_recv_unresolved.yu)
  — default 持ち record pattern の後続引数で receiver type が固まる。
- [`branch_merge_cast_missing.yu`](branch_merge_cast_missing.yu) — 分岐合流
  位置で暗黙 cast boundary が使われる。
- [`list_fold_method_inference_failure.yu`](list_fold_method_inference_failure.yu)
  — `xs.fold 0 (\acc x -> acc + x)` の callback が curried 関数として通る。
- [`record_alias_default_mix.yu`](record_alias_default_mix.yu) —
  「alias + default」と「default only」を混ぜた record pattern も通る。
- [`catch_role_method_thunk_invariant.yu`](catch_role_method_thunk_invariant.yu)
  — role method 経由 effect の catch、handler-in-handler の runtime invariant
  違反が解消された。
- [`string_interp_block_invades.yu`](string_interp_block_invades.yu) —
  `%{...}` 内で `;` や `{` を書いても文字列に侵食しなくなった。
- [`wrap_inside_for_body_leaks_fail.yu`](wrap_inside_for_body_leaks_fail.yu)
  — `for` body 内の `E::wrap` が `fail` を正しく捕まえる。
- [`wrap_does_not_traverse_from_chain.yu`](wrap_does_not_traverse_from_chain.yu)
  — `E::wrap` が `from` 連鎖の narrower error を直接捕まえる。
- [`handler_arm_guard_no_fallthrough.yu`](handler_arm_guard_no_fallthrough.yu)
  — handler arm の `if` guard が偽のとき、次の arm に fall-through する。
- [`error_display_impl_missing.yu`](error_display_impl_missing.yu) —
  `error E:` 宣言から `impl Display E` が自動生成され、`e.show` が通る。
- [`error_display_from_chain_missing.yu`](error_display_from_chain_missing.yu)
  — `error io_err: fs from fs_err` のような from variant を持つ error 宣言でも
  `impl Display io_err` が生成され、from payload の `Display` に委譲する。
- [`handler_recursive_extra_arg_runtime.yu`](handler_recursive_extra_arg_runtime.yu)
  — handler arm 内で `listen(k (), log + o + "\n")` のように handler を
  再帰呼び出ししつつ追加引数を渡すケースが、現在は `((), "hi\n")` を返す。
- [`my_record_spread_rest_inference.yu`](my_record_spread_rest_inference.yu)
  — `my { x, y, ..rest } = expr` の `rest` が record 全体として bind され、
  後段の使用や extra field access も通る。
- [`struct_literal_extra_field_silent.yu`](struct_literal_extra_field_silent.yu)
  — nominal struct constructor の record literal に宣言外 field を書くと
  `unknown record field` として弾く。

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
