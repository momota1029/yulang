# notes/bugs index (2026-05-14 更新)

「素直に書いたら動きそうなのに、実装上詰まった」snippet の履歴。

## 現在の未解決

### Effect / handler 系

- [`handler_arm_guard_no_fallthrough.yu`](handler_arm_guard_no_fallthrough.yu)
  — handler arm の `if` guard が偽になったとき、次の arm に fall-through
  せず effect が unhandled として外に漏れる。`case` の guard は次 arm に
  進むので、handler 側の dispatch が同じ意味を持っていない。

### Error 系

- [`error_display_impl_missing.yu`](error_display_impl_missing.yu) —
  `error E:` 宣言が約束する `impl Display E` が自動生成されていない。
  `errors.md` の生成リスト 5 つ（enum / act / Throw / Display / wrap・up）の
  うち Display だけ抜けている。`e.show` を呼ぶと「no impl for Display<E>」。
  `wrap` レシピの `err e -> e.show` 行がそのまま動かない。

### Pattern / binding 系

- [`my_record_spread_rest_inference.yu`](my_record_spread_rest_inference.yu)
  — `my { x, y, ..rest } = expr` で `rest` を後段で使うと型推論が失敗する。
  仕様上 `..rest` は record 全体を指す（field の引き算ではない）。case
  経路は同じ pattern で通るので、`my` 経路だけ rest の row 解決が抜けて
  いる疑い。`my_destructuring_unbound`（resolved）の親戚。

### Struct / 型システム系

- [`struct_literal_extra_field_silent.yu`](struct_literal_extra_field_silent.yu)
  — nominal な struct のリテラルに、宣言にない extra field を書いても無警告
  で通り、runtime には extra field が乗ったまま残る。`point { x: 3, y: 4,
  z: 5 }` が `{x = 3, y = 4, z = 5}` を返す（`p.z` は型レベルで弾かれる）。
  値表現と型表現が乖離する。

## 解決済み（2026-05-14 時点で再現せず）

- [`var_effect_leak_with_wildcards.yu`](var_effect_leak_with_wildcards.yu) —
  handler 関数の型注釈に `_` を混ぜると、`my $x = ...` で開いた局所 ref の
  `&x::get` effect が `catch` の scope を抜けて program 最外まで漏れていた。
  現在は `((), [])` を正しく返す。
- [`lambda_pattern_unbound.yu`](lambda_pattern_unbound.yu) — lambda 引数に
  destructuring pattern (`\(x, y) -> ...`, `\{ name } -> ...`) を書くと、
  body で名前が unbound になっていた。現在は通る。
- [`my_destructuring_unbound.yu`](my_destructuring_unbound.yu) —
  `my (a, b) = (1, 2)` / `my { x, ..rest } = rec` / `my [first, ..rest] = xs`
  の destructuring binding が、現在は通る。ただし record の rest spread に
  ついては
  [`my_record_spread_rest_inference.yu`](my_record_spread_rest_inference.yu)
  で別の症状が残っている。
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
  なお wrap 自体は直ったが、error 値の `e.show` は別 bug
  ([`error_display_impl_missing.yu`](error_display_impl_missing.yu)) で
  残っている。

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
