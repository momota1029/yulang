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
  — `my { x, y, ..rest } = expr` の `rest` の型推論が失敗する。`my (a, b)` や
  rest なし record は通るので、record spread `..rest` を含む `my` 経路だけ
  残っている。`my_destructuring_unbound`（resolved）の親戚。

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

## 仕様だけど docs 側で補足が欲しいもの

実装は意図通りで、bug ではない。docs に書き足すと初学者の事故が減る。

- **enum variant の短い名前は `use enum::*` 必須**（Rust と同じ、混ざらない
  ためのデザイン）。`reference/patterns.md` の「`tag x` | 短い名前で書く
  enum variant（曖昧でないとき）」表記は誤読を招くので、「`use enum::*` の
  後でのみ短名で書ける」と明記したい。さらに、pattern 位置で use なしの
  `red` と書くと variant マッチではなく **fresh binding** として silently
  通るので、
  ```yulang
  enum color = red | green | blue
  case c:
      red -> "r"      -- ← `red` は fresh 変数。すべての値にマッチして
                       --    `green` / `blue` arm が unreachable
      green -> "g"
      blue -> "b"
  ```
  のような書き間違いが起こりやすい。pitfalls.md / patterns.md に
  「short-name variant pattern には use が必要」と一節入れたい。
- **inline type ascription は `as` を使う**（`:` は colon application との
  衝突回避のため）。
  ```yulang
  ([] as list int)
  ```
  は通る。`reference/types.md` / `reference/casts.md` のどちらにも `as`
  キーワードでの inline ascription が明記されていない。casts.md は
  「`cast(x: A): B` 関数定義」と「expected-type 境界での暗黙挿入」までで、
  ユーザが「型を一回明示してから渡したい」場面で `as` に辿り着く誘導が
  ない。`reference/types.md` の Type variable 節か、`reference/casts.md`
  の頭に「inline ascription は `(e as T)`」を入れたい。
- **handler は shallow** — `catch action: op, k -> body` の body 内で k が
  返した先で再度同じ effect が起きると、handler は **自動的には適用されない**。
  再帰的に handler を巻き直す必要がある:
  ```yulang
  my run(a: [eff] 'r): 'r = catch a:
      eff::op _, k -> run (k ())   -- ← run で巻く
      v -> v
  ```
  tour.md / cookbook.md の例（`run_console (k "42")` のような再帰呼び）が
  この前提で書かれているが、shallow handler だと一言断ってあると、
  「なぜ再帰呼びが要るか」が読み手に伝わる。`reference/effects.md` か
  type-theory.md に追記したい。

## docs と挙動の小さな乖離（snippet 化していない）

- **`--infer` フラグが現存しない**: `cheat-sheet.md` / `pitfalls.md` /
  `reference/functions.md` に
  `cargo run -q -p yulang -- --infer examples/showcase.yu` の例が残って
  いるが、現在の CLI には `--infer` オプションがない。`yulang check
  examples/showcase.yu` が代替。
- **install.md の `cargo run` 例が subcommand 抜け**:
  `cargo run -p yulang -- path/to/file.yu` と書かれているが、現在は
  subcommand が必須。`cargo run -p yulang -- run path/to/file.yu` か
  `cargo run -p yulang -- check path/to/file.yu` に直したい。
- **`std::ops::add` という path は存在しない**: `reference/operators.md` の
  「演算子を関数として呼ぶ」節で `std::ops::add 1 2` を「明示形」として
  紹介しているが、`std::ops` には `+` operator 定義しかなく、`add` という
  free function はない。実体名は `std::int::add` か role method `x.add y`。
- **`0..10` は閉区間**: `cheat-sheet.md` の `for x in 0..10: println x.show`
  例を読んだ初学者は半開区間を想定しがちだが、`0..10` は 0..=10 の 11 要素
  （半開は `0..<10`）。`reference/types.md` には明記されているので仕様。

## 確認方法

```bash
yulang run notes/bugs/<file>.yu
# または
cargo run -q -p yulang -- run notes/bugs/<file>.yu
```
