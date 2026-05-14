# notes/bugs index (2026-05-14 更新)

「素直に書いたら動きそうなのに、実装上詰まった」snippet の履歴。

## 現在の未解決

## 解決済み（2026-05-14 時点で再現せず）

- [`var_effect_leak_with_wildcards.yu`](var_effect_leak_with_wildcards.yu) —
  handler 関数の型注釈に `_` を混ぜると、`my $x = ...` で開いた局所 ref の
  `&x::get` effect が `catch` の scope を抜けて program 最外まで漏れていた。
  現在は `((), [])` を正しく返す。
- [`lambda_pattern_unbound.yu`](lambda_pattern_unbound.yu) — lambda 引数に
  destructuring pattern (`\(x, y) -> ...`, `\{ name } -> ...`) を書くと、
  body で名前が unbound になっていた。現在は通る。binding 形 `my f (x, y)`
  も同じく通る。
- [`my_destructuring_unbound.yu`](my_destructuring_unbound.yu) —
  `my (a, b) = (1, 2)` / `my { x, ..rest } = rec` / `my [first, ..rest] = xs`
  のような top-level destructuring binding が、runtime export でも後続 scope
  から参照できる。現在は通る。
- [`list_map_method_unresolved.yu`](list_map_method_unresolved.yu) — list の
  companion method `.map` だけが解決できなかった。現在は通る。
- [`list_filter_method_missing.yu`](list_filter_method_missing.yu) — list の
  companion method `.filter` が解決できなかった。現在は通る。
- [`list_methods_undocumented_missing.yu`](list_methods_undocumented_missing.yu)
  — docs にある `xs.first` / `xs.rev` / `xs.sort` が stdlib companion method
  として登録されていなかった。現在は通る。
- [`result_methods_undocumented_missing.yu`](result_methods_undocumented_missing.yu)
  — result の `.map` / `.and_then` / `.unwrap_or` が companion method として
  登録されていなかった。現在は通る。
- [`lazy_operator_thunk_in_tuple.yu`](lazy_operator_thunk_in_tuple.yu) —
  lazy infix operator の結果を tuple 要素の位置に置いても、現在は
  `<thunk>` が漏れずに `true` として評価される。
- [`pattern_binding_vs_variant.yu`](pattern_binding_vs_variant.yu) —
  pattern binding 名が in-scope の variant constructor と一致すると、
  binding ではなく nested variant pattern として解釈されていた。現在は
  binding として通る (`result::err err -> ...` が動く)。
- [`labelled_for_var_effect_collision.yu`](labelled_for_var_effect_collision.yu)
  — labelled for loop 内で `&hits = $hits + 1` のような var update を
  混ぜると、外側 loop の `last 'outer` の effect row が壊れていた。現在は
  nested loop で `last 'outer` しつつ集計できる。
- [`enum_curried_payload_unresolved.yu`](enum_curried_payload_unresolved.yu)
  — 複数 payload variant を `tree::node value left right` のように分解しても、
  それぞれの payload 名が単独 bind される。現在は `[0] 3` を返す。
- [`default_arg_method_recv_unresolved.yu`](default_arg_method_recv_unresolved.yu)
  — default 持ち record pattern の後続引数で `.move` の receiver が固まる。
  現在は `[0] 4` を返す。
- [`branch_merge_cast_missing.yu`](branch_merge_cast_missing.yu) — 分岐合流位置で
  暗黙 cast boundary が使われる。現在は `({raw = 7}, {raw = 0})` を返す。
- [`list_fold_method_inference_failure.yu`](list_fold_method_inference_failure.yu)
  — `[1, 2, 3].fold 0 (\acc x -> acc + x)` が callback を curried 関数として
  扱う。現在は `[0] 6` を返す。
- [`record_alias_default_mix.yu`](record_alias_default_mix.yu) —
  record pattern で「alias + default」(`host: h = "..."`) と「default only」
  (`port = 80`) を同じ pattern に混ぜても通る。`f {}` のように optional
  field が呼び出し側で省略された場合も、default / role bounds 由来の型が
  runtime specialization に残る。

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
  例文を `std::int::add 1 2` か `(1).add 2` に直すか、`std::ops::add` を
  reexport で用意するかどちらか。
- **`0..10` は閉区間**: `cheat-sheet.md` の `for x in 0..10: println x.show`
  例を読んだ初学者は半開区間を想定しがちだが、`0..10` は 0..=10 の 11 要素
  （半開は `0..<10`）。`reference/types.md` には明記されているので仕様。
  cheat-sheet 側に一言補足があると親切。

## 確認方法

```bash
yulang run notes/bugs/<file>.yu
# または
cargo run -q -p yulang -- run notes/bugs/<file>.yu
```
