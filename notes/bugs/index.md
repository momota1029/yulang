# notes/bugs index (2026-05-13)

「素直に書いたら動きそうなのに、実装上詰まった」snippet の履歴。

## 現在の未解決

なし。

## 解決済み

- [`var_effect_leak_with_wildcards.yu`](var_effect_leak_with_wildcards.yu) —
  handler 関数の型注釈に `_` を混ぜると、`my $x = ...` で開いた局所 ref の
  `&x::get` effect が `catch` の scope を抜けて program 最外まで漏れる。
  `web/docs/ja/guide/cookbook.md` の handler レシピが `((), [])` の代わりに
  `request &entries#764::get () blocked=None` を返す。action の値型と return
  型を両方とも具体的に書けば回避できる。
- [`lambda_pattern_unbound.yu`](lambda_pattern_unbound.yu) — lambda 引数に
  destructuring pattern (`\(x, y) -> ...`, `\{ name } -> ...`) を書くと、
  body で名前が unbound になる。binding 形 `my f (x, y) = ...` は同じ
  pattern で通る。`reference/functions.md` / `reference/patterns.md` の例が
  動かない。
- [`list_map_method_unresolved.yu`](list_map_method_unresolved.yu) — list の
  companion method `.map` だけが解決できず "no field or method named `.map`
  could be resolved" で落ちる。同じブロックの `.append` / `.splice` / `.last`
  は通る。`idioms.md` の `xs.map ... .filter ... .len` チェイン例が動かない。
- [`pattern_binding_vs_variant.yu`](pattern_binding_vs_variant.yu) — pattern
  binding 名が in-scope の variant constructor と一致すると、binding ではなく
  nested variant pattern として解釈される。`result::err err -> ...`、
  `just just -> ...`、`ok ok -> ...` などが全滅。errors.md の `wrap` レシピが
  そのまま動かない。`local_name_vs_nullfix` の pattern 位置版。

## 確認方法

```bash
RUSTC_WRAPPER= cargo run -q -p yulang -- --run notes/bugs/<file>.yu
```
