# `my` が宣言修飾子として届かない宣言形が多数ある

発見日: 2026-07-27
状態: 未修正
発見経緯: `my` 可視性 enforcement の MYVIS-A で `my use` について、MYVIS-C で
型宣言側について、いずれも Codex の報告を Claude が再現・特性化した。

初版は `my use` だけを扱っていたが、MYVIS-C の調査で同じ原因の欠落が
型宣言のほぼ全体に及ぶことが分かったため、全面改訂した。

## 症状

`my` の直後に来る宣言キーワードのうち、**専用の分岐を持つのは `mod` と `act` だけ**である。
それ以外は `my <name>` の名前として宣言キーワードが食われ、束縛になる。

| 綴り | CST | lowering 結果 |
|---|---|---|
| `my mod m: ...` | `ModDecl` | private module（正しい） |
| `my act effect: ...` | `ActDecl` | `Vis::My` の型宣言（正しい） |
| `my use child::value` | `Binding` | 宣言にならない |
| `my type t = int` | `Binding` | 宣言にならない |
| `my struct s;` | `Binding` | 宣言にならない |
| `my enum e { a }` | `Binding` | 宣言にならない |
| `my error failure: ...` | `Binding` | 宣言にならない |
| `my role r;` | `Binding` | 宣言にならない |

`use` の例では次のようになる。

```yu
mod other:
    my use child::value
```

```console
compile error [yulang.lowering]: source has lowering errors
  detail: binding `use` is missing a body expression
```

`binding \`use\` is missing a body expression` が、`use` を束縛名として読んだことを示している。

## 他の可視性修飾子は動く

```console
our use child::value    -->  run roots [41]
pub use child::value    -->  run roots [41]
use     child::value    -->  run roots [41]
my  use child::value    -->  上記のエラー
```

`my` だけが取りこぼされている。

## `mod` には分岐がある

`crates/parser/src/stmt/mod.rs:165`:

```rust
if nud.lex.kind == SyntaxKind::Mod {
    return mod_decl::parse_mod_decl(i, Some(vis_kw), nud.lex);
}
```

同じ位置に `use` / `type` / `struct` / `enum` / `error` / `role` の分岐が無い。
着手時にこの読みを確認すること。

## 影響

**型名前空間のほとんどが今日 private にできない。** `my act` 以外の型宣言は
`Vis::My` を持てないので、`my` 可視性 enforcement が型に対して実ソースで検証できない。
MYVIS-C の型 matrix は、テスト内で `Vis::My` を直接立てて query 契約だけを検証しており、
**実ソース経路は未証明のまま**である。

構文エラーではなく意味の違う宣言になるので、書いた人が気づきにくい。

`notes/design/2026-07-27-my-visibility-enforcement.md` §6 が format bump の根拠のひとつに
挙げていた「`my use` が public target を private alias にできる」も、この欠落により
今日は成立しない。同 §6 に訂正と、別根拠での確定を追記済み。

## 修正の位置

`use` は `use` 経路に触る MYVIS-D、型宣言側は型に触る MYVIS-C/E と一緒に閉じるのが
自然に見える。ただし本件は可視性 enforcement とは独立した parser の欠落なので、
先に単独で閉じても構わない。**むしろ先に閉じたほうが、enforcement を実ソースで
検証できるようになる。**

## 着手前に確認すること

- visibility dispatch に各宣言キーワードの分岐が無いことの確認。
- `my` を通したとき、各宣言の可視性が `Vis::My` として registration に届くか。
- `my use` の意味論。別名は宣言したモジュールとその子孫からだけ見える、が
  設計文書 §0 の D1 と整合する読み方である。
- 束縛として解釈された結果が「本体が無い」エラーになるのは、`my type t = int` のように
  `=` を持つ形では別の壊れ方をしうる。各形の実際の出力を確認すること。
