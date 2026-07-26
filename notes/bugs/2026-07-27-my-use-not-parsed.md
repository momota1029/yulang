# `my use` が use 宣言として解析されない

発見日: 2026-07-27
状態: 未修正
発見経緯: `my` 可視性 enforcement の MYVIS-A 実装中、Codex が
「source の `my use` が alias registration へ届かない」と報告し、Claude が再現・特性化した。

## 症状

`my use` は `use` 宣言にならず、**`use` という名前の束縛**として扱われる。

```yu
mod child:
    pub value = 41

mod other:
    my use child::value
    pub get() = value

other::get()
```

```console
compile error [yulang.lowering]: source has lowering errors
  detail: binding `use` is missing a body expression
  detail: unresolved value name: value
```

`binding \`use\` is missing a body expression` が、`my` の直後の `use` を
束縛名として食っていることを示している。

## 他の可視性修飾子は動く

```console
our use child::value    -->  run roots [41]
pub use child::value    -->  run roots [41]
use child::value        -->  run roots [41]
my  use child::value    -->  上記のエラー
```

`my` だけが取りこぼされている。

## `my mod` には分岐がある

同じ位置の `mod` には専用分岐がある（`crates/parser/src/stmt/mod.rs:165`）。

```rust
if nud.lex.kind == SyntaxKind::Mod {
    return mod_decl::parse_mod_decl(i, Some(vis_kw), nud.lex);
}
```

`use` に対応する分岐が無い、という形の欠落だと思われる。着手時に確認すること。

## 影響

- **`my use` は綴れるのに何もしない。** 構文エラーではなく、意味の違う宣言になるので、
  書いた人は気づきにくい。
- `notes/design/2026-07-27-my-visibility-enforcement.md` §6 が、compiled-unit format を
  19→20 へ上げる根拠のひとつに「`my use` は public target を private alias にできるため、
  target 宣言から provenance を再構成できない」を挙げている。**その形は現在存在しない**ため、
  この根拠は今日の実装に対しては空である。同 §6 に訂正を追記済み。

  format bump 自体は別の根拠（compiled unit 境界を越える re-export）で依然必要と考えられるが、
  その論証は MYVIS-B で実際に検証すること。推論のまま前提にしない。

## 修正の位置

`my use` は `use` 経路に触る MYVIS-D で一緒に閉じるのが自然に見える。
ただし本件は可視性 enforcement とは独立した parser の欠落なので、
先に単独で閉じても構わない。

## 着手前に確認すること

- `crates/parser/src/stmt/mod.rs` の visibility dispatch に `use` 分岐が無いことの確認。
- `my use` を通したとき、alias の可視性が `Vis::My` として registration に届くか。
- `my use` が本来どう振る舞うべきか。別名は宣言したモジュールとその子孫からだけ見える、
  が §0 の D1 と整合する読み方である。
