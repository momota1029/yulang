# notes/bugs index (2026-05-13)

「素直に書いたら動きそうなのに、実装上詰まった」snippet の履歴。
現時点では、このディレクトリの `.yu` は未解決 bug 一覧ではなく、修正済み挙動や
期待 diagnostic の手元確認用として残している。

## 現在の未解決

- なし

## 修正済み / 期待 diagnostic

### 推論まわり

- [`compose_bound.yu`](compose_bound.yu) — `compose f g` を binding に置いても
  `f 3` が `7` を返す。
- [`lambda_param_in_interp.yu`](lambda_param_in_interp.yu) — lambda 引数を
  `%{x}` 文字列 interpolation に渡しても `Display::show` の型が壊れず、
  `x is 5` と `6` が出る。

### for ループとエフェクト

- [`for_ref_list_grow.yu`](for_ref_list_grow.yu) — `for` ループ内で list ref を
  `+ [x]` で伸ばしても ref effect が保持され、`[1, 2, 3, 4, 5, 6]` を返す。

### ドット解決

- [`dot_via_param.yu`](dot_via_param.yu) — 注釈なしの `my f p = p.norm2` は
  推論不能として、root expression ではなく `.norm2` の receiver 型不足を指す
  diagnostic を出す。注釈あり版は regression test に昇格済み。

### parser

- [`doc_comment_brace.yu`](doc_comment_brace.yu) — `--` doc comment 内の `}` を
  token として漏らさず、後続の `1` が実行される。
- [`indent_neg_silent_drop.yu`](indent_neg_silent_drop.yu) — 字下げ次行の `-2` で
  `-` が silent drop せず、`1` と `-2` の2 root として読まれる。
- [`tail_lookahead_design_note.md`](tail_lookahead_design_note.md) — tail lookahead
  heuristic を恒久化しないための設計メモ。

### ハンドラ / ランタイム

- [`handler_thunk_panic.yu`](handler_thunk_panic.yu) — handler に効果計算ではなく
  関数値を渡すケースは Rust panic ではなく型エラーで止まる。

## 確認方法

```bash
RUSTC_WRAPPER= cargo run -q -p yulang -- --run notes/bugs/<file>.yu
```
