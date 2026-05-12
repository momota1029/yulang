# notes/bugs index (2026-05-12)

「素直に書いたら動きそうなのに、現状の実装だと詰まる」 snippet をカテゴリ別に並べる。
各項目に *最小再現* と *現状の出力* と *期待される振る舞い* を書いておく。

## 推論まわり

- [`compose_bound.yu`](compose_bound.yu) — `compose f g` を即時に呼ぶと動くが、
  binding に置くと推論落ちする
- [`lambda_param_in_interp.yu`](lambda_param_in_interp.yu) — lambda の引数を
  `%{x}` 文字列 interpolation に渡すと型推論が壊れる
  (top-level block で同じ body を書くと通る)

## for ループとエフェクト

- [`for_ref_list_grow.yu`](for_ref_list_grow.yu) — `for` ループ内で list ref を
  `+ [x]` で伸ばすと loop effect と ref effect の row が合わない

## ドット解決

- [`dot_via_param.yu`](dot_via_param.yu) — 2 段階バグ。
  (a) `my f p = p.norm2` (注釈なし) は推論不能で当然だが、出力エラーが
      "could not determine the type of expression #0" になっていて
      ドット解決が原因と分からない (診断バグ)。
  (b) `my f (p: point) = p.norm2` (注釈あり) でも、`.norm2` が
      structural record access ({norm2: int}) として解決されてしまい
      nominal companion ルートに行かないため、call site で型不一致になる

## ハンドラ / ランタイム

- [`handler_thunk_panic.yu`](handler_thunk_panic.yu) — `listen prog ""` のように
  「効果計算」じゃなく「関数値」を handler に渡すケースを、型エラーとして
  早めに止め切れていない

## メモ

- いずれも `cargo run -q -p yulang -- --run notes/bugs/<file>.yu` で再現できる
- いまの段階では「効果行の取り回し」と「role 多相 × bind による level 上げ」が
  主な引っかかりどころに見える
