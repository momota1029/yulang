# 保護と解除の覚え書き: `'e?` (2026-11-06)

一枚の覚え書き。AE(代数的 effect)の研究者に相談するとき、将来論文にするときの出発点にする。
署名: Claude (Sonnet 5.5), 2026-11-06。主張の発案はユーザー(`'e?` の記法と、callback の衛生性の設計)。
先行研究との関係は、私が確かめたものではない。「確かめたい点」の節に分けて書く。

## 主張

高階の callback を渡したとき、callback が起こす effect は、内側の handler に奪われない。
Yulang はこの衛生性を、**境界ごとの整数の重み**で表す。

- effect の各出現は、境界ごとに整数の重みを持つ。
- 境界を越えて保護すると、許可マスクにない effect の重みが `+1`。
- 対応する解除は、同じ境界・同じマスクで `−1`。
- handler が捕まえられるのは、対象の effect で、**すべての境界の重みが 0** のときだけ。

保護と解除は、足し算と引き算なので、**互いの逆元**になる。
そして、解除に当たる印が、**推論された型に自動で現れる**: `'e?`。

```text
('a -> ['b[io]] 'c) -> ('c ['b] -> ['b?, 'd] 'e)
```

`f` の戻り行で `'b` が保護され(`+1`)、`g` の戻り側の `'b?` で解除される(`−1`)。
往復して 0 に戻るので、外側の handler から見える。

## 例

callback を受け取る関数の内部に、同じ key を捕まえて `99` を返す handler を置く。

- 保護なしでは、内側の handler が callback の effect を奪って `99` を返す。
- 高階の保護を入れると、引数側の `−1` が、内側の捕まえを阻止し、戻り側の `+1` で相殺されて、
  元の呼び出し側の handler が payload `7` を受け取る。

Lean の例: `DirectedHigherOrder.Examples.contravariant_debt_preserves_local_callback`。

## 証明したこと (Lean, `lean/Yulang/`)

| 性質 | 定理 | 場所 |
| --- | --- | --- |
| 保護と解除は両方向に相殺する | `release_protect`、`protect_release` | `Directed` |
| 関数を含む任意の値で、両方向の相殺が成り立つ | `transport_opposite` | `DirectedHigherOrder` |
| 単純な erase の解除は往復を復元できない(反例) | `fresh_roundtrip_is_not_symmetric` | `HigherOrder` |
| 由来の条件の下で、関数の呼び出しは内側の handler に捕まらない | `guard_arrow_noncapture`、`guarded_map_noncapture`、`default_zero_boundary_noncapture` | `DirectedHigherOrder`、`Directed` |
| computation を引数に取る実際の関数にも、両方向に通る | `value_opposite`、`tree_opposite` | `OperationalTransport` |
| checker が受理した式に、fresh な境界を割り当てても、非 capture が保たれる | `closed_checked_boundary`、`principal_fresh_boundary` | `CheckedHygiene`、`InfiniteOperationalCorrespondence` |
| 無限の重みの集合(再帰で保護が積み増される型)でも成り立つ | `least_principal`(最小解)、`InfiniteRowHygiene` の相殺 | `RecursiveRows`、`InfiniteRowHygiene` |
| 返却された closure の呼び出しが、非 capture を保つ | `guarded_call_noncapture`、`principal_guarded_arrow_calls` | `InfiniteOperationalTransport` |
| handler の arm が、許可マスクに無い key を扱うと、その arm は決して実行されない(診断と同値) | `diagnostic_iff_unreachable` | `HandlerPermissions` |
| shallow handler の結果の effect 上界 | `shallowHandle_bounded` | `SignatureRequests` |

## 前提と注意

- 非 capture は無条件ではない。もともと重みが `−1` の出現に `+1` を足すと `0` で可視になるので、
  定理は「その境界で重み 0 から来た」という前提 `ZeroAt` を明示する。
- 相殺の定理は、境界名の個数も重みの大きさも制限しない(任意の有限な `Fin n`、上限のない整数)。
- 実行時の closure の変換は、有限の形(atom・pair・arrow)で証明した。record と variant の中の closure は、
  この実行モデルでは空の解釈で、まだ扱っていない。

## 確かめたい点 (先行研究との関係, 未確認)

私が論文を読み込んで確かめたものではない。AE の研究者に聞く、または自分で読んで確かめる。

- **tunneling** (Zhang & Myers, *Abstraction-safe effect handlers via tunneling*, POPL 2019):
  callback の effect が、間にある handler を通り抜ける考え方。保護の発想に近い。
  確かめたい点: 往復の逆元(解除)を持つか。型に返済の印を自動で出すか。
- **lift / coercion** (Biernacki ほか, *Abstracting algebraic effects*, POPL 2019、
  *Binders by day, labels by night*, POPL 2020): effect の位置をずらして内側の handler を飛ばす。
  確かめたい点: 符号付き(負の差分)を許す定式化か。無限の保護の積み増しを許すか。
- Koka の `mask`: evidence の位置のずれとの対応。静的に決まる重みを evidence の offset に落とせるか。
- 差になりうる点(私の読み): 符号付きの重みで**往復の逆元**を持つこと、解除が推論された型に自動で出ること、
  保護が積み増される再帰も拒否せず許す(意味は最小解)こと。

## 実装への含み

- 重みのベクトルを持って、加減して、0 かを見るだけなので、Rust でも小さく書ける。
- 静的に決まる重みは、evidence passing の位置のずれに落とせるかもしれない(未検討)。
- 参照: `lean/Yulang/Directed.lean`、`DirectedHigherOrder.lean`、`OperationalTransport.lean`、
  `spec/05-effects.md` 5.4・5.5、`spec/07-display.md` 7.3。
