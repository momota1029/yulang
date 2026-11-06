# list index の error 宣言（2026-11-06）

## Q12. 下書きの `index_err` と無効indexのpayloadを確定するか

状態: **未回答**。回答済みQ9・Q10の、有効区間 `0 ≤ i < length`、
負のindexの禁止、無効indexを名前つきerror effectにすることは変更しない。
`spec/03-expressions.md` 3.2 は名前とpayloadを明示的に下書きとしている。

例（宣言と観測したい値の説明であり、未実装source runnerの結果ではない）:

```yulang
error index_err:
    out_of_range int

my xs = [10, 20]
xs[-1]     // 下書きAなら payload = -1
xs[2]      // 下書きAなら payload = 2
```

- **A（推奨）:** 下書きをそのまま確定し、`index_err` の `out_of_range` に
  無効だった `int` のindexを渡す。負数・空list・上限超過を同じoperationで扱う。
  既存のQ10に対して最小の追加決定であり、error型も小さい。
- **B:** effect名とoperation名は同じにし、payloadをindexとlist長さのrecord
  （例えば `{index: int, length: int}`）にする。呼出側で再計算せず範囲を診断できるが、
  宣言とpatternの型がAより大きくなる。

影響する義務: `Index` のsource辞書本文のelaboration、具体的なeffect keyと署名、
`catch` / `wrap` が返すerror payload、Rust oracleのerror encoding。
名前を公開するmodule pathは、この問いで新たに決めない。

回答に依存しない部分は `lean/Yulang/NominalListIndex.lean` で進めた。
`integerIndex_some_iff` は任意の有限list・整数位置について有効区間と成功を同値にする。
`effectIndex` は任意の既存 `ErrorEffects.Encoding` と `Int → Error` を受け取り、
無効位置を非再開error要求へ変換する。`wrap_effectIndex` は同じencodingのwrapと一致する。
従ってAを仮採用する必要はなく、現在の証明はどちらのpayloadにも依存しない。
Bの長さは各listを固定した時点で `Int → Error` に捕捉できる。
