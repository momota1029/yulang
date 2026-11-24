# Cycle 392: I-69 で残った二つの事実の出所

正本 `4b33692365cddbd8e2c6a16f8c0bc3f74ce8ca43`、I-69 inbox blob `5e202637769e290325b60e4425812e784428f3d7`。最上段と S13 の分割は変更しない。証明を始める前の確認。

| 葉 | 今ある前提から出ない事実（一文） | 本来の出所 |
| --- | --- | --- |
| S13bbba | 選んだその出現の元の explicit body / role default を実捕捉に適用した結果が、その ordinal に載る元の typed/ordinary literal RHS と一致すること。 | **(a)** spec 6.3 の関連型等式を作る独立な宣言的 local source rule。C386 `eventAt` は未具体化で `receiptAt` は `Supplies` と位置まで。canonical な住所や `Fits` では代用できない。 |
| S13bbbb | 同じ出現が作ったその RHS の等式が、同じ declarative State の元 fixed target に成り立つ論理制約として残ること。 | **(a)** spec 6.3 の named output の等式を同じ状態で課す宣言的規則。C365 `Fits` はすでにある論理制約・観測を解釈するだけ。特定の native 物理 origin / release の存在を結論に要求するのは spec からは出ないので、その表現を要求に足さない。 |

根拠: [spec 6.3: 関連型は変数と等式](https://github.com/momota1029/yulang/blob/4b33692365cddbd8e2c6a16f8c0bc3f74ce8ca43/spec/06-roles.md#L88)、[where の子と等式への糖衣展開](https://github.com/momota1029/yulang/blob/4b33692365cddbd8e2c6a16f8c0bc3f74ce8ca43/spec/06-roles.md#L133)、[名前つき output と head の分離](https://github.com/momota1029/yulang/blob/4b33692365cddbd8e2c6a16f8c0bc3f74ce8ca43/spec/06-roles.md#L238)、[実捕捉の中心で共有を表す](https://github.com/momota1029/yulang/blob/4b33692365cddbd8e2c6a16f8c0bc3f74ce8ca43/spec/06-roles.md#L383)。 [C386 LocalSource](https://github.com/momota1029/yulang/blob/4b33692365cddbd8e2c6a16f8c0bc3f74ce8ca43/lean/Yulang/GeneralDeclarativeI65LiteralReplay386.lean#L72) は一般 interface で `localRule` と `eventAt` の間に元 body の評価規則を持たない。 [C365 Fits](https://github.com/momota1029/yulang/blob/4b33692365cddbd8e2c6a16f8c0bc3f74ce8ca43/lean/Yulang/GeneralDeclarativeI65State365.lean#L50) から発生させない。少なくとも source RHS の不足を仮定として増やすのではなく、元の source で等式を導く規則を具体化する。

S13bbba を先に検討する。同じ出力が選択を決めないこと、元の where 子の順、actual capture と入力の使い回し、ordinary と declared mode の区別を保つ。実物の導出なしに C386 の `eventAt` へ `ExactSourceRhs` をそのまま field として入れない。未決の carrier 表現を意味論の決定にしない。S13bbbb の証明、Step 2・3、停止性、追加 fixture は行わない。
