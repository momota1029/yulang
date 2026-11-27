# C464 / I-88: 供給済み native 投影の境界

G04 の source-to-raw 条件を分解する。元の inline/bound term から raw 行をこの reader が生成する案は採らない。既存の raw snapshot と、外から明示的に供給された別 snapshot を区別する。追加する観測行は既存行列末尾の一行で、shape と ordinal をチェックする。元の発行済み native 行・issuer・論理 site から物理 owner への route は別の事実であり、単なる値の同値や raw Alias と交換しない。

独立な条件は (1) exact な行と raw shape、(2) 元 snapshot の全 ordinary model が行を満たすこと、(3) 旧 site が safe で、新しい子から元 site の alias class のどの要素にも旧 structural return がないこと、(4) 新 snapshot の既存ルールにより実在の source route と物理訪問を同じ座標で読めること。有限 split witness は (3) について双方向。(2) の証明を仮定する interface は有限／実行可能な全意味モデルの判定を意味しない。別 snapshot の外部供給・真正性は theorem の入出力境界であって、新しい producer の権限ではない。

目標：上記条件のもと任意の旧 site の raw K2 を保存し、実行 read に成功すれば同じ row、元構文位置、native route、terminal を実際の FitsFull で保つ。whole-candidate matching、GD、残余 join、旧 checker、正準 solver/graph は変えない。compiler/normalizer の入力走査と raw visit も区別する。
