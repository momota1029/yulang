# I-2: Parent/Left/Right の source 例を固定するための不足情報

元の模式例 `impl Parent (box 'a) where Left 'a, Right 'a` だけでは、
Right の関連型の名前・右辺、その出力を結ぶ source 変数、Right receiver が
先に決まる根拠が未記載。完全未知の 'a を、Right impl が唯一だから決める
処理は spec 6.3 に反する。外側 box が分かることだけでは 'a は決まらない。
一般の部分既知区間で不可能だという主張ではない。

1. 元例の補足まで最終適合例への昇格を遅延し、既知receiverからの流入を先に証明する。
2. 概念表記 `Parent (box 'a) where Left 'a, Right str(value = 'a)` と
   `impl Right str: type value = int` のように receiver と出力を分ける。
3. receiver と出力が同じ 'a という意図なら、それを先に決める別のsource制約を明示する。

今回は意味論を決めず 1 の範囲を進めた。実際の既存宣言
`impl Index (box 'b) int: type value = 'b` を既知 `box str` に適用し、
source `addAssociated` から普通制約を生成し、同じsource IDを持つ別slotの
Left候補を絞る橋を証明。これはParent全体の適合例ではない。
特にこのIndex childをそのまま `Parent(box 'a)` のwhereに置くと、既存
first-orderサイズではchild引数合計3がparent2より大きく、Patersonを満たさない。
関連型出力bindingの将来のsource表現・サイズの数え方はここでは決めない。
