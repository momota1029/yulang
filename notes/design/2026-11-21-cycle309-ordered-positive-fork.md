# C309: 出力要求と ordered branching を持つ正の実 source

C308 の child mismatch を成功へ読み替えない。別 source として nominal List[Int] の root が
関連出力 Int を明示要求し、異なる二つの子 role に同じ捕捉 Int を渡す fixture を作る。
入力側の requirements は ID 降順、辞書は canonical ID 昇順とする。
raw Step は実 checked registry の候補 report・frame・installability だけから証明する。
各 leaf を ledger に記録したと仮定せず、現 frame と同一の全モデルから
`evidence_node` の左右を独立に作る。比較対象は入れ替え・重複・切り落とした payload。
証明対象の型（達成した範囲だけ報告）:
- 実 source initial から `Step registry root initial after` と二子の Generated。
- 任意の m, Models after m なら、親の関連出力、左右 leaf、正しい順序の root Evidence が同時に成立。
- 任意の payload, Evidence iff 正しい一つの payload（固定たち）。
- 有限 readback の key・順序付き枝を checked frame の射影と照合し、実 recursive resolver と一致。
一般の source の termination/complete compiler は別。
