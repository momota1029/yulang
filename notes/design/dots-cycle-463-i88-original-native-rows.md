# C463 / I-88: 同一 raw row と元 AST の複数位置

有限 request は、同じ解析済み宣言に対する検査済み表 membership と、元 ordinal・実 point/role、旧 source compile を使う。宣言の証明書は準備段階で消化しており、request witness にはない。組み上げに失敗した表は新しい Yulang の拒否ではない。同じ declaration の membership を持つ表に替えても、同じ request 読取は不変。

一つの構造 reader の成功は、原入力の同じ normalized head を辿り、実際の raw equation index、Alias、ChildAt、native producer の同じ issuer/route 証跡を各 hop で持つ。raw index で照合するので似た row を別位置で代用しない。「各 raw step」と「元 AST の literal path」を同じ (address, logical child) で帰納的に zip する。既存の正式な訪問である限り、元 AST の literal path は少なくとも一つあり、返した全てが同じ normalized terminal と同じ indexed model evidence を持つ。証拠の中では元の全 path を保存し、表示位置は決めない。

normalize は既定どおり元構文を調べる（同一な正規化 join の両腕を見て判断することを含む）。しかし未訪問の raw 子に追加の開口・循環検査・認可をしない。既存の dual-inline 実例では同じ fitting model、同じ raw equations、同じ field/row と、同じ書かれた tag を重ねたことによる二つの別な元位置 (左、右) を確認。違う raw ordinal・元 clause、表なし、同 ID 別宣言などは対照。残余 join の中へ新たに降りない。元 inline/bound child を raw physical slot に一般に生成する上流と候補優先の実 dispatch は未証明。
