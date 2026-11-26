# C434: C17 の元の R(list A, out=A) / R(A, out=B)

spec/06-roles.md §6.3「自分の出力だけを根拠にした展開は保留する」の実形を採る。元親 R(list a) の input list A が authored で、型つきの元 RHS list B が実 row A に保持される。一方、元の where 順 0 の子 R(A,out=B) は A に独立した authored/settled 頭を持たず、親の仮出力が唯一の apparent root head。ordinary raw rows は残る。R の sole authored decl、子の実 occurrence/role/input/named output、実 B6 readback、未完成 B の無互換チェックを独立に検証する。raw graph の A→B は非循環の正例。A の raw K2 と独立 source 証拠は負対照。

実行版は元 row/decl 位置、有限 K2 証人を消費し、出力も completion の Bool も証人として受け取らない。同じ State の既存 `SourceTrace.other .pending` を与え、候補探索・新規子生成・出力書き込みを行わない。R16 に pending-only rule を加えるため DictionarySound の選択枝はそのまま。既存 raw root K2 を優先し、未確定出力も ordinary の K2 判定には残る。C18 や一般停止性は対象外。
