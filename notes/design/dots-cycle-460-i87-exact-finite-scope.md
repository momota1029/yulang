# C460 / I-87: 構造帰納で証跡を具体化できる範囲

`ScopedRaw` は scope を節ごとに別実装する reader ではない。一つの相互帰納構文の同じ位置を、raw の実 `AtStep` と `CompiledOpening` で揃えて進む。これらの independent な判断を前提に、選択された唯一の元子についてだけ帰納仮定を適用し、既存の `AuthoredQuery` を子へ輸送する。実行版は同じ snapshot の raw row / Alias / issuer / prefix escape を検査し、元の選択位置と child query を保持する。

- 先頭の本物の `AuthoredQuery` と各実 prefix の範囲があれば、任意有限の同じ raw 経路の末尾 field / raw K2 / 元 source 位置情報を返す有限データが存在する。逆方向および同じ FullState の全 `FitsFull` も成り立つ。これは `any_actual_scoped_source_report_has_an_exact_finite_wire` と `any_scoped_source_receipt_is_the_same_field_in_every_fit`。証跡の無い場合の言語判定や、経路を発見する solver の存在を述べない。既存の累積入口は変更していない。
- `TailBoundary` は実 open binder の tail を一般の未分類 tail と区別する。open tail は G06/G07。アプリの元引数の個数と現 catalogue の exact `Use` だけで mode/layout を区別する。一般 mode/kind・多引数・非 point は G20/G21。単項 covariant の演算子が書けることと、いま見ている実 physical endpoint が point と読めることは別。
- 正規化後も残る join と元に書かれた同一タグの join を区別する。同一書式の例は C459 で実 compile を再生した。残った `Expr.join` と裸の捕捉変数には現在の `Visit` 自体がない（全 raw snapshot に対する補題）。これは言語の拒否でも、join にある未知の分岐に対する新判断でもない。未訪問の payload は構文中に残るが、経路のために raw で開かない。
- 任意の候補に対する `DeclarationReady`・role/出力/point・元 where の適格性、上流が元 inline 位置へ妥当な raw row を置くこと、既存の K2 優先順位を保つ累積入口への持上げは未証明。その切り分けを次に照合する。余った所で prior lane の支持範囲を再チェックし、仕様の判断は増やさない。
