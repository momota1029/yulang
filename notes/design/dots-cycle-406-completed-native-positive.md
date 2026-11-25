# C406: 完了出力を下端に使う正の native head

- spec/06-roles §6.3（11/12, 11/22）: 元の必要位置から K2 を調べ、元の完了済み出力を入力の根拠に使う。中心の行の有無はガードに入れない。判定時の支持と raw グラフは別。
- まず単項 `K 'a` 共変値。下端は同じ State の適切な元の producer とその B6 typed receipt の固定先、上端だけは独立な authored Origin。C404 の型付き下端と同じ宣言 mode/table を使う。子の変数は検査しない。raw root K2 と以前の entered-child K2 は保持し、仮の著者を作らない。
- 比較で選ぶことと、実際の辞書を組み立てることを分ける。実 payload 名の読出しは元 q・arg ordinal・path [0] の与えられた authored 型入力から取れる場合を実証する。下端の名前も上端の名前も代用しない。中心の行を選択の条件には入れず、元の名前がこの carrier で未取得なら、その上での実証が不足していると明記する。
- C404 が証明した旧 `SourceHead` の型の壁により、元の state / request / B6 output / Fits はそのまま、新しい completed native root の head 意味を分けて表す。既存 C405 の actual source/ledger は同じ proof と順序で埋め込む。一つの provisional 断片であり、固定文や一覧を編集しない。新しい言語上の拒否・fixture・停止性は対象外。
