# cycle 487: 許可された元 prefix からの G05 tape

## データと独立な関係

旧 State・GD・raw 位置表とその関係は変更しない。元 demand 下端の列を維持する。既存で guarded かつ安全な下端には同じ finite old graph に対する checked root を作る。候補に渡す許可は引き続き別の入力であり、元 ordinal、元引数、元 action と物理位置列を含む key に適用する。空 prefix は root として処理し、proper prefix は許可されたときだけ、その子の符号を読む。独立な判断は旧 signed Trail と全 proper prefix の許可の連言。prefix 許可の有無と全候補の意味的な match/mismatch は別である。

## 実行と定理

- 元 demand の順序を保持し、既存 root checker を通る packet を返す。位置表で同じ logical 下端が重ならないことと、その exact 位置が guarded かつ非循環であることを仮定すれば、指定された全下端について同じ順に構成できる。欠落・符号不明・循環 root は成功と読み替えない。
- 旧符号が読める元 root から、同じ有限 node budget で、許可された proper prefix だけを下る。成功時は許可に合う旧 Trail の順序つき部分列を返す。各終点の許可が全 proper prefix に遡る条件の下で、同じ入力に対する C486 の末端フィルタと一致する。条件は局所入力の正確さとして別に扱い、実言語の規則とは断定しない。
- 全候補に同じ scoped compiler を使い、生成した packet を C485 checker に戻す。全実候補・実引数ごとの元開始位置、全接頭辞の許可と署名の境界を検証する。旧入口を置き換えない。G04 の名前つき未証明命題と G10 の選択・照合は変更しない。

## 明示的な許可表の検査

新しい公開前段は、各許可行の全 proper prefix が同じ元 ordinal・引数・元 action/pose・旧位置列で表に含まれるかを、型商や符号を読まずに調べる。不整合な表は none。許可を補ったり、届かなかった訪問を実言語上の安全と見なしたりしない。各行が本当の source 許可に対応することは別の前提であり、型等価や whitelist の自己一致からは導かない。既存の permissive Bool 入口と比較する深さ 2 の試験は、欠けた先祖を単に無視した場合に局所結果が違うことを示すための境界試験である。

## I-100 の固定した目標

このサイクル中に I-100 を受け取った後、先に `G05Goal : Prop` を宣言する。証明は付けない。正確な元 safe roots・prior の Boolean と独立な許可の同値・元 prefix 整合・実引数始点を名前つきの `G05ExactVisitInputs487` で受ける。局所の rigid-match / definitive mismatch / unresolved は意味を新たに決めず、有限な局所検査と独立な判断の関係を `G05ExactLocalProtocol487` として受ける。局所意味を任意の `FitsFull` で解釈する場合も別の前提である。

目標の report は同じ State の全可視候補を元 ordinal の順で一度ずつ残す。実際に許可され読まれた各元引数の path だけを記録し、真の K2 がある場合には全 hit を元順で返して通常の選択・曖昧性に進まない。なければ各候補の局所分類を引き渡すのであって、ここで辞書を選ばない。既存 flat の Bool を保持し、異なる report / witness タグの取り違えは false。今周の root と prefix tape は G05Goal の exact visits / K2 への足場で、prior を局所型付けから作らない。G04Entry は未証明・変更なし。
