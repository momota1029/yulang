# Cycle53: 元要求の occurrence を保持する診断

Status: Draft implementation boundary. Date: 2026-11-09.

## 部分目標
任意の有限 source table、初期入力、有限更新列について、元の batch と要求の順序・重複を
保持する診断を作る。表現された各 endpoint pair の ready / waiting を、元入力の
独立 source model が receiver を str に強制するかどうかと同値にする。
名前が表に存在しない要求も空の endpoint list と元名を保持し、消さない。

## データ・独立な判断・実行版
入力は既存 Problem、実行は既存 solve。診断の leaf は slot pair と Bool の waiting 印。
request node は元名とその全 endpoint pair、batch node は元要求の列を持つ。
独立な意味は元入力全体の SourceModel と ForcesString。実 solver の値を意味に埋め込まない。
証明する主張は、全 table T, initial P, updates U, request r, slots i,j, waiting w について、
r が元入力に属するとき、leaf 所属 iff endpoint 名が r と一致し、
w = true iff 元入力が i を str に強制しないこと。
さらに、診断から元名を取り出した入れ子リストは、入力の全 batch/request 列に等しい。

## 接続の境界
CommonRoleDiagnosticTree は CommonRoleMaterializedDomain.Endpoint.eval を使う。
この decoder は int のみを Ty.atom.int にし、str を含む他の値を unknown にする。
既存 Ty.Atom は int と named のみであり、str を named や int に偽装して接続しない。
今回はその一般 tree の代替ではなく、固定有限 str/equality 断片の診断 adapter を閉じる。
一般四分類、宣言からの request 生成、動的 carrier 拡大、辞書は未接続。
空 endpoint list は scope 情報であり、言語の rejected という意味を与えない。
Bool 印も内部の ready / waiting であり、selected 辞書を作らない。

## 橋と最短連鎖
既存 solve_residual_exact → request の全 pair の診断 exactness → batch 全体の source 順序保持。
実 checked との同値、元名欠落の可視化、更新順による各要求の診断不変を加える。
一般 B4 の残り 5 橋は今回も減らない。特に source_boundary_adequate に scalar carrier の
拡張と意味保存が必要。無意味な wrapper で橋が閉じたとはしない。

## 参照
spec/06-roles.md 6.3（等式流入、兄弟の安定待ち、順序独立）。
work/dots-audit の x-oracle.md X13〜X17 と C3-PARENT を確認した。
旧実機の有限例はこの任意有限入力の診断の一般証明の oracle ではない。
