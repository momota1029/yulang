# Cycle150: 同じ実宣言の未記録 leaf を含む alias coverage

一般 V5 は 6/14 供給・8/14 未解決のまま。

`GeneralDictionaryAliasMixedLocality` は recorded-alias coverage を拡張する。
各 Related site は、同occurrenceの実packetを持つか、**focusで選ばれた実packetの
同じdeclaration**について構造的SpineLeafShapeまたはScalarLeafShapeを持つ。
各siteの現在selectedは引き続き要求する。occurrence IDの同一性は要求しない。

任意 HasSpineLeaf / HasScalarLeaf だけでは、その別siteのdeclarationとfocus keyを
結び付けられない。Uniqueは同じoccurrenceでだけ候補を比較するためである。
同じ実declarationの構造検査を用いれば、別の意味的key等号を仮定せず、現在の同じ
assignmentでInstanceとBranchAtを構築できる。leafにはpacket・Instance・Joint・
Evidenceを仮定しない。terminal・出力要求なし等のshape制限はそのまま残る。
Spineは任意有限unary point-wrapper列とinjective leaf binderに限定される。

記録済siteはそれ自身の歴史をreplayする。未記録leafは上の構造検査からbranchを
構築する。いずれも与えられた一つのcurrent modelを変更せず、各site独立の存在model
を混ぜない。coherent journalにより記録packetのkeyをそろえ、rootの現在Uniqueと
合わせJointを導く。

`early_ordinary_joint` のordinary traceとEarlyMergeChoices.Scheduledはともに
明示前提である。前者からformation/growth、後者から既存coherence定理を適用する。
この新モジュールは任意traceのScheduledを証明せず、任意siteのcoverageも証明しない。
`covered_of_recorded` により直前の全記録coverageはこのmixed coverageの特殊例。
一般SameInputsから任意の出力要求や子辞書を転送したという主張ではない。

## 検証
Lean 4.35.0 direct compile `-DwarningAsError=true`: exit 0。
4定理の公理検査および完全修飾 `#check @early_ordinary_joint` を
`lean --trust=0 -DwarningAsError=true` で実行: exit 0。
依存公理は propext / Classical.choice / Quot.sound のみ。full build未実施。
開発中にはNonempty展開と予約語localのエラーを直し、最終検査で解消を確認した。
