# Cycle110: 構造ordinaryと宣言由来関連等式の同じ有限閉包

状態: Draft、2026-11-11。既存spec6.3の関連等式と既存ordinary規則の接続。

## 大きな部分目標

任意の有限source occurrence列・初期ordinary atom列から、宣言で計算される関連等式と
構造分解・推移を同一のHorn閉包で交互に導く。callerからcarrier、fuel、batch、traceは取らない。
まず任意の有限ordinary Horn clause列に対して、初期atomとclauseの全syntaxからcarrierを作る。
次に、既存associated valueの計算をpaired receiver boundsからpaired output boundsへのclauseにする。
宣言の値を一括で初期制約へ追加せず、必要なreceiverの上下界が導かれたときだけ発火させる。

## 独立判断と予定の型

`Derives seeds clauses atom` は seed / split / trans / clause の独立な帰納的判断。
全seeds/clauses/atomについて `atom ∈ saturate seeds clauses ↔ Derives seeds clauses atom`。
有限性は `carrier (seeds ++ clauses.flatMap (premises ++ [conclusion]))` から証明する。
普通の意味保存と異なり、関連等式はモデルを狭める。
全assignmentについて、最終atom列のモデル iff 初期atomのモデルかつ
「独立導出で全premiseが得られるclauseの結論」を満たすこと、を証明する。

source側の判断ではclause生成を参照せず、`DeclarativeComputed` とreceiverの二方向の
導出からoutputの二方向を導く。既存WellFormed/AssocWellFormedは前提に明示する。

## 境界

有限occurrence列、receiverのtemplate、source slotsは既存入力。動的where生成、fresh名、
K2、一般の関連型RHS、parserとの接続は閉じない。scalar decoderは既存int/str断片のまま。
新しい言語上の拒否規則や一意候補からのreceiver推論を追加しない。
主要橋5本は未完だが、橋2/3のordinaryとassociatedの相互feedbackの有限断片を閉じる。

## 照合

work/dots-auditのy2-claims-role-boundaries-cycle-2.mdのROLE-MORE-001/002/003/005を読んだ。
旧whereの差を新specの意味論に持ち込まない。新しいYulang2実行はしない。

## 次の部分目標: 任意の因果的scheduleの順序独立

firstFreshの固定順だけでなく、独立な1-step判断(seed/split/trans/clause)と
fresh条件に従う任意scheduleについて、開始空cacheからの実行長を同じcomputed carrierで
制限する。maximalな有限scheduleの最終membershipは独立Derivesとiff。
終端の閉包条件は明記するが、未証明のfairness仮定で停止を主張しない。
実firstFresh traceがその実行判断を満たし終端であることも結ぶ。
これでwhere occurrence順、ordinary/associatedの発火順に対する最終観測の不変性へ進む。
途中のtrace長・木の再build数や辞書列の文字通りの一致は主張しない。

## 次の部分目標: named ordinary構文からStateとallocationを内側で作る

任意の有限 `Atom Nat` 列と既存の構造的Programから名前を収集し、重複除去したtableへ
割り当てる。ordinaryの3つの既存grammar条件をBooleanで検査してStateを作る。
外部のn、slot map、checked State、receiverを作る高階関数は受け取らない。
空入力も扱うため末尾に未使用の内部slotを1つ置く。実入力名はそのslotへ行かず、
異なる実入力名が同じslotへ行かないことを証明する。言語上の名前を追加しない。
parserとscope解決、Programの有限occurrence選択は引き続き境界として明示する。
