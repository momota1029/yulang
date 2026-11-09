# Cycle20: source-indexed associated feedback adapter

既存の有限 source closure の各 Node に、有限個の associated Request を注釈として与える。
これは parser/一般区間の lowering そのものではない。receiver は固定、annotations は入力。
外部の有限 cardinal k、table、emit の三つを別々に渡す必要を除き、closure の nodes と
注釈を平坦化した (Node, Request) の有限リストから全て計算する。

独立な所属判断は q の注釈への request 所属。計算table/emitとの iff を証明する。
任意 registry/root/annotations、q/request について request∈annotations q iff
∃ i, i∈emit q ∧ table i=request。その上で任意 associated env/roles/wf/seed と
最終 ordinary model assignment、最終 Reach q、annotations q の request、Computed head
から、その request の出力slotとheadのEquivalentを示す。

Bridge1/2の有限更新adapter部分を接続する。一般B4の5橋は5本とも一般形が残る。
原文sourceからannotationsを導出する橋、変動receiver、順序独立、診断treeは未達。

追加: 非単調feedbackの最終closedだけでは、収集済み更新の由来を表せない。
実行と独立なTrace判断（freshなIDがその時点のReach nodeのemitにある場合のみ一歩）を定義し、
実loopがTraceを構成すること、収集済み全IDが過去のあるReachなnodeに由来することを証明する。
最後にReachでなくなったnodeからの等式も保持されるため、最終Reach-only最小解とは呼ばない。
