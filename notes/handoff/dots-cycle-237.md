# Cycle237 — semantic support and actual head/ancestry bridges

開始2026-11-17 09:31:36 UTC。この報告は途中checkpoint。
最新integration9222fe53、standing-orders/I44再読、STOPなし。
236最終a4f19c64とcompleted心拍、全tree一致を確認。復旧損失なし、稼働競合なし。
Yulang2 audit X13–16とrole003/004を開始時再読。旧実機の局所結果を新kernelの全体保証にしない。

## 最初の19モジュール

- 実refresh/reobserve/equateは全Modelsを保つため、以前の有限semantic supportをそのまま使える。
  install/mergeは新しいpacket/出力/全historical effectのcurrent classの支持だけを追加する。
  installのresidual frameは旧raw Modelsを既存journalから得るので、冗長なordinary atom支持や
  未使用raw slotをもう一度足さない。実source traceからそのsupport導出を構成した。
- reportのProjectionModels/cross/self checksは、実際のanchor/test/capture/checked endpointだけを読む。
  この正確な支持と任意の検証済みModelSupportに対するaggregate代入を接続。
  ProtectedCoveredから実stored equationが得られるが、一般coverage自体は未証明。
- actual head schema・HeadSharing・child actualschemaは既存selectivepatchで保たれる。
  任意current Frame/fullModels/privateHeadModels/actualheadSchemaから全capture Fitsを導出。
  全fullHoldsはHeadModels・actualheadSchema・Outputs・全child(Site.Holds＋actualschema)へ同値縮約。
  independent witnessesを同じmodelだとは仮定しない。出力・子の残件は明示したまま。
- 版付きactual headのweighted mass/readbackとchild semantic labelsを移植。
  InitialSource、point root、GroundRoots、Coverageの下で、実mixed traceの全modelと登録siteに
  depth＋ground label mass≤source mass。実installのcommon modelからenabled install depth boundを導出。
  旧fullHoldsや旧endpointagreementを前提にしていない。これは版数有限・全停止性とは別。
- 固定観測のordinary/context拡張による再構成planは履歴からCommittedを保つ。

## 検証と限界

19モジュールをdirect trust0/warningAsErrorで検証、174 constants監査PASS。定理数とは区別する。
全体lake build/verify-lean.shはstanding orderで未実行。
既存proof、凍結Audit.lean/README.md、spec/plan/lakefileは変更なし。
新たな対象反例は未確定。raw予約名の過剰支持とdescriptor付替えによる版増加は調査中の懸念で、
反例証明でも意味変更の根拠でもない。一般EvidenceNode/Choice/全install停止性は未完。
使用量枠不明。次のcheckpointで成果と限界を更新する。
