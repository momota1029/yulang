# Cycle150: 一般 EvidenceNode の残差と循環検査

一般 V5 は 6/14 供給・8/14 未解決。このノートは証明依存の監査であり、新しい
反例・意味論・実行規則・分類規則を導入しない。

## 現在すでに導出できる前提

`lean/Yulang/GeneralDictionarySupportEvidence.lean`:

- `selected_support registry state root key children selected` は
  `Local registry state root (.selected key children)` から
  `∃ support, DecisionGuard state registry root support` を導く。
  selected後のsupport不足を独立した未解決事項と数えるのは誤り。
- `stable_joint_packet` 内ではこのDecisionGuardから、実際の選択宣言・実boundsに
  対するPacketGuardを構成する。guardを「選ばれたから存在するはず」と省略していない。
- `stable_merges_of_exact` はExactとStableから実merge closureを導く。
  reachable状態のExactは `GeneralNominalSupportBoundary.reachable_formed` と
  `GeneralNominalSupportSteps.formed_exact` で供給できる。
- `reachable_packetFree_terminal` は、Reachable・journal全体が空・rootまたはGenerated
  focus・Stable・Local.selectedから、`children=[]` と全current Modelsでのleaf Evidence
  を導く。空journalでのstable selected非terminalは既に排除されている。

## 現在の一般的な穴

`lean/Yulang/GeneralNominalCycleSteps.lean` の `Installable` は、通常のmetadata、
lookup、Prepared、selected、merge closureに加え、ChoiceCompatibleとJointを含む。
`lean/Yulang/GeneralNominalJointCandidates.lean` の `Joint registry state focus key` は:

1. focusとalias関係にある全記録packetの宣言IDがkeyと一致すること。
2. 一つのmodelが `Models state`、focusの `BranchAt`、全Related siteそれぞれの
   `BranchAt` を同時に満たすこと。

別siteで個別に存在するPrepared/Survivor modelを、そのまま同一modelとして
合併してはいけない。SameInputsは各site固有のnamed output要求を消去しない。
初回installで新規capture/outputに値を与える共通存在modelの構成は、既に記録された
packetを任意のcurrent modelでreplayする定理とは異なる仕事である。

未解決ケースは、**journalの他所にはpacketが存在するが、対象のselected非terminal
focusにはまだpacketがない状態**におけるJoint構成である。これは未解決ケースの
指定であって、そのような状態が実際にReachableかつStableで存在するという主張ではない。

## EdgeOriginを使う循環に注意

`lean/Yulang/GeneralDictionaryEdgeOrigin.lean`:

- `edge_packet`: SourceFormedと実edgeから、そのedgeを生成した実packetを回収する。
- `committed_nonterminal_origin`: SourceFormed、Committed、packet.children≠[]から、
  同occurrenceの記録packetを回収する。
- `selected_nonterminal_packet`: Reachable、Stable、Local.selected、**Joint**、children≠[]
  から同occurrenceの記録packetを回収する。
- `unrecorded_nonterminal_not_joint`: 上記条件のうちJointを除き、記録packet不在を加えると
  ¬Jointを導く。この含意は具体的な反例の存在を示さない。

したがって「Stable/selected → EdgeOrigin → recorded coverage → Joint」という
証明順序は、最初のEdgeOrigin適用がJointを既に要求するため循環する。
記録packetのない場合のJointを、独立の構造的モデル構成などで先に供給する必要がある。

## Cycle150 alias結果の残差

`lean/Yulang/GeneralDictionaryAliasRecordedLocality.lean` と
`lean/Yulang/GeneralDictionaryAliasMixedLocality.lean` の `early_ordinary_joint` は:

- InitialSourceからの実ordinary traceを明示前提に取り、formationと全packet growthを導く。
- `GeneralDictionaryEarlyMergeChoices.Scheduled` を**別の明示前提に取り**、既存
  `scheduled_coherent` を適用する。任意traceがこのscheduleに従うとは証明していない。
- 各Related siteに現在selectedと構造的coverageを要求する。
  recorded版は同occurrenceの実packet、mixed版はそのpacketまたはfocusの実chosen
  declarationについてのSpineLeafShape/ScalarLeafShapeを使う。
- occurrence同一性、同じ子ID、同じoutput demand、意味的BranchAt/Joint/Evidence、
  独立したkey等号を追加前提としていない。
- しかしfocus自身の実packetは残るため、上記の「初回の未記録非terminal」問題を
  解消したとは数えない。任意HasLeafだけではcross-aliasのkeyを決められないため、
  mixed版は同じchosen declarationを構造検査する制限を保持する。

## 結論

有効なInitialSource＋Reachable＋Stable＋Modelsをすべて備えた未記録selected非terminal
の具体反例は、この監査では確立していない。一般定理を偽とも真とも断定しない。
新しい構造coverage定理を一般V5完成や未解決8項目の削減として数えない。
