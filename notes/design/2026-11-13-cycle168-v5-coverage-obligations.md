# Cycle168: MixedTree の解釈と V5 evidenceNode の間に残る義務

これは新しい意味論やclassifierの提案ではなく、現在の定義上の証明義務の整理である。基点11be97cb、cycle168 source1004e5ff。

## 今回得た十分条件

`SourceFormed registry root state` と `MixedTree registry state occurrence payload` から、任意の `Models state.current model` に対する現在contextのEvidenceを導く。MixedTreeにはEvidence/Instance/BranchModelsの前提がない。記録nodeにはsource-ID/seed/report/schemaの構造的一致、packet-free leafにはscalarまたは有限nominal-spineのsyntax/state shapeがある。

この解釈定理は、V5の `EvidenceNode` と同じ命題ではない。`B4SkeletonV5.EvidenceNode` はReachable、root/generated、parentとchildのStable、SafeKnown、Unique、同じ現在モデルのchild Evidenceから親Evidenceを要求する。そこにはMixedTreeの存在を仮定してよいという余地はない。

## 次に必要な橋

1. **実際のShared境界の整合**: I26のDecisionGuardとGenerationGuardを使うShared At/Stableに対応するfrontier/Localを使う。古いSupportBoundaryのSafeKnown/Uniqueを名前だけそのまま転用しない。Stableは生成された需要の全At操作を排除する条件であり、あるinstallがguardで止まるだけでは一般安定化を意味しない。
2. **親nodeの構造的coverage**: Reachable＋Stable＋SafeKnown＋Uniqueから、(a) 同じ需要を担当する記録packetと現在へのRelocates、または(b) 現在source shapeを得る必要がある。このcoverageを新しいSourceBoundaryの仮定にして「解決済み」と数えない。今回のRelocatesは計算report/schemaの一致であり、任意のrefreshについて自動的には得られない。
3. **選ばれたkeyと子の一致**: 新しいcurrent_instanceが得るpacketのkey/childrenと、Uniqueにあるkey/childrenを結ぶ。既存 `GeneralDictionarySelectedInstanceCoherence` はその比較の部品だが、そのLocal前提を実際のShared frontierから得る過程が必要。
4. **GeneratedChildren**: 記録packetの子は既存 `formed_recorded` のedge情報から扱える。source scalar/spine leafの子は空。これは全言語での子生成の一般的な完成ではない。
5. **同じ最終snapshot**: V5が渡すchild Evidenceは、親と同じ現在context・modelについてのもの。historical packetのcontextに戻して使わない。今回のcurrent_instanceが移送した親Instanceに、現在のchild Evidenceを接続するのが正しい向き。

## 何を一般化していないか

- packet-free scalar/spine shapeは既存の構造的leaf条件に限定され、任意の多引数・関連型出力を持つ未記録leafを覆わない。
- actual Display→IntのMixedTreeは既存の実例を新しい証明書に乗せたもの。全SafeKnown需要についてMixedTreeがあるとは示していない。
- MixedTreeがあることはTrusted ledgerのsettlementではない。実例にはMixedTreeがあり、RecordedTreeはない。
- captured producerのjournal移送成功は、source2のrouting aliasに依存するconsumerのReadyAtや再開を示さない。前167の固定状態のTrusted反例を保持する。

したがってV5の未証明数は8/14のまま。このノートの各項目も未証明の課題として次のサイクルに渡す。
