# Cycle185: WF/V6 の量化範囲・定義棚卸し

対象は `GeneralNominalCenteredHeadWFBoundary.boundary` と実際の `HeadStepKernel.Step`。旧ground Gへの到達可能性を仮定しない。19モジュールの101公開定理の正確な名前・全前提・結論は `notes/verification/cycle185/theorem-signatures.md`、暗黙引数を含む推論済み型は同ディレクトリの `public-types.txt`。補助定理数を一般フィールド完了数に換算しない。

## 主張

- `HeadRawSeparation185`: 任意のroles/registry/rootとWF到達可能状態について、任意のpurpose≥7のfresh名はrawSourcesに属さない。任意の有限個のその名の値を変更しても全raw journalのModelsを保存する。全effect Modelsの保存にはcentered ledgerと歴史/live effect支持の値の保存が別に要る。
- `HeadSiteCoherence185`: Checked registryとWF到達可能状態で、任意の二つの登録siteのwhole occurrenceが等しければsiteが等しい。invocation identityだけの等式には一般化していない。
- `HeadReadback185`・`HeadCandidateReadback185`: 登録済み歴史planと現在候補について、Checked、到達可能性、登録入力、同occurrence/同declaration、現在context、実head useなど型に列挙した全前提の下で、すべてのfullモデルの候補originを歴史binderへ読み戻す。非point binderの版は非output/非pointの前提を持つ。
- `HeadEffectsOrigin185`・`HeadOutputSupport185`・`HeadEffectReadback185`: 任意の実HeadStep traceに沿い、記録済みeffectのsnapshotは実際の到達状態に由来し、core plansはeffectsのplan射影と一致する。snapshot/live出力支持に属するpurpose≥7名について、実際のschema binderと、全fullモデルで読戻せる固定originを導く。外部にoutput target除外を仮定しない。
- `HeadFullOverlap185.wf_full_overlap_readback`: 任意のWF到達可能状態とpurpose8名が完全な `HeadLedgerFrame182.fullSources` に属するなら、ある一つの歴史originが存在し、すべてのAssignmentについてfull `HeadStepEffects.Models`なら、そのoriginと対象sourceがSameである。存在証人はモデルの全称量化より前。originの一意性は主張しない。
- `HeadHistoricalExtension185.wf_extension_iff_historical`: 任意有限個のpurpose8 binder引数、任意の既存fullモデル、endpoint/originのfullSourcesリンクの下で、到達可能性から歴史証人を得て、旧支持の値とfull Modelsを保存する引数拡張の存在を必要十分条件で記述する。観測存在・Fits・同一center整合性・候補と歴史originのSameは条件として残る。
- `HeadRootOverlap185.candidate_root_overlap`: Checked、WF到達、登録入力を持つ現在root候補、可視declaration、任意の非output/非point実head-useとfullSources overlapの下で、すべてのfullモデルにおいて候補originと候補binderはSame。歴史planや希望するSameそのものを仮定しない。
- `HeadRootExtension185.root_extension_iff`: 上記root候補の任意有限個の実head-use、任意の既存fullモデル、endpoint/originのfullSourcesリンクの下で、旧fullSources値と全Modelsを保ち選択した引数のHoldsを満たす拡張が存在することと、各観測の存在・全観測のFits・同一binderの観測間整合性は同値。歴史overlap条件は導出済み。候補plan全体のJoint、生成された需要、一般EvidenceNodeは結論ではない。

## 13定義項目と証明の区別

|項目|今回確認したWF境界の参照先/意味|
|---|---|
|Checked|一般nominal registry検査の定義あり|
|Models|coreおよび各effectのsnapshot Holds/live出力の定義あり|
|Step|実HeadStepKernel.Stepの定義あり|
|Stable|同Stepが進めないことの定義あり|
|Generated|raw journal到達の定義あり|
|RootPending|head-only分類の定義あり|
|RootK2|head-only分類の定義あり|
|CandidateK2|head-only分類の定義あり|
|InspectionPending|head-only分類の定義あり|
|Survivor|head-only分類の定義あり|
|Evidence|FeedbackEvidenceの定義あり、一般EvidenceNodeは未証明|
|Reorders|既存一般定義あり|
|DictionaryEquivalent|既存一般定義あり|

根拠はHeadStepBoundary.fields/remaining/Initial、HeadWFBoundary.boundary。V6追加のOutputConflictも定義あり。この棚卸しは言語全体の網羅性でも13本の証明完了でもない。

今回閉じた一般フィールドは **0**。旧G/V5のRemaining4本とWF/V6を混同しない。既存HeadWFTransferには12構造補題とV6 Exact/SaturationTotal/OrderIndependentがあるが、B4SkeletonV6構造体は存在しないので「V6の14本中12本完了」と数えない。NoFalseRejectionやV6 Statement全体の新規完了も主張しない。既存一般WF rootsから今回の新宣言への到達は0/138、局所4rootからは114/138。後者は一般接続ではない。

## 次の3つの橋

1. `registered_identity_centers_same`（未実装）: 同じinvocation identityを持つ登録siteの対応centerについて、構文上のsite等式ではなく、すべてのfullモデルで意味的Sameを示す。HeadSiteOrigin185、ChildCoherence184.producer_declarationsを出発点に、実producerの親identity帰納を行う。root一意性とchild fresh allocationを区別する。
2. `head_use_transport_same`（未実装）: 対応centerの意味的一致を用いたhead schemaのorigin投影/読戻しtransport。現HeadReadback185の構文的一致版を単に適用することはできない。OriginTerms.holds_transportを使いつつ、variablesのname/modeを保つ関係的schema帰納が要る。投影観測の存在は自明扱いしない。
3. これらをHeadFullProducer185/HeadBinderIdentity185と合わせて任意候補のoverlap一致へ進め、リンク・観測・Fits・同一center整合性を実分類から導き、全候補Joint、子証拠、親証拠へ接続する。現在root断片のiffだけでは一般EvidenceNodeを閉じない。

## 既存の別の障害

integrationには既にHeadWFJoinCounterexample.not_generatedChildren/not_v6_selected_productionがある。multi-tag variant materialization欠落により、現在WFの一般生成橋は単なる未証明でなく反証されている。これは今回の発見ではない。HeadMatStepHistory.Builtは後継journalの過大近似で、実Stepではない。境界/生成の修復は監督のAstra担当。今回、仕様や境界を弱める変更はしていない。利用者の意味論判断を要する新しい選択肢は提出していない。

## 最終追加: 意味的transportの独立基盤

`HeadSemanticTransport185` の6公開定理を追加し、最終合計は20モジュール・107公開定理。任意modelとSameな二つのoriginについてHeadを移送し、対応投影の同じ値のObservesが同値と証明した。投影自体のSameには左投影の自己Same（観測存在と全観測間coherence）を明示した。nominal Headだけからtype slotの観測存在を捏造していない。

`holds_leaves` は任意の同じExpr構造・二つのleaf-origin割当・その構造に出現する全leafのSameの下でHoldsを移送する。`holds_leaves_and_root` はさらに根のSameを合成する。登録siteの同identity center一致、実head schemaのRecipe対応は未証明で、上記次の橋2の独立基盤にとどまる。最終公理gateは147宣言を検査済み。
