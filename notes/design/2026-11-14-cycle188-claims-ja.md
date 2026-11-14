# Cycle188: 主張、量化子、残る境界

以下のstate、registry、roles、root、candidate、model、有限list、自然数は、明記した条件の下で全称量化する。modelの存在を結論にする箇所だけ存在量化。全定理の正確なLean型と公理は `lean/Audit/Cycle188PublicTypes.lean` と対応ログに保存する。

全て辞書健全性へ向かう補助結果。一般の健全性・完全性・主型性を新たに完成したという意味ではない。個々の行で省略する共通前提は各節の先頭に明示する。

## 初期stateから共通modelへ

### HeadInitialCommon188
- `initial_models_iff`: 任意context、全root引数の上下端が同じという条件、任意modelの下で、初期HeadStepEffects.Modelsとcontext.State.Modelsが同値。
- `frame_prepared_model`: 任意state/candidate、実Frameから、そのcandidateの実HeadModelsを満たすmodelが存在。現在stateのModelsはここでは結論に含めない。
- `initial_common_model`: 上記point-root条件と初期stateの実Frameから、同じmodelが現在Modelsと実HeadModelsを同時に満たす。
- `boundary_initial_common_model`: WF/V6の実Initial条件と実Frameから同じ共通modelを得る。一般reachableへは拡張していない。

### HeadInitialFrame188
- `survivor_frame`: 任意contextの実Survivor(key,children)から、初期stateに実Frameを持ち、packet.childrenが元childrenと等しいcandidateが存在。Frameや正のmodelを仮定しない。
- `initial_frame`: 同じ構成をWF/V6のInitialと現在contextのSurvivorへ接続する。

### HeadPointBounds188
- `initial_point_bounds`: point-rootの初期Frame、任意index/intervalが実boundsのindex位置にあるとき、intervalのslotは同一で、実center originがそのsource slotになる。有限indexのdefault値には依存しない。
- `boundary_initial_point_bounds`: 同じ結論をWF/V6 Initialから導く。

## Variable-onlyのprojection

PointReportはtestsが空で、全anchorとcaptureが自己のpoint source originであるという構造条件。
- `PointProjection188.point_append`: 任意2reportのPointReportからappendのPointReport。
- `point_many`: 任意の名前listのlist、bounds、origins、offsetについて、全実boundsの上下slotが同一で対応originがsourceなら、実variables検査reportはPointReport。長さ不一致のFinishedを主張しない。
- `point_projection`: 任意PointReport、任意model、実bindingsのCompatibleから全ProjectionModels。同名の異なるcaptureも含む。
- `point_projection_iff`: 同じ構造条件の下でProjectionModelsと実Compatibleが同値。

### HeadVariableExtension188
共通前提: 実WF Initial、実Frame、翻訳queryが任意有限のvariables listからなること。
- `initial_projection`: 任意modelの実HeadModelsから、同じmodelのcentered ProjectionModels。
- `initial_extension`: さらにChecked registryから、現在Models・HeadEquations・実HeadModels・centered ProjectionModelsを同時に満たすmodelの存在。共通modelは仮定しない。
- `survivor_extension`: 実Frameの代わりに実Survivorと、全eligible Frameの上記query形条件から、Frame、正確なchildren、共通modelを同時に構成。

## Nominal originの追加

### PointOriginEnrichment188
- `projection_visit`: 任意report/modelのProjectionModelsと、追加originの観測存在・全観測Fits・全観測Test.Holdsから、visit後のProjectionModels。
- `projection_visit_none`: originなしのvisitは任意report/modelでProjectionModelsを変えない。
- `nominal_enrichment`: 任意source Models、point slotに記録された実nominal descriptor、typeArgumentsの実結果、任意子query、raw Finishedとraw ProjectionModelsから、root sourceを付けたProjectionModels。入れ子のpointness条件なし。
- `nominal_point`: descriptorをcallerから渡さず、任意nominal queryのFinishedから実descriptorを取り出して同じ結論。
- `nominal_captures`: 任意nominal query/point slotについて、root sourceの追加でcapture列は変わらない。
- `projection_subset`: 任意2report/modelでanchors/tests/capturesが包含されれば、大reportのProjectionModelsから小reportのProjectionModels。
- `projection_parts`: 任意appendのProjectionModelsから両部分のProjectionModels。逆方向でcross条件を消してはいない。
- `projection_recombine`: 任意raw/2新reportで、raw ProjectionModels、両新reportのProjectionModels、append capturesとraw capturesの一致からappend ProjectionModels。
- `none_offset`: 任意query/bounds listで全originがnoneならoffsetは検査結果を変えない。
- `nominal_many`: 任意有限nominal root列と任意子query、point-source root対応、source Models、raw Finished、raw ProjectionModelsからcentered ProjectionModelsとcapture列一致。共有名と非pointなnominal内部区間も残す。

## Mixed rootの共有

### CaptureEnrichment188
Linkは名前・bounds一致、およびorigin一致、またはold originなしからpoint sourceへの追加。
- `projection`: 任意old/new report/model、old ProjectionModels、old実Compatible、全new captureのLink、new anchor/testの意味的成立から、new ProjectionModels。variableとnominalに跨る同名共有を実cross制約で導く。

### MixedOriginEnrichment188
Supportedはvariables/scalar/nominalというtop queryの構造条件。nominalの子queryには制限しない。
- `facts_same`: 任意new ProjectionModelsとold/new capture列一致からFacts（Linkとnew anchor/test成立）。
- `scalar_point`: 任意source Models、point slotのscalar検査Finishedからsource originつきProjectionModels。
- `single_facts`: 任意Supported query、source Models、point slot、raw Finished/raw ProjectionModelsからsource origin追加のFacts。
- `facts_append`: 任意2組のFactsからappendのFacts。capture間の整合性は後段で検査。
- `many_facts`: 任意Supported query列、任意point-source root対応、source Models、raw Finished/raw ProjectionModelsから全列のFacts。
- `mixed_many`: 同じ条件に実raw Compatibleを加えると、centered ProjectionModels。同名を別root種へ跨らせてもよく、distinct-name条件なし。

## 実selectedとoutput側

### HeadInitialEffects188（variable-only）
共通前提はChecked、実Initial、該当FrameのVariableQueries。readyは全eligible Frameの構文的EffectsReadyであり、model存在ではない。
- `chosen_head_exists`: 実Uniqueとreadyから、現在ModelsとChosenHeadを満たすmodelが存在。
- `selected_effects`: 実V6 selectedとreadyから、現在ModelsとChosenClassEffectsを満たすmodelが存在。正のChosenHead baselineを仮定しない。
- `empty_effects_ready`: 任意state/root/candidateで実requestsが空ならEffectsReady。
- `selected_empty_effects`: 実requests空の条件でselected_effectsのready前提を除去。
- `initial_requests`: 任意初期context/rootの実requestsはrootの名前付きoutputsに一致。
- `selected_without_outputs`: root.outputs空だけから実requests空を導き、ready前提なしのselected_effects。

### HeadNominalExtension188 / HeadMixedExtension188
前者はNominalQueries（任意nominal root列）、後者はSupportedQueries（任意mixed root列）を条件とする。共通前提はChecked、実WF Initial。Frameを量化する条件はeligible Frame全てについて。
- 両者の`initial_projection`: 実Frame、query構造条件、任意実HeadModelsからcentered ProjectionModels。
- 両者の`initial_extension`: 実Frameとquery構造条件から、現在Models・HeadEquations・実HeadModels・centered ProjectionModelsの同時witness。
- 両者の`selected_effects`: 実selected、query構造条件、全eligible FrameのEffectsReadyから、現在ModelsとChosenClassEffectsのwitness。
- 両者の`selected_without_outputs`: root.outputs空ならEffectsReady前提を除去。
- Mixedの`selected_registry_effects`: 任意registryで該当roleの可視宣言の翻訳queryが全てSupportedなら、query条件をFrameへの条件ではなく宣言への構造条件に置き換える。実selected/Initial/Checked/root.outputs空から実class-effects witness。

重要: initial_extensionのwitnessとselected_effectsのwitnessは同一とは限らない。後者のHeadModelsやcentered ProjectionModelsを追加して主張してはいない。存在性を全modelでの辞書健全性へ読み替えない。

## Structural sourceとの対応

### StructuralOrigin188
- `similar_refl`: 任意model/originのSimilar反射律。
- `similar_symm`: 任意2originのSimilarの対称律。
- `structural_slot_same`: 任意source Models、実structural slot、任意合法child indexで、actual structural projectionと実child sourceのSame。canonical shapeはstateから導出。
- `same_similar`: 任意2originのSameからSimilar。
- `structural_origin_same`: 任意originが実parent sourceとSimilarなら、そのstructural child projectionと実child sourceがSame。全record labels/arityを扱い、PointInspectionは仮定しない。

## 定義の存在と完成の区別

|項目|状態|
|---|---|
|Checked|一般nominal registry検査の定義あり|
|Models|core/保存effect/current出力の定義あり|
|Step|実HeadStepKernel.Stepの定義あり|
|Stable|同Stepの停止状態の定義あり|
|Generated|raw journal到達の定義あり|
|RootPending|head-only分類の定義あり|
|RootK2|head-only分類の定義あり|
|CandidateK2|head-only分類の定義あり|
|InspectionPending|head-only分類の定義あり|
|Survivor|head-only分類の定義あり|
|Evidence|FeedbackEvidenceの定義あり、一般EvidenceNodeは未証明|
|Reorders|一般定義あり|
|DictionaryEquivalent|一般定義あり|

V6のInitial/OutputConflictも定義あり。今回の一般フィールド新規閉鎖は0。V6にはSkeleton構造体がないので架空の分母は作らない。初期head feasibilityの前提削減と、一般reachable EvidenceNode/DictionarySound/NoFalseRejection/Statementの完成を区別する。

## 意味上同じorigin間の再帰transport

### ReportTransport188
任意state/model/reportを量化する。Optionalは両方none又は両originの値が双方向にsubtype同値となるSimilar関係、Relatedは各capture/anchor/testに対する同名同bounds/同testの対応を意味する。
- `optional_some`: 左がsomeなら右もsomeで、そのoriginがSimilar。
- `test_transport`: 任意test、Equivalentな値、右値でのHoldsから左値でのHolds。
- `projection`: Relatedと右reportのProjectionModelsから左reportのProjectionModels。capture間cross制約を省かない。
- `optional_refl`: 任意optional originは自分自身とOptional。
- `related_refl`: 任意reportは自分自身とRelated。
- `related_append`: 二組のRelatedはreport連結でもRelated。
- `related_visit`: bodyのRelatedと訪問originのOptionalから、同bounds/testのvisit reportもRelated。

### InspectionTransport188
任意state/model、任意有限深さquery/list、任意bounds、任意optional originsを量化。point制約もquery形状制約も不要。
- `structural_optional`: Optionalなparentに同じshape/indexを射影してもOptional。
- `nominal_default`: Optionalなparentに共通fallbackを適用し同じnominal名/indexを射影してもOptional。
- `inspect_related`: Optionalな起点からの実inspect同士はRelated。
- `many_related`: 全indexのOptional対応から実inspectMany同士がRelated。offsetも任意。
- `projection_transport`: 上記Optionalと右実inspectのProjectionModelsから左のProjectionModels。

### StructuralEnrichment188
任意state/model、State.Models、point slot、shape、有限children patterns。直下patternsはSupported(variable/scalar/nominal)で、nominal内のdescendantsは任意。実raw inspectionのFinished、ProjectionModels、およびbindingsのCompatibleを前提とする。
- `structural_enrichment`: slotの実structural記録をさらに指定すれば、起点noneのraw projectionを実source-origin projectionへ拡張できる。
- `structural_point`: shape一致やstructural記録をFinishedから回復し、同じ結論を得る。

### HeadStructuralExtension188
初期point-root state、実Frame、top headがちょうど1本のstructural queryで直下SupportedというStructuralQuery条件。
- `initial_projection`: 実HeadModelsを満たす任意modelから実centered ProjectionModels（必要なsource ModelsはHeadModelsから回復）。
- `initial_extension`: point-root/実Frame/StructuralQueryのみから、同じmodelでcurrent Models・HeadEquations・HeadModels・centered ProjectionModelsを同時に得る。
- `selected_effects`: WF/V6のChecked、Initial、実Local.selected、全FrameのStructuralQueryと出力schema coverageから、current ModelsとChosenClassEffectsを満たすmodelが存在。
- `selected_without_outputs`: root.outputs=[]なら出力coverageを別途仮定せず上と同じ存在結論。
最後のeffect witnessは選択された別のeligible frameに由来しうる。initial_extensionのmodelと同一という主張ではなく、HeadModels/projectionの保存も結論に含めない。

## 最終結果: query形状制約を除いた再帰enrichment

前節のmixed/structural制約つき結果は途中段階として残す。次の最終結果では任意の有限深さQuery、任意有限query列、任意の繰り返しcapture名を扱い、Supportedや単一structural-rootという制約は不要。

### SemanticEnrichment188
任意assignment、型値、origin、capture、reportを量化する。新しい意味Linkは同名・同boundsに加え、旧noneからpoint sourceへの挿入又は旧originとのSimilar対応を保持する。
- `equivalent_trans`: Equivalentの二関係から推移関係。
- `similar_trans`: 同一assignmentのSimilarの二関係から推移関係。
- `similar_source`: originがsourceとSimilarで値を観測するとき、その値はsourceへのassignment値とEquivalent。
- `from_syntactic`: 旧CaptureEnrichmentの任意Linkから任意modelでの意味Link。
- `transported`: 旧→中間の意味Linkと中間→新originのOptional対応、同名同boundsから旧→新の意味Link。
- `projection`: 任意old/fresh reportについて、old ProjectionModels、old bindingsの実Compatible、fresh各captureの対応する意味Link、fresh各anchor/testの検証からfresh ProjectionModels。

### RecursiveEnrichment188
Factsはfresh captureの意味Link、全anchor/testの成立を持つ。任意state/model/reportを量化する。
- `from_mixed`: MixedOriginEnrichmentのFactsを意味Factsへ持ち上げる。
- `append`: 各report対のFactsから連結report対のFacts。
- `transport`: old→middleのFactsとfresh→middleのRelatedからold→freshのFacts。
- `visit`: bodyのFactsとpoint sourceで成立するtestから、source-origin visit後のFacts。
- `single_facts`: 任意state/model/query/slot、source State.Models、起点noneでpoint boundsのraw Finishedとraw ProjectionModelsから、source-originを挿入した実inspectへのFacts。
- `many_facts`: 任意query列/bounds列/origin関数/offsetに対し、各boundsがpointで指定originがそのsource、source Models、raw Finished、raw ProjectionModelsなら実inspectManyへのFacts。query深さ、root個数、nominal内のdescriptor boundsを新たに制限しない。
- `point_many`: 上記に実raw bindingsのCompatibleを加えると、centered ProjectionModels。別々のcapture間制約も保持。

### HeadRecursiveExtension188（最終外側の定理）
任意roles/registry/root/state/key/childrenを量化する。query形状制約は一切ない。
- `initial_projection`: WF/V6の実Initial、実Frame、実HeadModelsを満たす任意assignmentから、そのcandidateのcentered ProjectionModels。source ModelsはHeadModelsから導く。
- `initial_extension`: Checked registry、実Initial、実Frameから、単一modelがcurrent Models・HeadEquations・実HeadModels・centered ProjectionModelsを同時に満たす。
- `selected_effects`: Checked、実Initial、実Local.selected、全eligible Frameに対するEffectsReadyから、current ModelsとChosenClassEffectsを満たすmodelが存在。Frameや正のbaseline modelは前提ではない。
- `selected_without_outputs`: Checked、実Initial、実Local.selected、root.demand.outputs=[]だけから上の存在結論。EffectsReadyもquery条件も不要。

source State.Modelsはpacket.context.stateについて、current Modelsはcentered stateについての判断で、両者を取り違えない。最後のselected-effect witnessは別eligible frame/modelを許す。一般reachable stateへの拡張、子のinstall、EvidenceNode/BodyPlanは依然として未証明。一般フィールド新規閉鎖0は変わらない。

補記: `GeneralNominalPointProjection188.point_append` は任意stateと二reportについて、それぞれPointReportなら連結もPointReportであるという補助定理。上のPointProjection群の連結補題を正確な名前で記した。
