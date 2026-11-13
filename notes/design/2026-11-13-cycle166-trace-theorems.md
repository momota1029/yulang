# Cycle166: trace・guard・Evidence の定理ごとの主張

以下の短い名前は各見出しのnamespaceの下にある。`roles/registry/root`、parent packet、producer candidate、refreshed、installed、observedはこのサイクルの具体例。一般化されていない定数を任意stateの定理と読み替えない。完全な型はCycle166PublicTypesと公開再実行ログで照合する。分類はすべて健全性・具体例の補助であり一般の完全性ではない。

## GeneralDictionarySharedCapturedConsequences

- `path_models`: 任意roles/registry/rootとbefore/after、任意の実際のShared Steps、任意assignmentについて、afterのModelsならbeforeのModels。
- `recorded_output_int`: 任意Tracked stateとassignmentについて、具体candidateがstateのpacketsに含まれ、assignmentがそのcurrentのModelsなら、target≃int。
- `recorded_captured_int`: 任意state/assignmentについて、具体refreshedからstateへのShared Steps、candidateの記録所属、現Modelsを前提にsource2≃int。
- `captured_int_after_path`: 任意before/after/assignmentについて、refreshed→before経路、beforeでのcandidate記録、before→after経路、afterのModelsを前提にsource2≃int。

## GeneralDictionarySharedCapturedProducerGuard

- `endpoint_ready`: 任意Fin5 slotについて、slot=3またはslot=4を前提に、そのbase.source slotについて、具体refreshedにおける旧ValueSupport ReadyAtを空supportで得る。親input factを根拠とする。
- `only`: 任意宣言dについて、registryに属しroleがproducerのroleなら、具体producer宣言に等しい。
- `reads_exact`: 具体snapshot・interpretation・宣言head・candidate boundsの読み取り列は正確に[3,4]。
- `decisions`: 具体refreshed、registry、producer、空supportについて旧DecisionGuardが成立。
- `shared_decisions`: 同じ具体状態でSharedSupportのDecisionGuardが成立。親の未settled出力を仮定しない。
- `coherent`: 具体candidateのShared InputCoherenceが成立。葉の空入力schemaを使う。
- `guard`: 具体refreshedにおけるcandidateのShared PacketGuardが空supportで成立。

`input_member` は定理一覧外の証明済み定義として監査される。親の入力factが実際のrefreshed factsに属する証拠である。

## GeneralDictionarySharedCapturedProducerResolution

- `generated`: 具体refreshedのrootからproducerがGenerated。
- `install_step`: 具体candidateがrefreshed.currentでCommittedでないことを前提に、refreshed→installedという実際のShared Step。
- `installed_models`: 具体intモデルがinstalled.currentのModels。noveltyや実行済み仮定を追加せず、installの意味論とbranch witnessから示す。
- `installed_scalar`: 任意assignmentについてinstalled.currentのModelsならsource2≃int。
- `installed_context`: 具体installedの現contextはcandidate.privateContextと等しい。
- `resolved`: 具体refreshedからShared Stepsで到達できるあるfinalStateが存在し、SourceFormed、具体intモデルのModels、全assignmentについて現Models⇒source2≃intを満たす。補助的に既存Committedか実際installかで場合分けする。

## GeneralDictionarySharedCapturedProducerEvidence

- `terminal`: 具体candidateのchildrenは空。
- `current_evidence`: 任意assignmentについてinstalled.currentのModelsなら、installedの**現context**でproducerの辞書node(declaration.id,[])のEvidence。後続scalar refresh後の文脈はこの結論には含まれない。

## GeneralDictionarySharedCapturedResumption

- `producer_step`: 具体refreshed→installedの実際のShared Step。noveltyを仮定で残さずstr反例から証明する。
- `producer_formed`: 具体installedは初期source由来のSourceFormed。
- `producer_prefix`: 具体初期startからinstalledへのShared Steps。親install、fresh-slot refresh、producer installを接続。
- `scalar_step`: installed→observedの実際のShared Step。全現モデルのscalar帰結を使ったexact refresh。
- `observed_formed`: 具体observedはSourceFormed。
- `observed_prefix`: 初期startからobservedへのShared Steps。前述3操作にscalar refreshを追加。
- `models_exact`: 任意assignmentについて、observed.currentのModelsとinstalled.currentのModelsは同値。
- `inhabited`: 具体intモデルがobserved.currentのModels。
- `scalar_consequence`: 任意assignmentについて、observed.currentのModelsならsource2≃int。
- `producer_recorded`: candidateがobserved.current.packetsに記録されている。
- `consumer_raw_ready`: observedの現snapshotで具体consumerのraw RootPendingは偽。Shared Trusted ReadyAt、DecisionGuard、consumerのinstall、Evidenceのいずれもこの結論からは主張しない。

## GeneralDictionarySharedCapturedFinalProducer〔最終文脈の検査だけの補助〕

- `report_exact`: 具体的な最終scalarContextで再構成したfinalPacketのreportは、lo/hiの異なるoriginを持つsource2の二重capture、inspected[(3,4)]、checked[(3,4),(3,4),(2,2),(2,2)]、二つのanchorsという記載通りの有限reportに等しい。一般のrefresh不変性ではない。
- `finished`: 同じ具体的reportはFinished。BranchModelsや実際の導入可能性は結論に含まれない。
- `repeated_bindings`: finalPacket.bindingsは正確に[(0,(2,2)),(0,(2,2))]。二つのcaptureを一つに省略していない。
