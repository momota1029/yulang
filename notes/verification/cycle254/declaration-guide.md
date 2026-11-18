# Cycle254 宣言ガイド
各節の共通前提を同節の定理に適用する。完全な量化順序・型はリンク先Leanと `Cycle254Complete.lean` を正とする。全84明示宣言を含む。

M1上の位置づけ: 全て補助。意味同値readbackは健全性側の支援、有限menu・rank・深さは停止性/完全性側へ向けた支援だが、M1の健全性・完全性・主型性や外側Statementを完成したものではない。K2の新たな拒否規則を追加していない。

## GeneralNominalQueryReadback254
ソース: `lean/Yulang/GeneralNominalQueryReadback254.lean`
任意のquery・有限な正規ground親Pattern・実観測・実SchemaHoldsを対象とする。Shapedはdeferredを許さず、構造nodeのcanonical性とarityを要求する。複数nameのサイズを足し合わせない。
- `GeneralNominalQueryReadback254.Shaped`: 変数名列、scalar、canonicalな構造node、nominalからなるquery形状の述語。
- `GeneralNominalQueryReadback254.member_sum`: 任意の自然数listの各memberはそのsum以下。
- `GeneralNominalQueryReadback254.projection`: CompleteLabelな親の実観測とcanonical Headがあれば、任意の有効射影に親size以下のCompleteLabelな子がある。
- `GeneralNominalQueryReadback254.many_names`: 任意query列のmanyNamesは各query.namesのflatMapと等しい。
- `GeneralNominalQueryReadback254.query_part`: Shaped query、CompleteLabel親、その実観測、実SchemaHoldsがあるなら、任意のquery内nameに親size以下のPartがある。
- `GeneralNominalQueryReadback254.translated_arity`: 任意Patternのtranslationがnodeなら子数がshape.arityと一致。
- `GeneralNominalQueryReadback254.shaped_of_source`: translation一致、Complete query、vocabularyのcanonical性からShaped。
- `GeneralNominalQueryReadback254.translated_shaped`: tidy PatternのComplete translationはShaped。

## GeneralNominalInputReadback254
ソース: `lean/Yulang/GeneralNominalInputReadback254.lean`
任意の実Frame/Holds/ground Inputsを対象とする。coveredHeadやwhere非空を要求しない。massはここでは当該plan.input labelsのmass。
- `GeneralNominalInputReadback254.variable_member`: 任意Pattern列のvariablesArgs内nameは、列内のあるPatternに出現する。
- `GeneralNominalInputReadback254.input_part`: 任意inputNames内nameに、modelで同値な閉じた正規Partが存在し、encode sizeは入力mass以下。
- `GeneralNominalInputReadback254.readback`: 固定modelについて一つのcaptureを選び、全inputNamesにPart・size・depth上界を同時に与え、Capturesを満たす。定義域外はvarで、全域groundではない。

## GeneralNominalOutputReadback254
ソース: `lean/Yulang/GeneralNominalOutputReadback254.lean`
実Frame/Holdsとground Inputsからのreadback。閉じた代表のraw深さであり、再normalize後や正規形性の主張ではない。
- `GeneralNominalOutputReadback254.emitted_meaning`: 実Holdsと実emitted要求・actual mode・成功したtranslationから、その出力targetとcaptureで解釈したPatternとの同値を得る。
- `GeneralNominalOutputReadback254.emitted_readback`: 上記に正規化templateの変数がinputNames内というscopeを加え、閉じた代入代表とtemplate深さ+local massの上界を得る。
- `GeneralNominalOutputReadback254.leaf_no_output_names`: checkedなwhere無し宣言のoutputNamesは空。
- `GeneralNominalOutputReadback254.leaf_associated_scope`: 同じleafの任意associated RHSの正規化変数はinputNames内。
- `GeneralNominalOutputReadback254.leaf_root_readback`: 実Frame/Holds/Inputs、where無し、DeclarationCovered、実rootRequest memberを前提に、閉じた意味代表と加算上界を得る。

## GeneralNominalBinderProducer254
ソース: `lean/Yulang/GeneralNominalBinderProducer254.lean`
任意のchecked packetで実際のwhere child出力targetとparent binderを結ぶ。
- `GeneralNominalBinderProducer254.binder_child`: 任意outputNames内nameに、そのparent binderとtargetが等しい実child出力要求が存在する。別のtarget等式は仮定しない。
- `GeneralNominalBinderProducer254.binder_readback`: 全実child出力に閉じた同値代表と共通depth boundがあれば、全parent output binderに同じboundを移す。

## GeneralNominalDefaultReadback254
ソース: `lean/Yulang/GeneralNominalDefaultReadback254.lean`
defaultはimpl binderでなく役割の位置引数を読む。この違いを保持する。
- `GeneralNominalDefaultReadback254.pattern`: 任意Roles.Termを同形のPatternへ写す。
- `GeneralNominalDefaultReadback254.patterns`: 任意Roles.Term列を同形のPattern列へ写す。
- `GeneralNominalDefaultReadback254.compiled`: 任意Roles.TermのPattern translationはtranslateDefaultと等しい。
- `GeneralNominalDefaultReadback254.compiled_many`: 上記の列版。
- `GeneralNominalDefaultReadback254.variable_bound`: decoder結果の任意出現nameは元term.bound未満。
- `GeneralNominalDefaultReadback254.variables_bound`: decoder列の任意出現nameは元argsBound未満。
- `GeneralNominalDefaultReadback254.default_readback`: ground Inputs、role一致、実default宣言、compileBody成功、実BodyHoldsを前提に、閉じた同値代表を作り、decoded default深さ+local massで抑える。RoleDecl.defaultsScopedを利用。

## GeneralNominalCapturedOutput254
ソース: `lean/Yulang/GeneralNominalCapturedOutput254.lean`
任意実Frame/Holds/Inputsと、実childから供給されるBinderBoundを組み合わせる。
- `GeneralNominalCapturedOutput254.BinderBound`: 各outputNames内binderの同値な閉じた代表と共通深さ上界の述語。
- `GeneralNominalCapturedOutput254.combined`: 実入力captureとBinderBoundから、input/outputNames内で閉じたcaptureを同時に選ぶ。深さはmax(local mass, binder bound)以下。定義域外はgroundと主張しない。
- `GeneralNominalCapturedOutput254.bodyDepth`: explicitはnormalizeしたRHS深さ、defaultはdecoded term深さ。
- `GeneralNominalCapturedOutput254.explicit_readback`: visible associated equation、compileBody成功、BodyHoldsから閉じた代表を作り、normalized RHS深さ+maxの加算で抑える。
- `GeneralNominalCapturedOutput254.witness_readback`: 実OutputWitnessのexplicit/default両場合を扱い、Supplies由来のbodyと閉じた代表、bodyDepth+maxの上界を得る。

## GeneralNominalEvidenceOutput254
ソース: `lean/Yulang/GeneralNominalEvidenceOutput254.lean`
実際に存在する有限Evidence proof treeを前提とする。Evidenceの生成を証明しない。
- `GeneralNominalEvidenceOutput254.FiniteValue`: 指定targetが指定modelで閉じたPattern代表を持つという述語。
- `GeneralNominalEvidenceOutput254.FiniteOutputs`: 任意requested outputがFiniteValueを持つという述語。
- `GeneralNominalEvidenceOutput254.clause_mem`: 任意実clause/signatureから作るchildはpacket.childrenに含まれる。
- `GeneralNominalEvidenceOutput254.binder_bound`: 全実child outputのFiniteOutputsから、有限outputNamesに対する共通BinderBoundを選ぶ。
- `GeneralNominalEvidenceOutput254.local_outputs`: Certificate、ground Inputs、証明書内childのFiniteOutputsから親のFiniteOutputsを得る。
- `GeneralNominalEvidenceOutput254.evidence_outputs`: indexed Evidence treeと各実Frameへのground Inputs供給を前提に、tree.rootの全requested outputを有限readbackする。
- `GeneralNominalEvidenceOutput254.payload_outputs`: 同じ結果をerased payload Evidenceへ移す。

## GeneralNominalSourceReadback254
ソース: `lean/Yulang/GeneralNominalSourceReadback254.lean`
InitialSource、point引数、GroundRoots、Coverage、実mixed Steps、到達状態のModelsを前提とする。入力labelsをsource祖先定理から供給する。
- `GeneralNominalSourceReadback254.input_bound`: 任意実Frame/Holdsの全inputNamesに、元rootLabels mass以下のPartがある。local massとsource massの橋。
- `GeneralNominalSourceReadback254.evidence_outputs`: さらに現在のEvidenceがあれば全requested outputはFiniteOutputs。Evidence前提は残す。
- `GeneralNominalSourceReadback254.mixed_source_outputs`: source boundary Initial/Steps/Models/Evidenceから同じFiniteOutputsを得る。
- `GeneralNominalSourceReadback254.point_source_outputs`: point boundary traceをmixedへ写して同じ主張を得る。

## GeneralNominalProducerOrder254
ソース: `lean/Yulang/GeneralNominalProducerOrder254.lean`
静的candidate-frameのchild-call graph。Selected証明は要求しない。scheduler Step、alias graph、一般等式graphではない。
- `GeneralNominalProducerOrder254.Edge`: 実Frameとそのpacket内childからなるchild,parent関係。
- `GeneralNominalProducerOrder254.child_successor`: visible packetの任意child identityは宣言由来successorsに含まれる。
- `GeneralNominalProducerOrder254.successor_above`: 任意successors memberの数値identityは親より大きい。
- `GeneralNominalProducerOrder254.edge_above`: 任意Edge(child,parent)はparent<child。
- `GeneralNominalProducerOrder254.no_self_edge`: 任意nameに自己Edgeはない。
- `GeneralNominalProducerOrder254.ceiling`: 有限自然数listの最大値。
- `GeneralNominalProducerOrder254.below_ceiling`: 各memberはceiling以下。
- `GeneralNominalProducerOrder254.source_edge_bounded`: 上記source/point/ground/coverage/trace/model条件下でEdgeのchildはsource由来の数値ceiling以下（parent<childはedge_aboveで別に証明）。
- `GeneralNominalProducerOrder254.bounded_accessible`: 辺が数値で増加し有限ceiling以下なら、その静的辺関係でAcc。
- `GeneralNominalProducerOrder254.source_wellFounded`: 実source trace/model条件下の静的Edgeは整礎。operational Step Accではない。

## GeneralNominalOutputMenu254
ソース: `lean/Yulang/GeneralNominalOutputMenu254.lean`
実traceで保たれる有限出力名とbodyのmenu。role defaults map全体の有限性は仮定しない。
- `GeneralNominalOutputMenu254.names`: root requested名と全registry where output名の有限列。
- `GeneralNominalOutputMenu254.clause_name`: visible declaration内clauseのoutput名はnamesに入る。
- `GeneralNominalOutputMenu254.child_name`: 上記clauseChildの任意実requested output名もnamesに入る。
- `GeneralNominalOutputMenu254.source_names`: 任意mixed traceで記録済みsiteの全requested output名は同じsource names内。
- `GeneralNominalOutputMenu254.bodies`: 全visible associated equationと、names上でだけdefaultをlookupしたbody列。
- `GeneralNominalOutputMenu254.supplied_mem`: visible declaration、menu内output名、実Suppliesがあればbodyはbodies内。
- `GeneralNominalOutputMenu254.budget`: bodies内bodyDepthの最大値。
- `GeneralNominalOutputMenu254.body_bound`: 実trace/Frame/要求member/SuppliesからbodyDepthは固定budget以下。

## GeneralNominalProducerRank254
ソース: `lean/Yulang/GeneralNominalProducerRank254.lean`
数値IDの大きさでなくsource frontierの残り要素数を測る。重複は残して安全な上界とする。
- `GeneralNominalProducerRank254.rank`: list内のparent以上の要素数。
- `GeneralNominalProducerRank254.monotone`: parent≤childならrank(child)≤rank(parent)。
- `GeneralNominalProducerRank254.strict`: parentがlist内かつparent<childならrank(child)<rank(parent)。
- `GeneralNominalProducerRank254.length_bound`: 任意list,parentでrank≤list.length。
- `GeneralNominalProducerRank254.positive`: parentがlist内ならrank>0。
- `GeneralNominalProducerRank254.pool`: 元入力mass段のsource frontier。
- `GeneralNominalProducerRank254.frame_member`: source/point/ground/coverage/trace/model条件下で任意実Frameのfocus identityはpool内。
- `GeneralNominalProducerRank254.edge_rank`: 同条件下の任意静的Edgeでrankが真に減る。
- `GeneralNominalProducerRank254.pool_length`: pool長は(1+branching registry)^root mass。

## GeneralNominalSourceOutputDepth254
ソース: `lean/Yulang/GeneralNominalSourceOutputDepth254.lean`
source入力R=mass(rootLabels)、有限body深さT、frontier件数Nを使う。代表はmodelごとの存在、再normalize前のraw Pattern深さ。
- `GeneralNominalSourceOutputDepth254.bound`: focusごとにR+T*rank(pool,identity)。
- `GeneralNominalSourceOutputDepth254.evidence_depth`: source/point/ground/coverage/実trace/Modelsとindexed Evidence treeを前提に、全requested outputにclosed同値代表を作り、bound以下にする。Evidence inductionと実child producer順を利用。
- `GeneralNominalSourceOutputDepth254.payload_depth`: 同結果をerased payload Evidenceへ移す。
- `GeneralNominalSourceOutputDepth254.mixed_uniform`: source boundary Initialから先にD=R+T*Nを一つ選ぶ。全後続mixed状態、全Models、全focus/payload Evidence、全requested outputに、depth≤Dのclosed同値代表がある。Dはfuture state/modelに依存しないが代表は依存してよい。
- `GeneralNominalSourceOutputDepth254.point_uniform`: 同じ量化順序をpoint boundaryに移す。

## GeneralDictionaryOutputReadback254
ソース: `lean/Yulang/GeneralDictionaryOutputReadback254.lean`
既存cycle252の実sourceを使う非空虚回帰。
- `GeneralDictionaryOutputReadback254.evidence`: 初期状態・表示modelに実leaf Evidenceを構成。
- `GeneralDictionaryOutputReadback254.computed_bound`: 同sourceのroot boundは4。
- `GeneralDictionaryOutputReadback254.all_later_readbacks`: 任意後続mixed traceの任意Modelsとroot Evidenceについてtarget3にclosed同値代表がありdepth≤4。
- `GeneralDictionaryOutputReadback254.initial_readback`: 初期状態はpath/models/evidenceを全て具体的に供給して上記を満たす。
- `GeneralDictionaryOutputReadback254.root_input_bounded`: 初期実Frame/Holdsのinput0はsource mass2以下のPartを持つ。

## GeneralNominalRawOutputBudget254
ソース: `lean/Yulang/GeneralNominalRawOutputBudget254.lean`
ground意味代表でなく、展開せず参照を残したraw出力template。実Frameの候補outputに限定し、state全atomを覆ったとは言わない。
- `GeneralNominalRawOutputBudget254.compile`: compileBodyと同じraw explicit/default translation。explicit RHSを追加normalizeしない。
- `GeneralNominalRawOutputBudget254.templates`: source contextと有限bodiesから成功translationのみを列挙。
- `GeneralNominalRawOutputBudget254.budget`: templatesのrawDepth最大値。
- `GeneralNominalRawOutputBudget254.source_template`: 実trace/Frame/要求member/Supplies/compileBody成功ならexpressionは固定templates内。ModelsもEvidenceも不要。
- `GeneralNominalRawOutputBudget254.source_depth`: 同条件下のexpression rawDepthは固定budget以下。
- `GeneralNominalRawOutputBudget254.reference_depth`: 同条件下、任意のMode/name→source名写像で変数を参照にしたmaterialized Exprの深さもbudget以下。参照先名の有限性やatom閉包は仮定から除いて証明したわけではなく、ここでは主張しない。
