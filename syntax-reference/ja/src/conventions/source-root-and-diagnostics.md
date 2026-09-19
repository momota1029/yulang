# Source root、header、diagnosticの責務

このページは、完全なsource CST、header placement、diagnostic ownershipに関する`syntax-v0`の規約を定める。
parser implementationの経緯ではなく、参照のboundaryを示す。

## Authorityと対象範囲

Authoritativeな*Syntax freeze and vertical-implementation completion-policy amendment*（2026年9月17日）は、受理するgrammarとdirect Rowan topologyを`syntax-v0`としてfreezeする。
Authoritativeな*Rowan CST-only successor amendment*は、一つのdurable lossless CSTを要求する。
Authoritativeなrecovery recordとtopology recordは、保持するrecovery factを定める。

構文ページはそれぞれのordered child grammarを定める。
このページは`Root`だけからconstructごとのchild listを推論しない。

## Source root

`Root`は完全なsource CSTを含む。
sourceを持つdescendantは完全なsourceを順に保持する。
`Root`はheader、recovery fact、diagnosticのための第二のtreeを作らない。

root expression、declaration、root-only operator definitionは、[syntax content model](syntax-content-model.md)が定めるplacementに置く。
nested statement ownershipはowning constructが定める。
root-level statement-sequence wrapperは追加しない。

## Headerとsyntax environment

header constructはCST内でsource-order placementを保つ。
別のheader syntax treeにはしない。
selected syntax environmentとそのeffective operator tableは、parsed sourceに結び付くsyntax inputである。
recovery factでも第二のCSTでもない。

operator capabilityを選ぶとき、importしたcapabilityはsource orderのlocal header declarationより先に置く。
最初に受理したcapability siteが勝つ。
completeなlocal `OperatorHeader`ごとに、selected environmentは同じspellingとfixityでそのaccepted siteを比較する。
異なるsiteが既に勝っていればconflictとなる。
等しいdeclarationもconflictとなる。
binding powerだけではconflictにならない。
environment factは`Invalid`を加えず、ほかの方法でもCST structureを変えない。

## Recovery factとdiagnostic

`Missing`、raw `Error`、structured `Invalid`はCST内のstructural recovery factである。
これらはmalformed sourceを受理するalternativeにせず、recovery structureを保つ。
recovery topologyはsource ownership、retryとcontinuation、caller boundary、fence handoffを変えない。

structural recovery interpretationはCSTから導く。
source orderとequal-range occurrenceのdeterministic orderを保つ。
expected alternativeとprimary alternativeはschema factである。
catalogにないrecovery occurrenceは、recovery topologyの規約が定めるdeterministic generic structural interpretationを使える。

environment factはstructural recoveryから分けてfinal syntax diagnosticへ寄与する。
CSTを変更してはならない。
syntax environmentが変わると、recovery structureを加えずにenvironment diagnosticが変わり得る。

## Migrationの状態

shadow CST diagnostic interpreterは実装済みである。
temporary parser ledgerは現在のpublic syntax diagnosticを保つ。
Gate 4のpending atomic diagnostic migrationは、parser recovery record、reconciliation state、`ParsedFile` diagnostic storageを一つのmigrationとしてretireする。
受理するinput、lossless source、recovery continuation、selected syntax environment、effective tableを保つ。

exhaustiveなslotごとのprecisionはGate 4の前提ではない。
totalでdeterministicなCST-derived interpretationが必要である。

recovery structureは[回復の`Error`と`Invalid`のtopology](recovery-error-invalid-topology.md)を、sourceとrangeの規約は[Rowan CST表記](rowan-cst.md)を参照する。
