# Source root、header、diagnosticの責務

このページは、source root、header、diagnosticの責務について承認済みのtargetを定める。
direct Rowan construction、header discoveryとselection、`Error` tokenと`Invalid` nodeのCST topologyは実装済みである。
後続のCST由来diagnostic migrationは実装待ちである。

## Source root

`Root`は完全なsource CSTを入れるcontaining nodeである。
sourceを持つdescendantはsource orderを保つ。
root schemaはheader、recovery fact、diagnosticのための第二のtreeを作らない。

構文schemaは`Root`の下に置くordered child grammarを定める。
このページはroot nodeだけから構文ごとのchild listを推論しない。

## Header selection

operator syntaxを選ぶ必要があるため、実装済みのheader discoveryはfull parseより前に行う。
選択に必要なsource identity、coverage、import、完全なlocal operator factを保持する。

現在のfull parseは、それらのfactと与えられたsyntax environmentからrootをparseするtableをcompileする。
現在の実装はparserが作るrecovery diagnosticとconflict diagnosticも公開する。

実装待ちのtargetでは、full-parse plannerが一つのeffective operator tableを返す。
importしたcapabilityをsource orderのlocal header declarationより先に置く。
既存のfirst-capability-wins ruleがaccepted siteを選ぶ。
selected syntax environmentとeffective tableは、analysisのsyntax inputとしてparsed CSTとともに残る。
第二のsyntax treeでもrecovery ledgerでもない。

このtargetでは、header discoveryはopaque bodyを持つtemporary treeを使ってよい。
header recovery diagnosticは公開しない。
syntax diagnosticを公開するのはfull CST analysisだけである。
header parseとfull parseはdiagnostic streamをreconcileも比較もしない。

## CST由来diagnosticの責務

完了したtopology-only migrationはCST shapeだけを変更した。
raw malformed sourceは`Error` tokenに記録し、`Invalid`は承認済みのstructured ownerだけに使う。
既存のparser recovery record、frozen-header reconciliation、公開するdiagnosticは、一時的なcompatibility machineryとして残る。

後続のCST由来diagnostic targetでは、parserはstructural recoveryを`Missing`、`Error`、`Invalid`に記録する。
syntax-schema interpreterは、frontendがred CSTをwalkするときにstructural diagnosticを導く。
frontendまたはtype traversalが存在するまでは、whole-tree collectorがtoolとtestのために同じ解釈を行う。

grammar slotはordered child positionと、それを解釈するために必要なancestor contextを表す。
parent kindだけではslot identityにならない。
parser diagnostic ledgerを削除する前に、recoveryを持つすべてのslotを文書化しなければならない。
この最初のsliceは個別のslotを割り当てない。

interpreterはsource orderでvisitする。

- `Missing`に入ると、nodeのzero-width rangeでslotのmissing diagnosticを出す。
- 同じslotかつimmediate parentにある、隣接する`Error` tokenの最大列は、combined rangeに一つのmalformed-input diagnosticを出す。
  通常のtrivia、`Missing`、nested node、slot boundaryが列を終える。
- `Invalid`に入ると、childをvisitする前に`Invalid.text_range()`に対するstructured-recovery diagnosticを出す。
  `Invalid`はtransparentではない。
  validなnested syntaxを含んでもouter diagnosticを必要とする。

同じrangeは、文書化されたslot orderとoccurrence ordinalで順序を決める。
diagnostic identityは一つのsnapshot内に限る。
構成要素はtree occurrence path、grammar slot、diagnostic kind、ordinalである。
rangeはUTF-8 byte rangeであり、diagnostic identityがsource revisionをまたいで安定することは約束しない。

targetのpublic resultは、`ParsedFile`のdiagnostic arrayではなく、このtraversalから出る一つのordered sequenceである。
expected alternativeとprimary alternativeはschema constantである。
raw malformed spellingはCST token groupまたはそのsource rangeに残る。
parallel parser recordには置かない。

## Environment diagnostic

実装待ちのtargetでは、selected effective tableをenvironment diagnosticにも使う。
同じCST analysisは、完全なlocal `OperatorHeader` occurrenceに入ると、同じspellingとfixityでaccepted capability siteと比較する。
異なるsiteが既に勝っていれば、child recovery diagnosticより前に、その`OperatorHeader` occurrenceへconflicting-operator diagnosticを出す。
traversalはその後、source orderでchildを続けてvisitする。
等しいdeclarationもconflictとして比較する。
binding powerだけを比較してはならない。

environment diagnosticはCSTへ`Invalid`を書き込んではならない。
capability provenanceだけが変わる場合は、CSTを再利用してanalysisをやり直せる。
effective tableが変わる場合はparse結果も変わり得る。
その場合、同じsource textでも同じCSTは約束しない。
最初の安全なreuse unitは、whole source revisionとeffective syntax-table identityである。

## 現在と実装待ちのpublication

現在の実装はparserが作るrecovery diagnosticを公開している。
完了したtopology-only migrationは、`Error` tokenと限定した`Invalid` nodeをemitする。
このpublicationはそのまま保つ。
後続のtargetがparser ledgerを削除する。
上で定めた一つのCST walkでstructural recovery diagnosticとenvironment conflict diagnosticを導く。
後続のtargetが現在のpublicationを置き換える前に、残るslotごとのschema auditとimplementation migrationが必要である。
