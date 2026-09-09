# 回復の`Error` tokenと`Invalid` nodeのtopology

このページは、lossless Rowan CSTに実装済みの回復topologyを定める。
対象はsource shapeだけである。
grammar slot、expected syntax、public diagnostic resultは定めない。

## Raw malformed source

raw recoveryは、所有するすべてのphysical source fragmentを`Error` token leafとしてemitする。
structuralな`Error` nodeは作らない。

```xml
<Error text="@" />
<Error text="/*bad*/" />
```

隣接する`Error` leafは、source orderで一つのopaque malformed runを構成できる。
このleaf列はrunの内部に文法を作らない。
leafの数はdiagnosticの数ではない。

raw modeは、interior trivia、Yumark quote-prefix fragment、same-line EOF leading、2つのconsumed retry-leading prefixを含め、残るphysical fragmentを`Error`としてemitする。
owning productionが既にemitしたtriviaはrunの外に残る。
retryまたはboundary ownerに残すleading triviaもrunの外に残る。
raw recoveryの外側にあるaccepted tokenと通常のtriviaはnative token kindを保つ。

## Structured recovery

`Invalid`は対になったRowan nodeである。
nested grammar、`Missing` child、または`Error` childを残すstructured recoveryだけに使う。
通常のraw `Error` tokenを包んではならない。

このtopology gateで`Invalid`をemitできるstructured ownerは、次の2つだけである。

- polymorphic-variant tag-name recovery
- record-pattern wrong-kind itemまたはseparator recovery

次はconstruct schemaではなくtopologyの概略である。

```xml
<Invalid>
  <Error text="@" />
  <Missing />
</Invalid>
```

`Invalid`はnested source orderとnested recovery elementを保つ。
ほかのownerが類推だけで`Invalid` nodeを加えてはならない。

## Missingとdiagnostic publication

`Missing`は、含むgrammar slotに置くzero-widthのstructural nodeのままである。
`Error` tokenと`Invalid` nodeへのmigrationは、recovery ownershipと既存のparser diagnostic machineryを変えない。
parser recovery record、structured reservation、frozen-header reconciliation、diagnostic ID、public diagnostic constructionは、一時的なcompatibility machineryとして残る。

CST walkからdiagnosticを導き、そのcompatibility machineryを削除する前に、完全なslotごとのschemaが必要である。
[Source root、header、diagnosticの責務](source-root-and-diagnostics.md)は、その後続のboundaryを定める。

## 表記とrange

このページのtagは、runtime XMLではなくXMLに似たRowan表記を使う。
各`Error` leafは、`text` attributeにsource spellingを持つ。
[Rowan CST表記](rowan-cst.md)は、可逆なattribute escapeとUTF-8 byte rangeを定める。
