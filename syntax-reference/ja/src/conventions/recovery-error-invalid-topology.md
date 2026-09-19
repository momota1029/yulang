# 回復の`Error`と`Invalid`のtopology

このページは、lossless Rowan CSTにおける`syntax-v0`のrecovery topologyを定める。
保持するsource structureを対象とする。
malformed sourceを受理するgrammar、grammar slot、expected alternative、public diagnostic wordingは定めない。

## Authorityと対象範囲

Authoritativeな*Syntax freeze and vertical-implementation completion-policy amendment*（2026年9月17日）は、`Missing`、raw `Error`、structured `Invalid`をrecovery factとして保持する。
Authoritativeな*Error-token and Invalid-node topology ordering addendum*は、それらのtopologyを定める。
これらの規約はaccepted-inputとrecovery-ownership contractを保持する。

## Raw malformed source

raw recoveryは、所有するすべてのphysical source fragmentを`Error` token leafとしてemitする。
structuralな`Error` nodeは作らない。

```xml
<Error text="@" />
<Error text="/*bad*/" />
```

隣接する`Error` leafは、source orderで一つのopaque malformed runを構成できる。
runの内部にgrammarを作らない。
leafの数はdiagnosticの数ではない。

raw recoveryは、interior trivia、Yumark quote-prefix fragment、same-line EOF leading、2つのconsumed retry-leading prefixを含め、残るphysical fragmentを`Error`としてemitする。
owning productionが既にemitしたtriviaはrunの外に残る。
retryまたはboundary ownerに残すleading triviaもrunの外に残る。
raw recoveryの外側にあるaccepted tokenと通常のtriviaはnative token kindを保つ。

## Structured recovery

`Invalid`は、nested grammar、`Missing` child、または`Error` childを残すrecoveryのstructural Rowan nodeである。
通常のraw `Error` tokenを包んではならない。

`Invalid`をemitできるstructured ownerは、次のものに限る。

- Polymorphic-variant tag-name recovery。
- Record-pattern wrong-kind itemまたはseparator recovery。

次はconstruct schemaではなくtopologyの概略である。

```xml
<Invalid>
  <Error text="@" />
  <Missing />
</Invalid>
```

`Invalid`はnested source orderとnested recovery elementを保つ。
ほかのownerが類推だけで`Invalid` nodeを加えてはならない。

## Structural diagnostic interpretation

実装済みのshadow CST interpreterは、CSTからstructural recoveryをsource orderで読む。
`Missing` occurrenceにはzero-width rangeがある。
同じslotとimmediate parentにあるraw `Error` tokenの最大隣接列は、一つのmalformed-input occurrenceである。
通常のtrivia、`Missing`、nested node、slot boundaryが列を終える。
`Invalid` occurrenceはchildより前にvisitする。
validなnested syntaxを含む場合もouter rangeを保つ。

cataloged occurrenceはprecise schema-derived interpretationを使える。
それ以外のoccurrenceはCST factだけから決まるdeterministic generic interpretationを使う。
使うfactはrecovery kind、range、occurrence pathまたはimmediate structural parent、source/preorder ordinalである。
interpreterはparser recovery recordを読まず、parseをreplayせず、opaqueな`Error`をrelexせず、hidden recovery episodeを推論せず、recovery nodeを作らない。

environment-only factは、`Invalid`を加えず、ほかの方法でもCSTを変更しない。

## Publicationの状態

shadow interpreterは実装済みである。
public syntax diagnosticは、atomic diagnostic migrationであるGate 4が実施待ちの間、一時的なparser ledgerを使う。
Gate 4にはtotalでdeterministicなCST-derived interpretationが必要である。
ledger retirementの前にexhaustiveなslotごとのprecisionは必要ない。

[Source root、header、diagnosticの責務](source-root-and-diagnostics.md)はrootとpublication boundaryを定める。
[Rowan CST表記](rowan-cst.md)は可逆な`text` spellingとUTF-8 byte rangeを定める。
