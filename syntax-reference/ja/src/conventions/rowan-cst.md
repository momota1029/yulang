# Rowan CST表記

このページは、Yulangのlossless Rowan CSTに使う表記とsource ownershipの規約を定める。
対象は、受理する`syntax-v0`のgrammarとdirect Rowan topologyである。
実装の経緯ではなく、参照用の規約を示す。

## Authorityと対象範囲

Authoritativeな*Syntax freeze and vertical-implementation completion-policy amendment*（2026年9月17日）は、受理するgrammar、recovery ownership、direct Rowan topologyを`syntax-v0`として保持する。
Authoritativeな*Rowan CST-only successor amendment*と*Error-token and Invalid-node topology ordering addendum*は、ここで使うone-CSTとrecovery topologyの規約を定める。

構文ページは受理するspellingとordered child grammarを定める。
このページはconstruct productionとdiagnostic wordingを定めない。

## 文書上の表記

この表記はXMLに似た文書記法である。
runtime XMLでもinterchange formatでもない。
対になったtagはRowan nodeを表す。
`text` attributeを持つself-closing tagは、sourceを持つtoken leafを表す。

```xml
<OperatorChain>
  <PrefixOperator text="!" />
  <Missing />
</OperatorChain>
```

structural nodeの間にはbare character dataを置かない。
sourceを持つleafは`text`にspellingを置く。
そのため、indentationやleafの外側にあるtextはsource byteを表さない。

`text` attributeは可逆なsource spellingを表す。
この文書記法はXML entityを使わない。
次のcanonical backslash escapeを使う。

| Source character | `text` spelling |
| --- | --- |
| reverse solidus | `\\` |
| quotation mark | `\"` |
| carriage return | `\r` |
| line feed | `\n` |
| horizontal tab | `\t` |
| ほかのU+0000--U+001F control character | four uppercase hexadecimal digitsを使う`\u{XXXX}` |

それ以外のUnicode scalar valueはliteralに書く。
decodeは正確である。
visual notationではなく、decode後のspellingがleafのUTF-8 byte rangeを決める。
したがってCRLFとLFは区別され、literalな`\r`とcarriage returnも区別される。

## Source orderとlosslessness

nodeとtoken leafはsource orderで現れる。
sourceを持つleafは完全なsource spellingを保つ。
structural nodeは表現されないsource textを追加しない。
sourceを持つleafを左から右へ読めば、sourceを正確に復元できる。

malformed runの外側にある通常のtriviaは、そのproductionが所有するsource-bearing leafとして残る。
raw malformed runに吸収されたtriviaは`Error` leafで表す。
construct schemaは各tokenとtrivia leafを一つのgrammar slotへ割り当てる。
このページはconstructごとのslotを割り当てない。

## Recovery element

`Missing`は、文書化されたgrammar slotに置くzero-widthのstructural nodeである。
`text` attributeを持たず、source byteを追加しない。

```xml
<OperatorChain>
  <PrefixOperator text="!" />
  <Missing />
</OperatorChain>
```

`Error`は常にtoken leafであり、nodeではない。
各`Error` leafは、owner slot内で既にemitされたphysical source fragmentを表す。
隣接するleafは、一つのraw malformed runを構成できる。
そのrunは内部のgrammarを作らない。

```xml
<Error text="@" />
<Error text="/*bad*/" />
```

raw recoveryは、そのitemに残るすべてのphysical fragmentを`Error`に対応付ける。
これにはinterior triviaとYumark quote-prefix fragmentを含む。
owner productionが既にemitしたleading triviaと、retryまたはboundary ownerに残るleading triviaは吸収しない。

`Invalid`は、nested grammar、`Missing` child、または`Error` childを残す、schemaで定めたrecoveryのstructural nodeである。
通常のraw `Error` tokenを包んではならない。

```xml
<Invalid>
  <Error text="@" />
  <ParenthesizedTypeGroup>
    <Missing />
  </ParenthesizedTypeGroup>
</Invalid>
```

[回復の`Error`と`Invalid`のtopology](recovery-error-invalid-topology.md)は、`Invalid`を使える限定したstructured ownerを定める。

## Source coordinate

tree rangeとdiagnostic rangeは、0始まりで終端を含まないUTF-8 byte rangeを使う。
`Missing`のrangeはzero-widthである。
sourceを持つleafは保ったspellingからrangeを決める。
structural nodeはsource textを追加しない。

## Diagnosticの境界

CSTはstructural recoveryを保持する。
selected syntax environmentは、そのstructureを変えずに別個のenvironment factを与える。
どちらも第二のCSTを作らない。
