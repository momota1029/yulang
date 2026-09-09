# Rowan CST表記

このページは、Yulangのlossless Rowan CSTを表す記法を定める。
これはAuthoritativeなtarget specificationである。
`rowan::GreenNodeBuilder`によるdirect constructionは実装済みである。
`Error` token、`Invalid` node、CST由来diagnosticは承認済みだが、実装待ちのgateである。

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
そのため、indentationやleafの外側にある通常のtextはsource byteを表せない。

`text` attributeは可逆なsource spellingを表す。
この文書記法はXMLではないため、XML entityを使わない。
次のcanonical backslash escapeを使う。

| Source character | `text` spelling |
| --- | --- |
| reverse solidus | `\\` |
| quotation mark | `\"` |
| carriage return | `\r` |
| line feed | `\n` |
| horizontal tab | `\t` |
| ほかのU+0000--U+001F control character | 4桁の大文字hexadecimal digitを使う`\u{XXXX}` |

それ以外のUnicode scalar valueはliteralに書く。
attributeのdecodeは正確である。
visual notationではなくdecode後のspellingがleafのUTF-8 byte rangeを決める。
そのためCRLFとLFは区別され、literalな`\r`とcarriage returnも区別される。

## Node、token、trivia

nodeはstructuralなCST elementであり、対になったtagで表す。
token leafはsourceを持つCST elementであり、`text`を持つself-closing tagで表す。
childはsource orderで現れる。

malformed runの外側にある通常のtriviaは、owner productionのsourceを持つ独立したleafとして残る。
raw malformed runに吸収されたtriviaは、代わりに`Error` leafで表す。
schemaは各tokenとtrivia leafを一つのgrammar slotへ割り当てなければならない。
このページは構文ごとのslotを割り当てない。

## Recovery element

`Missing`は、文書化されたgrammar slotに置くzero-widthのstructural nodeである。
`text` attributeを持たず、source byteを追加しない。

```xml
<OperatorChain>
  <PrefixOperator text="!" />
  <Missing />
</OperatorChain>
```

`Error`は承認済みで実装待ちのtoken topologyである。
`Error`は常にtoken leafであり、nodeではない。
各leafはowner slot内で既にemitされたphysical source fragmentを表す。
隣接するleafは一つのraw malformed runを構成できる。
そのrunは内部のgrammarを作らない。

```xml
<Error text="@" />
<Error text="/*bad*/" />
```

raw recoveryは、そのItemに残るすべてのphysical fragmentを`Error`に対応付ける。
これにはinterior triviaとYumark quote prefixを含む。
owner productionが既にemitしたleading trivia、retryまたはboundary ownerに残るleading triviaは吸収しない。

`Invalid`は承認済みで実装待ちのnode topologyである。
schemaで定めたstructured recoveryがnested grammar、`Missing`、nested `Error` childを保持するときだけ使う。
通常のraw `Error` tokenを`Invalid`で囲んではならない。

```xml
<Invalid>
  <Error text="@" />
  <ParenthesizedTypeGroup>
    <Missing />
  </ParenthesizedTypeGroup>
</Invalid>
```

## Source coordinate

tree rangeとdiagnostic rangeは、0始まりで終端を含まないUTF-8 byte rangeを使う。
`Missing` nodeのrangeはzero-widthである。
sourceを持つleafはrangeを決めるsource spellingを保存する。
structural nodeは表現されないsource textを追加しない。

## 現在と実装待ちのtopology

direct Rowan builderは実装済みのconstruction pathである。
現在のCSTにはstructuralな`Error` nodeと、parserが公開するrecovery diagnosticが残る。
承認済みのtargetは、そのrecovery shapeを`Error` token leafと限定した`Invalid` nodeへ置き換える。
その後、structural diagnosticをCSTから導く。
[Source root、header、diagnosticの責務](source-root-and-diagnostics.md)は、そのtargetのpublication boundaryを定める。
