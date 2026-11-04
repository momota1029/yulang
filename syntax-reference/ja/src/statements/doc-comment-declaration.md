# Doc-comment declaration

## 1. 権限と対象範囲

このページは、`syntax-v0`の`DocCommentDeclaration`のenvelope、Statement dispatch、直接Rowan CST、回復を定める。
Authoritativeな`notes/design/2026-09-01-doc-comment-yumark-addendum.md`と、その明示的なamendmentが統治する。
document内部の構文は[Yumark document grammar](yumark-document.md)で定める。
doc commentと後続宣言を結び付ける意味論、lowering、名前解決、表示は対象外である。

## 2. 受理する構文

```text
DocCommentDeclaration := LineDocComment | BlockDocComment
LineDocComment := "--" InlineDocument(LineDocMode)
BlockDocComment := "---" H* PhysicalNewline
                   BlockDocument(BlockDocMode)
                   RecoveredBlockDocClose
RecoveredBlockDocClose := DocBlockClose | Missing(DocComment, ClosingDelimiter)
DocBlockClose := LineStart "---" H* (PhysicalNewline | EOF)
```

`H`はspaceまたはtabである。
markerの後のhorizontal triviaとphysical newlineは受理条件に含まれるが、marker tokenがcommitするのは`--`または`---`のbytesだけである。
line formは最初のphysical newlineを所有しない。
block closeもsuffixのhorizontal triviaとnewlineを所有せず、outer statement sequenceへ返す。

## 3. Admission、dispatch、境界

`DocCommentDeclaration`はtriviaではなく、独立したdeclarationである。
rootでは`Root`の直接の子になり、入れ子のcanonical statement sequenceでは既存の`Statement`の子になる。
root、brace block、indented block、inline colon bodyが同じcanonical dispatchを使う。
orphan documentも有効である。

marker judgeはcaller-owned leading triviaの後で動き、canonical Statementの開始位置だけでdynamic operatorより先に選ぶ。
`---`を`--`より先に判定する。
statement base columnで受理されたmarkerは直前のexpression chainを終え、その位置では宣言済みoperatorより優先される。
expressionのNUD、LED、その他のnon-statement位置ではこの優先順位を使わず、同じspellingのuser-declared operatorが従来どおり動く。
same-line semicolonの直後は新しいdoc statementの開始位置ではない。

root-leading doc declarationはheader discoveryを`FirstNonHeader`で止める。
その後の`use`やoperator declarationはheaderに入らない。
struct、enum、record、role、actのfield列とowner固有の列はdoc declarationを受理しない。

block openerとcloseは、physical line start、opening base column、exact `---`、horizontal suffixだけ、という条件をすべて満たす。
`---x`、`----`、mid-lineの`---`、opening line上のclose-like text、異なるindentのmarkerはenvelope markerではない。
`//`と`/* ... */`はordinary Yulang commentのままである。

## 4. Source-order Rowan schema

```text
LineDocComment := DocCommentDeclaration(
  DocLinePrefix,
  YmDoc
)

BlockDocComment := DocCommentDeclaration(
  DocBlockOpen,
  Whitespace?,
  Newline,
  YmDoc,
  DocBlockClose | Missing
)
```

direct CSTはneutral Yumark grammarから同じbuilderへstreamし、AST event listをbuildまたはreplayしない。
source textはtriviaとrecoveryを含めてlosslessに保存する。
root formに合成`Statement`を加えず、nested formだけが既存の`Statement` wrapperを持つ。

## 5. Recovery CST

unterminated block docはEOFにちょうど一つのzero-width `Missing`を置く。
typed identityは`YumarkOwner::DocComment`と`YumarkSlot::ClosingDelimiter`である。
close-like textがstrict closeでなければtextとしてdocumentに残り、その場ではMissingを置かない。

```xml
<DocCommentDeclaration>
  <DocBlockOpen text="---" /><Newline text="\n" />
  <YmDoc><YmParagraph><YmText text="body" /></YmParagraph></YmDoc>
  <Missing />
</DocCommentDeclaration>
```

Yumark内部のrecoveryは、それぞれのsection、list、quote、fence、inline、command ownerに残る。
同じ原因についてdoc envelopeがinner recoveryを重複させない。

## 6. SourceとCSTの例

```yulang
-- line *document*
my value = 1
---
# Heading
- item
> quote
---
```

最初のnewlineはline declarationの外側にある。
block formではopening newlineがdeclaration内にあり、closing `---`の後のnewlineはouter statement sequenceにある。

## 7. 構成と非対象

document bodyは[Yumark document grammar](yumark-document.md)と構成する。
[構文の内容モデル](../conventions/syntax-content-model.md)、[Rowan CST表記](../conventions/rowan-cst.md)、[回復のtopology](../conventions/recovery-error-invalid-topology.md)も参照する。
doc declarationはfield member、declaration attachment、後続宣言のsynthetic childを追加しない。
