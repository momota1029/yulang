# Doc-comment declaration

## 1. 権限と対象範囲

このページは、`syntax-v0`の`DocCommentDeclaration`のenvelope、Statement dispatch、直接Rowan CST、回復を定める。
Authoritativeな`notes/design/2026-09-01-doc-comment-yumark-addendum.md`と、その明示的なamendmentが統治する。
document内部の構文は[Yumark document grammar](yumark-document.md)で定める。
G12の付与位置は`spec/01-lexical.md`§1.2と`notes/design/2026-11-04-parser-gap-closure-addendum.md`§7に従う。
parserは各documentと構文上の所有者を保存する。
documentの連結、lowering、名前解決、表示は対象外である。

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

先行する`DocCommentDeclaration`はtriviaではなく、独立したdeclarationである。
rootでは`Root`の直接の子になり、入れ子のcanonical statement sequenceでは既存の`Statement`の子になる。
root、brace block、indented block、inline colon bodyが同じcanonical dispatchを使う。
orphan documentも有効である。
宣言の直前の行に置いたdocumentは、その宣言を文書化する。
複数の先行documentはソース順に残る。

marker judgeはcanonical Statementの開始位置で`---`を`--`より先に判定する。
statement base columnで受理されたmarkerは直前のexpression chainを終える。
その位置では宣言済みoperatorより優先される。
same-line semicolonの直後は独立したdoc statementの開始位置ではない。

有効なoperator tableに`--`がない場合、bindingは開始行の式末尾にもline documentを受理する。
同じ行の`=`直後にdocumentを置き、本体を後続行に書く形も受理する。
同じ行で複数のbindingが始まった場合、最後のbindingがdocumentを所有する。
`--`が宣言済みなら、両方の位置でoperatorとして扱う。
継続行、operatorの直後に必要なoperand、括弧やcall引数の内側は従来の解析規則を保つ。

structのfield、enumのvariant、roleのmethod、actのoperationも、直前行と開始行末尾のline documentを受理する。
`=`を持つmemberでは、その直後にも置ける。
完成したfieldやvariantと行末documentの間にcommaがある場合、そのcommaもmember内に残す。
member本体の開始記号と同じ行に続くdocumentは、先行member documentではない。
record typeのfieldは従来の扱いを保つ。

root-leading doc declarationはheader discoveryを`FirstNonHeader`で止める。
その後の`use`やoperator declarationはheaderに入らない。

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

付与するline documentも`DocCommentDeclaration(DocLinePrefix, YmDoc)`を使う。
所有する`BindingStatement`、`StructField`、`EnumVariant`の直接の子になる。
roleのmethodとactのoperationも`BindingStatement`を使う。
bindingの`=`直後のdocumentは`BindingHeader`と`BindingBody`の間に置く。
行末のdocumentは`BindingBody`の後に置く。
本体のないmethod headerでは`BindingHeader`の後になる。
fieldの`=`直後のdocumentは`Equals` tokenの後に置く。
memberの行末documentは、型、payload、default式と、直前のcommaの後に置く。

先行documentは上記の兄弟配置を保つ。
field列とvariant列では、member nodeの直前に置く。
roleとactの本体では、docの`Statement`がmemberの`Statement`に先行する。
両者の間にはblock separatorが入ることがある。
後続の段階は、この木の配置から所有者を特定できる。
先行documentと付与したdocumentは両方ともソース順に残し、parserでは連結しない。
新しい`SyntaxKind`は追加しない。

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

### Bindingとmemberのline document

```yulang
-- leading
my g x = x -- trailing
my h x = -- after equals
    x
struct point {
    x: int, -- x
    -- y
    y: int,
}
```

`g`の二つのdocumentは順番を保つ。
`=`直後のdocumentは`h`に属し、fieldのdocumentはそれぞれ`x`と`y`に属する。
block documentは既存の先行位置のenvelopeとdispatchを保つ。

## 7. 構成と非対象

document bodyは[Yumark document grammar](yumark-document.md)と構成する。
[構文の内容モデル](../conventions/syntax-content-model.md)、[Rowan CST表記](../conventions/rowan-cst.md)、[回復のtopology](../conventions/recovery-error-invalid-topology.md)も参照する。
documentは意味上のmemberを追加せず、宣言の評価を変えない。
先行documentは兄弟の位置を保ち、付与したline documentは§4の所有者の子になる。
