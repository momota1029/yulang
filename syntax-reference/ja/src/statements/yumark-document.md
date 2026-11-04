# Yumark document grammar

## 1. 権限と対象範囲

このページは、doc-comment declarationの内部で使う`syntax-v0` Yumark grammarを定める。
Authoritativeな`notes/design/2026-09-01-doc-comment-yumark-addendum.md`、`notes/design/oracles/2026-09-01-yumark-draft.md`、および後続amendmentが統治する。
envelopeとStatement dispatchは[Doc-comment declaration](doc-comment-declaration.md)で定める。
rendering、macro expansion、document attachment semanticsは対象外である。

## 2. Block grammar

```text
YumarkDocument := YumarkBlock*
YumarkBlock := BlankLine | Section | List | Quote | CodeFence
             | Paragraph | Command | My | Use | IfChain
```

section headingはline startの`#`列で始まる。
implicit sectionは同じlevel以上の次のsection boundaryまでをbodyにする。
terminal `:`を持つexplicit sectionはstrictly deeperなbodyを要求し、対応するsection closeを持てる。

list itemはmarkerと一つの`YmListItemBody`を持つ。
sibling marker、dedent、parent boundaryがitem bodyを終える。
quoteはprefix formとexplicit fenced formを持ち、depthとopener columnがcloseを決める。
blank lineは`YmBlankLine`として保持し、ordinary text lineの連続は`YmParagraph`になる。

## 3. Inline grammar

```text
YumarkInline := Text | Group | Link | Image | Apply | Reference
              | Emphasis | Strong
```

`[...]`はinline group、`[label](destination)`はlink、`![label](destination)`はimageである。
`*...*`と`**...**`はemphasisとstrongであり、longest-firstで選ぶ。
inline applyとreferenceはdocument argumentまたはYulang argumentを持てる。
line-doc modeはblock starterを無効にし、最初のphysical newlineで終わる。

## 4. Raw fence

triple-backtick openerはmarker、info、opening newline、raw text、recovered closeを持つ`YmCodeFence`を作る。
raw bodyではYumark inline grammarもYulang grammarも動かない。
closeはopener columnにあるexact triple backtickだけである。

infoの最初のatomがexact `yulang`のfenceは、後続のparsed-Yulang amendmentが選ぶ特別なformである。
そのbodyをcanonical Yulang adapterへ収束させる処理はO6 gateへdeferされており、Gate 6はbody factを捏造しない。

## 5. Commands、`do`、`\if`、`\my`、`\use`

general commandはbackslashとnameで始まり、Yulang argumentとdocument argumentをソース順に持てる。
immediate document argument、`do`、local body、またはYulang argument後のdocument/bodyがpromotion formを決める。
local bodyはbraced documentまたはstrictly indented documentである。
`do` captureはinitiating commandの`YmDoCapture`となり、後続のsibling blocksをソース順に所有する。

`\if`は`YmIf`、0個以上の`YmElsif`、任意の`YmElse`を持つ`YmIfChain`を作る。
conditionは`YmIfCondition`または`YmElsifCondition`の中のcanonical Yulang expressionである。
各branch bodyはlocal Yumark documentであり、branch boundaryはinner bodyにconsumeされない。

`\my`はbareまたはparenthesized headを持つ。
headは`YmMyBindingHead`内のcanonical `Pattern`である。
bodyはinline expression、indented expression、braced document、indented documentのいずれか一つである。
`\use`はparenthesizedまたはsemicolonで終わるbare formを持ち、canonical `UseTree`を所有する。

## 6. Embedded Yulangの所有権

Yumarkはcanonical Yulangを次のclosed adapter homeだけに置く。

| Yumark owner | canonical Yulang child |
| --- | --- |
| `YmYulangArgs` | command/reference call arguments |
| `YmInlineApplyArgs` | inline-apply arguments |
| `YmMyBindingHead` | `Pattern` |
| `YmMyExpressionBody` | `OperatorChain` |
| `YmUse` | `UseTree` |
| `YmIfCondition`, `YmElsifCondition` | condition `OperatorChain` |

embedded Yulangは新しいpublic `Root`、`Statement`、declaration dispatchを開かない。
raw fence、`YmDocArg`、plain textではYulang parserを起動しない。
delimiterはYumark wrapperが一度だけ所有し、canonical childは同じcloseのMissingを重複させない。

## 7. Source-order Rowan schema

`YmDoc`はrecovered blockをソース順に持つ。
主要な直接child順は次のとおりである。

| form | 直接child順 |
| --- | --- |
| section | heading、implicit/explicit `YmDoc` body、任意のsection close |
| list item | marker、`YmListItemBody` |
| quote | opener/prefix、document、explicit formだけrecovered close |
| raw fence | open marker、info、opening newline、raw text、recovered close |
| general command | head/arguments、任意の`YmCommandBody`、任意の`YmDoCapture` |
| `\my` | `YmMyBindingHead`、exactly one body form |
| `\use` | backslash/name、route、bare formではterminating semicolon |
| if-chain | `YmIf`、`YmElsif`*、`YmElse`? |

direct CSTは一つのiterative grammarからstreamされる。
section、list、quote、group、body、argumentのnestingは明示的なframe stackを使い、Rust recursionのdepth limitを言語制限にしない。

## 8. Recovery vocabulary

recovery nodeはgeneric `Missing`または`Error`である。
typed identityは`YumarkOwner`と`YumarkSlot`の組で保持する。

```text
YumarkOwner := DocComment | Section | List | ListItem | Quote | CodeFence
             | InlineGroup | InlineLink | InlineImage | InlineApply
             | InlineReference | Emphasis | Strong | Command | My | Use
             | DocArgument | DoCapture | IfChain | IfBranch | ElsifBranch
             | ElseBranch

YumarkSlot := Starter | Name | Head | Arguments | Condition | BodyIntroducer
            | Body | Destination | BranchPredecessor | ClosingDelimiter
            | SectionClose | QuoteForm | ExpressionBody | Route | Terminator
```

missing delimiterはzero-width `Missing`である。
malformed raw runはactive frameのsafe stopまでのnon-empty `Error`である。
safe stopはnewline、active close、block-doc close、quote boundary、list sibling/dedent、fence close、command-body boundary、EOFである。
一つのcommitted recovery recordは同じrangeのgeneric recovery node一つを作る。

## 9. 例と構成

````yulang
---
# Section
- first
- second with **strong** and [link](target)
> quote
\note[document argument]
\if(condition){shown}\else{fallback}
```text
raw *not emphasis*
```
---
````

Yumark documentは[Doc-comment declaration](doc-comment-declaration.md)のlineまたはblock envelopeだけから到達する。
[構文の内容モデル](../conventions/syntax-content-model.md)と[回復のtopology](../conventions/recovery-error-invalid-topology.md)も参照する。
