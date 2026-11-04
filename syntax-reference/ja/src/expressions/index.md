# Expressions

Expressionの文脈と記録済みの全ファミリーは、[構文の内容モデル](../conventions/syntax-content-model.md)で確認する。次のページは、詳細化済みの形式の配置と生成規則を定める。

## Identifierのprimary form

`IdentifierExpression`はoperand位置にある通常のidentifier、参照sigil identifier、またはlabel identifierを記録する。

```text
IdentifierPrimary := Identifier | ReferenceSigilIdentifier | LabelIdentifier
ReferenceSigilIdentifier := ("$" | "&") ! Identifier
LabelIdentifier := "'" ! Identifier
```

`!`はsigilとidentifierの間にtriviaを置かず、隣接させることを表す。
直接CSTは`Identifier`または`SigilIdentifier` token一つを持つ`IdentifierExpression`である。
operandの後でLED演算子を選択するとき、宣言済みの`&`はsigil identifierを開始せず、演算子candidateのままになる。
単独のsigilとidentifierに隣接しないsigilはidentifier primaryではない。

```yulang
$count
&count = $count + 1
last 'outer
'done.return 42
```

- [Parenthesized primary form](parenthesized-expression.md)
- [List-expression primary form](list-expression.md)
- [数値リテラルのprimary form](numeric-literals.md)
- [Operator-chainによる式](operator-chain.md)
- [Assignmentのterminal form](assignment-tail.md)
- [Colon applicationのterminal form](colon-application.md)
- [`if` / `elsif` / `else`のprimary form](if-expression.md)
- [Braceで囲むstatement blockのprimary form](braced-statement-block.md)
- [`case` / `catch`のprimary form](case-catch.md)
- [Call、field、path、ML-applicationのcontinuation form](call-field-path-tails.md)
- [Index、projectionのcontinuation form](index-projection-tails.md)
- [`with` bodyのterminal form](with-body-tail.md)
