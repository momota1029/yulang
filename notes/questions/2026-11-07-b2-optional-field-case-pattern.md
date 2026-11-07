# optional fieldをdefaultなしのcase patternで照合できるか

状態: 要確認。既存の構造Common判断は後述の選択肢2に相当する。full B2の判断へどちらを採用するかは未承認。

## 根拠と境界

- [spec/03b-patterns.md §3b.3](../../spec/03b-patterns.md) は「明示した field は、default がなければ必須」とする。
- 同節は、defaultは型の上でoptionalなfieldにだけ書け、patternのdefaultはfieldをoptionalとして推論させるとする。
- 同節と [spec/03-expressions.md §3.7](../../spec/03-expressions.md) は、書かれた順に照合し、合わなければ後続armへ進む。
- 実 `ScopedCasePatterns.run` はdefaultなしfieldが欠けていればmissを返す。一方、部分的な独立
  `CommonPatternTyping.Typing.field` / `CommonAlignedPatternTyping.RawTyping.field` は、input全体が
  `required name payload` 以下であることを要求するため、型付き入力でこの欠損missを使う場合を含まない。
  この判断はfull B2ではないことを既に明記している。

## 問い

次のcaseは合法か。`config`の型注釈は既にoptionalで、defaultの推論による変更はないものとする。

```yulang
my read_port(config: {port?: int}): int = case config:
    {port: p} -> p
    _ -> 80
```

1. **推奨: 合法。** 「defaultなしfieldは必須」は、そのpatternが成功するためにfieldの存在が必要という意味。
   optional入力では欠けていればmissし、後続armへ進む。存在時にはoptional payload型で束縛する。
   関数引数や`my`のirrefutable制約は別途保ち、このpatternをそれらへ無条件に許可しない。
2. 第一armを型エラーにする。defaultなしfield patternは、入力型の全値でそのfieldがrequiredな場合だけ型付ける。
   optional fieldの値を取り出す際はdefaultを要求する。

required fieldにdefaultを書けるかという既存規則は、この問いで変更しない。

## 証明側への影響

選択肢1では、defaultなしfieldの独立case pattern規則に、存在時payloadを拘束する
`OptionalPayload name input payload` と欠損時missの枝を使う。選択肢2の既存required規則は保存できる。
どちらでも実matcherとQ4累積環境の順序は変わらない。

承認前に元のfull B2 statementや既存判断を変更しない。workerは既存required規則の証明を保ち、
optional入力を許す局所規則と有限生成・部分正当性を別名の補題として進める。

## 追加のkernel検証

`CommonOptionalFieldBoundary` は `exactEmpty | required(0,int)` 入力・`{0: x}` patternで二つの規則を区別する。
`strict_rejects` は任意元types/default判断/結果bindingsについて既存required規則では導出不能、
`permissive_typed` は同じ任意元環境/default判断でoptional局所規則を導出する。
`generated_model` / `real_scheme_instance` は後者の実finite制約のmodelと実返却scheme/parameterが存在すること。
`actual_empty_miss` はどちらの型規則でも変更していない実matcherが空recordでmissすることを示す。
この局所差は元のfull B2 statementの反証ではなく、未承認の意味選択の正確な境界である。
