# 未決定の問い（2026-11-06）

ここにある選択肢は仕様の決定ではない。推奨は先頭に置く。
既存の決定を広げず、回答に依存しない核と証明を先に進める。

## Q1. operation の payload pattern が非網羅の catch を許すか

状態: **未回答**。出典: `spec/03-expressions.md` 3.8、`spec/05-effects.md` 5.2。
operation arm の payload pattern と value arm は書けるが、operation ごとの
payload が非網羅のときの扱いは、現在の記述から確定できない。

例（構文の説明用。parser/oracle 実行はしていない）:

```yulang
act ask:
    our choose: bool -> int

catch action:
    ask::choose true, k -> k 1
    v -> v
// action が ask::choose false を起こす場合
```

- **A（推奨）:** 扱う operation ごとに payload pattern の網羅性を静的に要求する。
  guard 付き arm を網羅に数えず、非網羅なら拒否する。網羅できた operation key のみ行から引く。
- **B:** 非網羅の payload arm も許す。合う arm がない要求は元の継続とともに外へ渡し、
  その operation key を残余行に残す。

影響する義務: source arm の operation ごとの編成、payload pattern の網羅性、
source `catch` から `MultiOperationHandlerTyping.Expr.handler` への翻訳、行の残余の健全性。
同じ operation の arm が複数あることを、一律に拒否する仕様は追加していない。

この回答に依存せず証明した範囲: 相異なる解決済み operation key ごとに一つの全域な body を持つ
有限表の実行・独立型付け・checker の一致、shallow/multi-shot、許可 mask と符号付き重み。
表の key 一意性はこの核の表現条件であり、source payload arm の意味の決定ではない。

## Q2. 小数 literal の float はどの精度と丸めを持つか

状態: **未回答**。`spec/03-expressions.md` 3.1 は整数を任意精度、小数 literal を `float` とするが、
float の精度・丸めは書いていない。今回の依頼の「任意精度の整数・小数」が、小数にも任意精度を
要求するかを含めて決める必要がある。旧 `Inference.Base` には float 自体がまだない。

例: `0.1`、`9007199254740993.0`、非常に大きい指数を持つ小数。
仮数を全部保存することと、評価後の数値に丸めがないことは異なる。

- **A（推奨。通常の float と実装の小ささを優先する場合）:** IEEE 754 binary64。
  有限の範囲内の literal は最近接・偶数丸め。小数も任意精度という要求なら、この案は採らない。
- **B:** 有限小数を任意精度の十進数として正確に保持する。割算等の非有限小数の規則は別に定める。
- **C:** 任意精度浮動小数とし、精度・丸め context を持つ。context の渡し方も必要になる。

影響する義務: `LiteralValues.ofDecimal` の具体化、Lean/Rust oracle の値codec、
数値演算、float literal の解釈の一致。比較規則は精度と独立に次の問いへ分ける。
現在どの案も採用していない。`DecimalToken` と明示的な解釈引数だけを追加し、
整数・文字列・bool・unit と整数範囲の証明を先に閉じた。

## Q3. float literal pattern の比較は数値比較か、表現の一致か

状態: **未回答**。Q2の精度とは別の問い。
例: `0.0` のpatternは `-0.0` に合うか。選んだfloatモデルにNaNがある場合、NaN同士は合うか。

- **A（推奨）:** 選んだfloatの数値比較に合わせる。IEEEモデルなら正負の零は等しく、NaNは自分にも一致しない。
- **B:** 保存表現の一致にする。IEEEモデルならbit patternを比較し、正負の零を区別する。
- **C:** float literal pattern を静的に拒否し、必要ならguardで比較する。

影響する義務: `LiteralValues.matchCheck` のfloat比較、独立関係 `Matches` の具体化、
float patternの網羅性。保存値の構造的な等号 `eqCheck` と、言語のpattern比較は区別する。
現在は比較関数と関係の正確性を明示的な引数に取り、反射性を仮定しない。
整数・文字列・bool・unitの比較はこの回答に依存せず閉じている。

## Q4. record pattern のdefaultから、同じpattern内の束縛が見えるか

状態: **未回答**。`spec/03b-patterns.md` 3b.3 は欠如時の評価を定めるが、default式の名前のscopeを定めていない。
決定43の評価順だけから、束縛が見える範囲までは拡張して決めない。

例（`outer` の値が10の場合）:

```yulang
my outer = 10
case { x: 3 }:
    { x: outer, y: result = outer } -> result
```

- **A（推奨）:** defaultはpatternの外側のlexical環境を見る。同じpattern内の新しい束縛はguard/bodyから見える。例は10を返す。
- **B:** それまでに照合して束縛した名前もdefaultから見える。例は3を返し、fieldの記述順が名前解決にも影響する。
- **C:** 同じpattern内の名前をdefaultが参照すること自体を禁止し、外側と同名の場合も明示的な別名を要求する。

影響する義務: `CaseDataTerms.defaultEval` に渡す環境のsource elaboration、nested pattern、or patternの各枝、
default式の型環境、effectを持つdefaultの意味保存。現在の核はdefault evaluatorを明示的に受け取り、
具体data wrapperの外側環境も引数で指定する。これはAをsourceの仕様に採用したという意味ではない。
既存の「presentなら評価しない」「absentなら観測を保って評価する」証明と、局所default契約からのcase安全性は、
sourceがどの環境を選ぶかの回答に依存しない。

## Q5. patternの先行不一致で、後に書いたdefaultの評価を省略するか

状態: **未回答**。`spec/03b-patterns.md` 3b.3 は欠如時のdefault評価を定め、
決定43は実行する式の順序を定めるが、先行patternのmiss後も評価を続けるかは書いていない。

例（`log 1` は観測を残して1を返す式の説明用記法）:

```yulang
case { y: 1 }:
    { y: 0, x = log 1 } -> 10
    _ -> 20
```

- **A（推奨）:** patternを記述順に照合し、先行部分のmissでそのarmの残りを打ち切る。例では`log 1`を実行しない。
- **B:** armに入ったら欠けたfieldのdefaultを記述順にすべて評価してから、pattern全体の成否を決める。例でも`log 1`を実行する。

影響する義務: effectful defaultの訪問列、複合pattern/or patternの失敗時の実行、
LeanとRust oracleの差分テスト、sourceから`CasePatterns.run`への意味保存。
**仮:** 現在の解決済み照合核はAで実装し、その評価器についてのみ順序・型安全性を証明する。
Aをsource仕様の決定とは扱わない。既存のdefault訪問例は先行missを含まないため、この回答を先取りしない。

## Q6. or patternの枝を、照合成功時に確定するか、guardまで含めて試すか

状態: **未回答**。`spec/03b-patterns.md` 3b.1/3b.6/3b.6′は選択・名前集合・asの結合力を定めるが、
普通のor patternで複数の枝が合う場合の選択とguard失敗時の再試行は明記していない。
`spec/09-parser-dsl.md` 9.3のparser選択のbacktrack規則は、普通のpatternへ拡張しない。

```yulang
case (1, 2):
    (x, _) | (_, x) if x == 2 -> x
    _ -> 0
```

- **A（推奨）:** 左から照合し、最初に合った枝の束縛でguardを一度評価する。guardが偽なら次のarmへ進む。例は0。
- **B:** 左からguardまで含めて試す。左のguardが偽なら右を試し直す。例は2。

影響する義務: orの束縛の選択、guard/defaultの実行回数と訪問列、CaseEvaluationとRust oracleの一致、
sourceのor patternから解決済み核への翻訳。guard付きarmを網羅性に数えない決定は、どちらでも変更しない。
**仮:** 現在の核はA。名前集合の一致・asの結合力は既存仕様どおりであり、選択順の回答を待つために止めない。

## Q7. 同じ照合経路で、同じ名前を二度束縛するpatternを許すか

状態: **未回答**。`spec/03b-patterns.md` 3b.1は名前/asの束縛、3b.6はorの枝の名前集合を定めるが、
一つの枝の内部での重複名は定めていない。`spec/02-declarations.md` 2.1の後のmyによるshadowingは、
一つのpattern内へ拡張しない。

例: `(x, x)`を`(1, 2)`へ合わせたとき、および`(x, _) as x`。

- **A（推奨）:** 同じ照合経路内の重複束縛を静的に拒否する。別のor枝に同じ名前を書く`(x,0) | (0,x)`は既存仕様どおり許す。
- **B:** 重複を許し、最初または最後の束縛を選ぶ規則を追加する。この案ならasを含む優先順も明記する必要がある。
- **C:** 二回目以降を新しい束縛ではなく等値制約として扱う。例の`(1,2)`はmissとなり、必要な比較の型・effectも定める必要がある。

影響する義務: sourceの名前解決、orの束縛順の整列、`BindingsHold`へのelaboration、guard/bodyの変数参照。
現在の核は解決済みIDの位置付き列を扱い、lookupは先頭を返す。これはsourceのBを採用したことではない。
sourceとの対応は重複の解決規則を決めるまで主張せず、既存の独立な束縛型判断の証明はそのまま保つ。

## Q8. polyvariantの反駁可能なpayload patternを、複数armで網羅してよいか

状態: **未回答**。`spec/04-types.md` 4.5と決定4による、tag一意・同一tagのpayload合流・
残余にはpayload全体だけを残す規則は確定済みで、問い直さない。
ここで問うのは、3b.4のRust相当coverageと4.5の「payloadの中まで入らない」の適用範囲である。

入力`x`の型が閉じた`:flag bool`の場合:

```yulang
case x:
    :flag true -> 1
    :flag false -> 0
```

- **A（推奨）:** 反駁可能なpayload patternを許し、同じtagの複数armを合わせてpayload全体を覆えた場合にtagを丸ごと処理済みにする。残余型を部分payloadへ細分化しないことと、coverageの内部計算を区別して明文化する。
- **B:** 反駁可能なpayload patternは書けるが、tagを処理済みにするにはpayload全体を覆うunguarded armまたは最後のwildcardを別に要求する。上の二armだけでは受理しない。

補助例: `:flag true -> 1; rest -> 0`を許す場合でも、`rest`へ`:flag false`だけの残余型を与える案ではない。
tagを残すなら元のbool payload全体を残す決定は、どちらの選択肢でも維持する。

影響する義務: source polyvariantのcoverage、処理済みtag集合の生成、`VariantsMerged`残余とcase typingの接続。
現在のcheckerは一つのarmがpayload全体を覆う場合を認証するだけで、falseをsource拒否と解釈しない。
これはBを仕様として採用したことではない。nominal enumへ決定4を広げず、そのpayload分割は通常のcoverage算法の残る義務とする。

## Q9. listの負の整数indexを、無効とするか末尾相対とするか

状態: **未回答**。`spec/03-expressions.md` 3.5、`spec/04-types.md` 4.1、`spec/06-roles.md` 6.1はIndex経由の解決を定めるが、
負のlist indexの解釈は定めていない。例: `[10, 20][-1]`。

- **A（推奨）:** 有効な位置は`0 ≤ i < length`とし、負のindexは無効にする。失敗の表現は次の問いで分けて扱う。
- **B:** 負の`i`は`length + i`へ変換する。`-1`は末尾となり、変換後も範囲外なら無効にする。

旧素材の根拠: [mainのruntime snapshot](https://github.com/momota1029/yulang/blob/d4c8bc8fc8a49173180932cd25921a2c41057354/crates/mono-runtime/src/lib.rs)
の`value_index`は整数からusizeへの変換失敗を返すため、負数を末尾相対にはしない。
ただし`spec/00-sources.md`に従い、この素材を新仕様として自動採用しない。machine integerの上限も引き継がない。

影響する義務: sourceの任意精度Intから内部Nat indexへの変換、`NominalListViews.index_exact`との接続、
Index辞書とRust oracleの一致。現在は内部Nat indexと独立な位置判断だけを証明し、A/Bのどちらも選んでいない。

## Q10. 無効なlist indexの結果を、どの失敗として表すか

状態: **未回答**。負数の解釈（Q9）とは独立に、`[10,20][2]`や`[][0]`の結果を定める必要がある。
`spec/06-roles.md`と`spec/08-errors-std.md`は、その失敗の型・effectをまだ確定していない。

- **A（推奨）:** 名前つきerror effectにし、sourceの型とhandlerで扱えるようにする。effect key・payload・署名とIndexのeffect行への反映を定める。
- **B:** interpreterの実行時失敗にし、通常のsource catchの対象にはしない。
- **C:** `opt A`を返す。Indexのassociated valueが`A`のAPIからは変更になるので、安全な別methodを追加する案とは区別する。

旧素材: [listのIndex実装](https://github.com/momota1029/yulang/blob/d4c8bc8fc8a49173180932cd25921a2c41057354/lib/std/data/list.yu)
は返り値を要素型そのものとし、[旧list説明](https://github.com/momota1029/yulang/blob/d4c8bc8fc8a49173180932cd25921a2c41057354/web/docs/ja/reference/std/list.md)
は範囲外を実行時失敗とする。旧runtimeのListIndexはhost側のRuntimeErrorを返し、
名前つきbounds effectは導入していない。Aはこの素材からの変更案であり、採用済みではない。

影響する義務: source Indexの値型・effect行、progressが保証する結果、Rust oracleと速い実装の失敗観測。
現在の`NominalListViews.index`のOptionは内部lookupの成否だけを表し、sourceにCを採用した意味ではない。
構築値とcursor/index/foldの一致はこの回答に依存せず証明済みである。
