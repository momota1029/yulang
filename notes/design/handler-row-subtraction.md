# Handler Row Subtraction

2026-05-13 時点の effect row hygiene の作業メモ。

このメモの焦点は、「高階関数が引数由来の effect を handler で勝手に捕捉しない」
という衛生性を、型の恒久的な属性ではなく、handler / thunk 境界での row 照合規則
として定義することにある。

## 目的

Yulang の handler は、関数引数から発生した effect を、呼び出し側の意図なしに捕捉して
はいけない。

例として、`for` loop の中で呼ばれる関数引数 `f` が `last` を投げても、その `last` は
loop の `last` handler に捕捉されない、という性質を保つ必要がある。

この問題は、単に effect row に `;` を足すだけでは足りない。必要なのは、
「thunk に入れる瞬間に、どの表層 effect を現在層へ残してよいか」を表す
`shift[keep]` と、thunk から出る瞬間に対応する delimiter を剥く `peel` である。

## 前提: Handler は Shallow

この設計では、handler は shallow handler であると仮定する。

handler が捕捉するのは、その handler の body を評価している間に直接発生した depth 0
の operation だけである。捕捉後に resumption を呼ぶ場合、再開された継続は同じ handler
の内側へ自動的には再設置されない。

したがって、次の性質を前提にできる。

- handler は現在の表層 effect だけを見る。
- depth が 1 以上の effect を、同じ handler が再帰的に捕捉しない。
- resumption の中で同じ effect をもう一度処理したい場合は、明示的に handler を置く。

`[; e]` によって depth が 1 つ増えた effect は、現在の shallow handler から見て表層では
ない。このため、未注釈 thunk 由来の effect は handler body の内側を通っても捕捉されず、
thunk から外へ出る時に `peel` されて、外側の row として観測される。

## Row の見方

Effect row は `;` で区切られた層を持つ。

```text
[α, β; γ]
```

左端の層を表層と呼ぶ。handler が直接処理できるのは表層の effect だけである。

実装上は、effect item に de Bruijn depth のような番号を持たせる形で見られる。

- depth 0: 現在の表層
- depth 1 以上: handler 境界の外側にある層

handler / thunk 境界に入れるときだけ、必要な effect を表層へ取り出す。取り出されな
かった effect は、境界の内側から見ると depth が 1 つ増える。

## Shift / Peel としての `[; e]`

より単純な見方として、未注釈の thunk entry は effect row 全体を 1 段 shift する。

```text
shift(e) = [; e]
```

これは、`e` に含まれる全 effect の depth を 1 つ増やす操作として扱える。

```text
α          -> depth 1 の α
[α, β]     -> [; α, β]
[α; β]     -> [; α; β]
```

通常の場所では `[; e]` を `[e]` と同じように分解してよい。ただし、handler / thunk の
内部 view では marker を消さない。handler は depth 0 だけを捕捉するため、`[; e]` の中の
effect は、その handler から見ると 1 段外側にある。

thunk から外へ出すときは必ず 1 段 peel する。

```text
peel([; e]) = [e]
```

この `shift` / `peel` は cast のように実装できるが、任意の型変換ではない。thunk entry
と thunk exit に対応する構造的な row operation である。

動的意味論としては、未注釈 thunk の周りに「何もしない handler」を 1 枚置く、と読める。
その handler は effect を処理せず、外側へ投げ直すときに depth を 1 つ増やす。したがって
内側の未処理 effect は、外側の表層 handler に捕捉されない。

```text
inside thunk:
  perform α

no-op handler at thunk boundary:
  α@0 -> α@1

outer handler for α@0:
  does not catch α@1

leaving thunk:
  peel α@1 -> α@0
```

この見方なら、反変位置と共変位置で `[α; e]` の意味を変える必要がない。`[; e]` は一貫
して「handler 内部 view では 1 段奥、通常 view / 外側 view では peel される row」として
扱う。

## 選択的 Shift

`shift` は、単なる全体 shift ではなく、どの表層 effect を現在層に残してよいかを引数に
持つ命令として扱う。

```text
shift[keep](row)
```

`keep` は、thunk entry で現在の表層に残す effect の集合である。`keep` に含まれない
effect は 1 段奥へ送る。

未注釈 thunk は、何も現在層に残してはいけない。

```text
shift[]( [α, β; γ] ) = [; α, β; γ]
```

`[α]` 注釈付き thunk は、表層の `α` だけを現在層に残してよい。

```text
shift[α]( [α, β; γ] ) = [α; β; γ]
```

`[_]` 注釈付き thunk は、表層にある effect をすべて現在層に残してよい。

```text
shift[_]( [α, β; γ] ) = [α, β;; γ]
```

この形では、`[_]` は「shift しない」ではない。現在の表層を handler から見えるままに
残し、その奥にある effect はさらに 1 段奥へ送る。したがって、thunk boundary 自体は
常に保存される。

`peel` は、対応する `shift[keep]` が挿入した delimiter を 1 つ剥く操作として扱う。

```text
peel( [; α, β; γ] ) = [α, β; γ]
peel( [α; β; γ] ) = [α, β; γ]
peel( [α, β;; γ] ) = [α, β; γ]
```

この `peel` は、row を適当に正規化する規則ではなく、対応する thunk entry evidence を
持つ boundary exit でだけ使える。

## 遅延 Shift / Peel

`shift` / `peel` は意味論としては分かりやすいが、実装で row 全体を毎回走査して全 effect
の depth を書き換えると重い。

実装では、row 本体を書き換えず、thunk / handler boundary に選択的 shift frame を持つ
view を置く。

```text
RowView {
  row,
  frames: Vec<ShiftFrame>,
}

ShiftFrame {
  keep,
}
```

未注釈 thunk に入るとき:

```text
RowView(row, frames) -> RowView(row, frames + shift[])
```

`[_]` 付き thunk に入るとき:

```text
RowView(row, frames) -> RowView(row, frames + shift[_])
```

thunk から出るとき:

```text
RowView(row, frames + shift[keep]) -> RowView(row, frames)
```

handler が見るのは、shift frame を適用した後に depth 0 に残る effect だけである。
`shift[]` は何も depth 0 に残さない。`shift[_]` は元の表層だけを depth 0 に残し、tail
を 1 段奥へ送る。

この形なら、`shift` / `peel` は O(1) になる。row を実際に分解するのは、handler が表層
effect を照合するときだけでよい。

shift frame は通常の型として広く流さない。constraint solver の汎用 row 型へ混ぜるより、
handler / thunk boundary の照合 relation が読む view として閉じ込める。

```text
match_handler_effect(RowView(row, frames), handled, residual)
```

`frames` がある場合、handler は frame が残した depth 0 の effect だけを処理できる。
処理できない effect は、residual 側へ view のまま流れる。外へ出る boundary で対応する
frame を外す。

この遅延化により、理論上は `shift` / `peel` として説明しつつ、実装上は row の clone /
再走査 / depth 書き換えを避けられる。

## Runtime / Native 表現との分離

遅延 `shift` / `peel` は、型推論ではよい表現である。ただし、そのまま native 表現として
十分かどうかは別問題である。

型推論では、`EffectView { row, frames }` のような view を持てば、row 本体を書き換えずに
handler 照合を遅延できる。しかし実行時には、effect operation が発生した瞬間に、どの
handler frame が捕捉してよいかを決める必要がある。

native / runtime 側には、少なくとも次のどちらかが必要になる。

1. operation に depth / delimiter 情報を載せる
2. handler stack 側に delimiter frame を載せ、探索時に shallow handler が depth 0 だけを
   見る

型推論の `shift[keep]` / `peel` evidence は、native lowering では実行時 frame 操作へ落とす
必要がある。

概念的には、未注釈 thunk entry は no-op delimiter frame を push する。

```text
enter thunk:
  push Delimiter { keep = {} }

perform α:
  handler search sees α under delimiter
  current shallow handler cannot catch it

exit thunk:
  pop Delimiter
```

`[_]` 付き thunk entry は、表層を現在 handler へ見せる delimiter を push する。

```text
enter thunk:
  push Delimiter { keep = Surface }

perform α from original surface:
  current shallow handler may catch α

tail effects:
  remain behind the delimiter
```

ここで注意するべき点は、型推論の `peel` は O(1) view で済むが、native では handler stack
から対応する delimiter を必ず pop する制御フローが必要になることだ。例外的な unwind、
resumption、multi-shot continuation では、この frame の snapshot / clone / restore が
意味論に含まれる。

したがって、型推論の設計と native 表現は次のように分けて考える。

- 型推論: row view と evidence で `shift[keep]` / `peel` を遅延する。
- runtime VM: handler stack に delimiter frame を追加し、operation dispatch が shallow
  depth 0 だけを捕捉する。
- native CPS: continuation / handler context に delimiter frame を含め、resumption clone
  が frame を構造共有または snapshot する。

この分離を置かないと、型では衛生的でも、実行時に handler stack が普通に近い handler を
捕まえてしまう危険がある。

## 推論中の挿入方針

`shift` / `peel` は、subtyping や unification が好きな場所で推測して挿入するものでは
ない。挿入位置は構文上の thunk boundary で決まる。

基本形:

```text
thunk entry:
  effect view e -> shift[keep](e)

thunk exit:
  shift[keep](e) -> peel(shift[keep](e)) = e
```

推論器は、通常の型を直接 `[; e]` に書き換えない。代わりに、thunk boundary の evidence
として次を記録する。

```text
EffectEvidence::Shift { row, keep }
EffectEvidence::Peel { row }
```

または solver 内部の一時 view として次を持つ。

```text
EffectView {
  row,
  frames,
}
```

重要な不変条件:

- `shift` は thunk entry でだけ入る。
- `peel` は対応する thunk exit でだけ入る。
- `shift` / `peel` を generic subtype edge の解決策として探索しない。
- 通常の row 型を compact / display / hover する時点では、対応済みの evidence は残さない。

これにより、推論は `shift` / `peel` を「大量に使う」が、「どこにでも入る cast」にはならない。
挿入点が構文で固定されるため、principal type を壊しにくい。

`compose` の未注釈引数なら、`g x` を `f` 側の thunk に入れる edge にだけ `shift[]` が載る。

```text
g x : e
thunk entry evidence: shift[](e)
handler view inside f: [; e]
thunk exit evidence: Peel([; e])
external effect: e
```

`[_]` が付いた引数なら、その thunk entry には `shift[_]` が載る。これは boundary を消す
のではなく、現在の表層だけを handler から見えるままに残す。

```text
g x : e
thunk entry evidence: shift[_](e)
handler view inside f: surface(e); shifted tail(e)
external effect: e
```

この差は、関数引数の row 変数に属性を付けるのではなく、`g x` から `f` の thunk parameter
へ渡る edge に付く。

## 注釈は Keep Set

この案では、`[α]` や `[_]` を反変位置と共変位置で別の意味に読まない。
thunk parameter の effect 注釈は、thunk entry に置く `shift[keep]` の `keep` を決める。

```text
未注釈: keep = {}
[α]:    keep = {α}
[_]:    keep = surface
```

未注釈なら、呼び出し元から入ってきた effect はすべて 1 段奥へ送る。

```text
shift[]( [α, β; γ] ) = [; α, β; γ]
```

`[α]` なら、表層の `α` だけを現在層に残す。

```text
shift[α]( [α, β; γ] ) = [α; β; γ]
```

`[_]` なら、表層全体を現在層に残す。

```text
shift[_]( [α, β; γ] ) = [α, β;; γ]
```

このため、注釈は row 変数の性質ではなく、thunk に入る edge の性質になる。

## Handler 照合

普通の handler は、現在の depth 0 operation だけを処理する。

handler 照合は、型そのものに `shift[keep]` を適用しない。`shift[keep]` は thunk boundary
の evidence であり、handler 照合 relation がそれを読む。

relation は、対象 row が型変数なら、そのまま制約として残す。型変数を開いて表層を推測
しない。

```text
actual = 'e
constraint = handler_match('e, keep, handled, residual)
```

対象 row が既知 row なら、その表層だけを見る。`keep` によって現在層へ残っている表層
effect のうち、handler が処理する effect だけを引き、残りは inside rest として残す。

未注釈 thunk では、表層 effect が何も残らない。

```text
before entry: [α, β; γ]
entry:        shift[]
inside view:  [; α, β; γ]
handler:      α
inside rest:  [; α, β; γ]
exit peel:    [α, β; γ]
```

`[α]` 注釈付き thunk では、`α` だけが handler から見える。

```text
before entry: [α, β; γ]
entry:        shift[α]
inside view:  [α; β; γ]
handler:      α
inside rest:  [; β; γ]
exit peel:    [β; γ]
```

`[_]` 注釈付き thunk では、元の表層全体が handler から見える。ただし、tail はさらに
1 段奥へ送られる。

```text
before entry: [α, β; γ]
entry:        shift[_]
inside view:  [α, β;; γ]
handler:      α
inside rest:  [β;; γ]
exit peel:    [β; γ]
```

handler が要求する effect が表層にない場合は捕捉されない。

```text
before entry: [α, β; γ]
entry:        shift[_]
inside view:  [α, β;; γ]
handler:      δ
inside rest:  [α, β;; γ]
exit peel:    [α, β; γ]
```

この規則なら、`[; e]` の意味を極性で変えなくてよい。`shift[keep]` と `peel` の組だけが
handler boundary の層を作り、handler は常に shallow に depth 0 を処理する。

## 「保護」ではなく照合規則

この仕組みは、row 変数に「保護済み」という恒久的な属性を付けるものではない。

同じ row でも、通常の row として開く場所では普通に `[e]` として扱う。handler / thunk
境界で、`shift[keep]` frame 越しに handler 型と照合するときだけ、「どの effect を
現在の表層に残してよいか」という規則が働く。

したがって、内部表現に `ProtectedRow` のような通常型を増やすより、handler 照合専用の
関係として持つほうがよい。

## 実装境界

この設計なら、型推論の中核は次の形へ寄せられる。

- 通常の row unification は、従来の open row として扱う。
- `;` は一般の row 型として広く流さない。
- handler / thunk 境界に、専用の selective shift / peel evidence を置く。
- display / compact / diagnostics は、handler 照合の内部 artifact を見ない。

専用 relation の仮名:

```text
handler_match(actual, keep, handled_set, residual)
```

この relation は、`shift[keep]` を型へ適用しない。`actual` が型変数なら relation のまま
制約として残す。`actual` が既知 row なら、その表層だけを見て、depth 0 に残っている
`handled_set` だけを処理し、残りを `residual` に制約する。

疑似規則:

```text
row variable:
  handler_match('e, keep, {α}, residual)
  => keep relation as constraint

unannotated thunk:
  handler_match([α, β; γ], keep = {}, handled = {α}, residual)
  => residual = [α, β; γ]

annotated thunk:
  handler_match([α, β; γ], keep = {α}, handled = {α}, residual)
  => residual = [β; γ]

wildcard annotation:
  handler_match([α, β; γ], keep = Surface, handled = {α}, residual)
  => residual = [β; γ]
```

`FunctionExitRow` のような別 variant は、この設計では不要に見える。関数から出るときに
特別な型を残すのではなく、thunk entry / exit の evidence だけが `;` の意味を知る。

## 手計算

### `compose` と未注釈引数

```text
compose f g x = f (g x)
```

`g` が型注釈なしで導入された関数引数だとする。このとき、`g x` の effect を
`ρg` と置く。

`f` の適用で `g x` を thunk に入れるとき、未注釈なので `shift[]` が入る。

```text
entry: shift[](ρg)
```

`ρg` の中に実行時の `α` が含まれていても、それは `f` 側の handler が捕捉してよい
effect ではない。`compose` は、`g` 由来の effect を外へ残したまま返す。

呼び出し側で `g` が具体的に次の effect を持っていたとしても、

```text
ρg = [α, β; γ]
```

未注釈の `compose` 内では、`g x` を `f` の thunk に入れる boundary で `α` を引かない。

```text
before entry: [α, β; γ]
entry:        shift[]
inside view:  [; α, β; γ]
handler:      α
inside rest:  [; α, β; γ]
exit peel:    [α, β; γ]
```

この形なら、`f` が内部で `α` を handle する関数であっても、`g` が投げた `α` は捕捉され
ない。高階関数引数の effect hygiene はこの規則から出る。

### `compose` と `[_]` 付き引数

```text
compose f (g: _ -> [_] _) x = f (g x)
```

`[_]` は、`g` の effect を thunk に入れるとき、現在の表層を handler から見えるままに
残す `shift[_]` を入れる。

同じく `g x` の effect を `ρg` と置く。`ρg` が呼び出し側で次のように具体化された場合:

```text
ρg = [α, β; γ]
```

`f` 側の handler が `α` を処理するなら、`shift[_]` 後の表層に残った `α` を捕捉できる。

```text
before entry: [α, β; γ]
entry:        shift[_]
inside view:  [α, β;; γ]
handler:      α
inside rest:  [β;; γ]
exit peel:    [β; γ]
```

この場合だけ、`g` 由来の `α` は `f` 側の handler に渡る。意味論上も、型上も、
`[_]` によって明示的に捕捉を許可した effect だけが処理対象になる。

`[_]` は「必ず全部捕捉する」という意味ではない。表層を現在層に残すだけで、実際に
捕捉するのは handler が要求した effect だけである。

```text
before entry: [α, β; γ]
entry:        shift[_]
inside view:  [α, β;; γ]
handler:      δ
inside rest:  [α, β;; γ]
exit peel:    [α, β; γ]
```

つまり `[_]` は、通常の row を壊す cast ではなく、thunk に入れる edge 上の
`shift[keep]` の一種と見られる。

### `compose` を Relation として見る

```text
compose f g x = f (g x)
```

`g x` の effect row を `ρg`、`f` の中で引数 thunk を評価している間に処理しうる
effect 集合を `Hf`、`f` から外へ出る `g` 由来の残りを `ρout` と置く。

未注釈の `g` なら、`g x` から `f` の thunk parameter へ渡る edge に次の制約が立つ。

```text
handler_match(ρg, keep = {}, handled = Hf, residual = ρout)
```

`ρg` が型変数なら、この relation は制約として残る。`ρg` が既知 row なら、表層を見ても
`keep = {}` なので handler は何も引けない。

```text
ρg = [α, β; γ]
Hf = {α}

handler_match(ρg, {}, Hf, ρout)
=> ρout = [α, β; γ]
```

`g` に `[_]` が付くなら、同じ edge の `keep` が表層全体になる。

```text
handler_match(ρg, keep = Surface, handled = Hf, residual = ρout)
```

この場合だけ、`f` が処理する effect と `ρg` の表層が一致した分だけ落ちる。

```text
ρg = [α, β; γ]
Hf = {α}

handler_match(ρg, Surface, Hf, ρout)
=> ρout = [β; γ]
```

`[α]` のような注釈なら、`α` だけを現在層に残す。

```text
ρg = [α, β; γ]
Hf = {α, β}

handler_match(ρg, {α}, Hf, ρout)
=> ρout = [β; γ]
```

`β` は `Hf` に含まれていても、`keep` に含まれていないため捕捉されない。

### 表層の一部を処理

```text
handler: α
actual:  [α, β; γ]
result:  [β; γ]
```

### 表層の順序に依存しない

```text
handler: α
actual:  [δ, α; γ]
result:  [δ; γ]
```

### 表層を全て処理

```text
handler: α, β
actual:  [α, β; γ]
result:  [γ]
```

### 未注釈の引数由来 effect は shift される

```text
entry:       shift[]('f)
handler:     α
inside rest: shift[]('f)
exit peel:   'f
```

`'f` の中に実行時に `α` が含まれていても、`shift[]` の内側では depth 0 に現れないため、
この handler がそれを捕捉してよい根拠にはならない。

## 未決事項

- effect item の depth を既存の row 表現へ入れるか、`EffectView` の frame stack だけで
  表すか。
- cast と thunk entry / exit evidence を同じ expected boundary に置く場合、evidence を
  どの順で挿入するか。

## 実装境界

この設計は、型構文、制約、evidence、runtime frame を混ぜないことを不変条件にする。

```text
Type:
  ordinary row only

Solver:
  HandlerMatchEdge(actual, mask, residual)

HIR / typed IR evidence:
  delimiter boundary
  handler_match metadata

VM / native:
  HandlerFrame
  DelimiterFrame
```

`handler_match` は `Type` ではない。`shift` / `peel` も `Type` ではない。`SegmentedRow` や
`ProtectedRow` のような public row variant として流さない。

Solver では、`keep` と handler の処理集合から `mask` を作れる。

```text
mask(None, H)       = {}
mask(Set(K), H)     = K ∩ H
mask(Surface, H)    = H
```

ただし、`mask` は「row 全体から消す集合」ではなく、既知 row の表層だけに作用する。
`actual` が naked row variable の場合は開かず、`HandlerMatchEdge` として残す。

```text
handler_match(ε, Surface, {α}, ρout)
```

ここから `ε = [α | rest]` を発明してはいけない。これが simple-sub の principal graph を
壊し、thunk boundary の漏れを作る。

### Catch Lowering

既存の catch lowering は、handled effect atom を集めたあと、概念的には
`handled + rest` を `comp.eff` と比較して residual を作っている。

新しい lowering では、効果残余だけを専用 relation に置き換える。

```text
residual = fresh row variable

record handler_match(
  actual = comp.eff,
  keep = current thunk boundary keep,
  handled = handled_ops,
  residual = residual,
)

result_eff = residual + arms_eff
```

`constrain_existing_comp_effect_atoms` のような既存 atom の型引数合わせは残してよい。ただし、
open row variable を開いて handled atom を発明する根拠にしない。

### Generalize / Instantiate

解けなかった `HandlerMatchEdge` は hidden constraint として scheme に閉じる。

```text
∀ ε ρout. hidden HandlerMatch(ε, mask, ρout) => ...
```

hover / compact には出さないが、module interface や typed IR metadata には残す。import
後に instantiate したとき、hidden edge も fresh row variable に合わせて複製する。

### Display

compact / hover / normal diagnostics は次を辿らない。

```text
HandlerMatchEdge
ShiftEvidence
PeelEvidence
DelimiterEvidence
```

solved substitution だけを普通の row として表示する。未解決の `handler_match` は debug mode
以外で表示しない。

### Runtime

VM / native では型 row を持ち込まず、control stack に delimiter frame を入れる。

```text
ControlFrame =
  Handler(handled)
  Delimiter(keep)
  Return(...)
```

effect dispatch は内側から外側へ走査し、delimiter を越えるたびに runtime depth を更新する。
handler が捕捉できる条件は `depth == 0 && handled contains op` だけ。

```text
cross(op, depth, None) =
  depth + 1

cross(op, depth, Surface) =
  if depth == 0 then 0 else depth + 1

cross(op, depth, Set(K)) =
  if depth == 0 && op ∈ K then 0 else depth + 1
```

`Surface` は深い effect を再露出しない。現在すでに depth 0 の operation だけを通す。

Shallow handler の resumption は handler frame 自身を含まない。ただし delimiter frame は
captured continuation に含める。これを落とすと、resume 後に thunk hygiene が壊れる。

## 実装手順案

1. 既存の実験的な segmented row / function-exit 系の変更を戻し、通常 row の不変条件を
   回復する。
2. `ShiftKeep::{None, Set, Surface}` のような小さい概念を用意し、row 変数ではなく
   thunk に入れる edge に付ける。
3. selective shift / peel relation だけを独立した小さい module として作る。
4. `compose` の `[_]` なし / ありを、まず手計算に対応する小さい test として固定する。
5. 既知 row、通常 row 変数、`shift[_]` の手計算に対応する unit test を先に固定する。
6. `catch` / handler lowering は、generic subtype 制約ではなく専用 relation を呼ぶ。
7. compact / display / hover は、通常 row の結果だけを見る。

この順にすると、hover や display に `;` の内部都合が漏れにくい。型推論の見た目を直す
ための後段補正ではなく、handler 境界の規則として説明できる。
