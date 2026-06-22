## 位置づけ

このメモは、`ref_update/update_effect` の符号化を残す前提で、なぜ current safe commit でも
`ref.update` の public scheme に private stack evidence が漏れているかを整理する診断メモである。

まだ実装方針の確定ではない。特に、`3daadaaf` の termination guard は、private evidence の
scope と replay key を直すまで外さない。`pop(n)` を丸める guard を消す作業は最後に回す。

採用寄りに見える点は次の三つだねぇ。

- 問題を `ref_update` という名前や std 固有 API へ押し込まず、data-position function の latent
  return-effect boundary として一般化している。
- `κ <: e` / `e <: κ` の普通の alias を張らず、scope-close 時の projection として扱う必要を
  明示している。
- `pop(n)` を無視する新しい seen key ではなく、source graph の nonzero-displacement cycle を
  消して exact full-label key へ戻す、という順序になっている。

実装時に注意する点もある。

- `private tail/id` は単に `lower_data_effect_row_{pos,neg}` 内で fresh にするだけでは足りない。
  field value が selection 後に利用されるところまで evidence を運ぶ必要がある。
- `struct self` の synthetic getter 専用で済ませるか、constructor payload / public field /
  stored function value まで含む existential package として扱うかは、最初の slice で境界を決める。
- private evidence を close する前に public scheme へ stack id や private tail が残らないことを
  assert する canary を先に置く。

## 実装結果: 今回採用した最小修正

今回の実装では、Pro 案の full replay key / private data-tail projection までは入れていない。
採用した修正は次の二つ。

1. type method の戻り型注釈を、body lowering 中の raw body effect へ直接接続しない。
   `pub r.update(f: 'a -> 'a): ['e] ()` の `['e] ()` は、receiver + args を含む method
   scheme の結果位置に対する deferred check として扱う。これにより、`loop(x: [_] _)` の
   wildcard stack evidence、handler arm 内 callback、`r.update_effect()` の data field
   tail が、method body の未外部化状態で早く合流しすぎることを避ける。
2. generalize の final cleanup で、構造上の出現と declared fact が `Empty` だけの stack id を
   public scheme から落とす。これは `#id[Empty]` / `#id(1)[Empty]` のような boundary evidence
   を surface へ出さないための cleanup であり、`All` / `AllExcept` / `Set` を持つ stack id は
   対象にしない。

この組み合わせで、実際の std `ref.update` は次へ落ちる。

```text
std::control::var::ref('a & 'c, 'b) -> ('b -> ['c] 'b) -> ['c, 'a] ()
```

`#...` や `AllExcept` は public 表示に出ない。

一方で、data-position effect tail を private tail / private id へ射影する案は試したが戻した。
`update_effect: () -> [ref_update 'a; 'e] ()` の data tail を private projection にすると、
型表示は一見きれいになる一方で、`tests/yulang/regressions/runtime/list_update.yu` が
`unhandled effect std::control::var::ref_update::update` で壊れた。runtime の `RefSet` 特別処理と
catch marker の再送経路は、現在の data field effect shape に依存している。ここを変えるなら、
specialize / control VM 側の marker guard と ref-set request handling も同時に見る必要がある。

したがって今回の修正は、termination guard、full replay key、`pop(n)` clamp removal には触れない。
それらはこのメモの後半にある full plan 側の未完了項目として残す。

## 追加調査: `#37` は local helper の wildcard 注釈由来

Pro 案の方向は妥当だけど、実際の `std.control.var.ref.update` で表示されている
`#37(1)[AllExcept(ref_update ...)]` は、synthetic getter の `update_effect` だけから来ているわけではない。

最小化した入力でも、

```text
pub r.update(f: 'a -> 'a): ['e] () =
  my loop(x: [_] _) = catch x:
    ref_update::update v, k -> loop:k:f v
  loop:r.update_effect()
```

を `dump-poly-raw` すると、public method scheme に次が出る。

```text
stack_quantifiers: [#3]
p58 = Stack { inner: p57, weight: { #3 -> pops: 1,
  stack: [AllExcept(std::control::var::ref_update, [u22])] } }
```

この `#3` は trace で、

```text
[gen] #3 at crates/infer/src/annotation/constraints.rs:458
```

つまり `effect_row_stack` の wildcard branch から出ている。対象は field getter ではなく
local defined helper の引数 `x: [_] _` だねぇ。

さらに `d15:loop` 自体の local scheme には `stack_quantifiers` が残っていない。
ただし local scheme は外側 method の自由変数を参照したまま generalize されるため、`#3` を含む
var-var lower bound は outer method の constraint graph に残る。trace では public tail 側の
`TypeVar(25)` に、

```text
LeftStackWeightEntry { id: SubtractId(3), leading_pops: 1, family: None, pushes: 0 }
```

を持つ lower が積まれていた。row split / handler 側でこれが `AllExcept(ref_update ...)` と合流し、
最終的に outer public scheme の `['e]` に見える。

一度試した getter-only の private-tail 化では、synthetic getter の scheme から stack evidence は消せた。
それでも `ref.update` の public scheme は同じ形で漏れたので、`struct self` getter だけを閉じる修正では
canary は直らない。

ここから分かることは次の通り。

- private に閉じるべき evidence は data-position function boundary だけでは足りない。
  local defined helper の effectful parameter wildcard boundary も、local generalization / enclosing
  method generalization のどこかで閉じる必要がある。
- ただし public API の wildcard callback annotation は意図的に surface へ出る。
  `nested_callback_wildcard_return_keeps_push_and_pop_one` は
  `('d ['a#0[All]] -> ['e] 'c) -> ...` を期待しているので、wildcard stack を全消ししてはいけない。
- `local_binding_call_return_effect` は binding の戻り型注釈だけを見る。
  そのため `my loop(x: [_] _) = ...` は `LocalCallReturnEffect::Unannotated` のままで、
  call 側の Empty subtract も別に発生する。今回 public scheme に出ている id 自体は、
  その Empty subtract ではなく `x: [_] _` の annotation id だった。

したがって canary は、getter 単体ではなく「method result annotation + local `loop(x: [_] _)` +
`r.update_effect()`」の形を固定する必要がある。望ましい修正は、local helper の内部 evidence を
outer public scheme へ stack id として輸出せず、ordinary residual row だけへ射影することになる。

補助実験として、local helper を

```text
my loop(x: [ref_update 'a; 'e] _) = ...
```

へ明示すると、最小入力の public `ref.update` から `#...AllExcept(ref_update ...)` は消えた。
ただし detached な `update_effect` getter scheme にはまだ data-position function 由来の
`#...AllExcept(ref_update)` が残る。これは std 側の局所回避としては使えるかもしれないが、
private evidence scope の根治とは別物として扱う。

さらに切り分けると、単純な local handler だけでは漏れない。

```text
act tick:
  pub ping: () -> ()

pub h(action: [tick; 'e] ()): ['e] () =
  my loop(x: [_] _) = catch x:
    tick::ping(), k -> loop:k()
  loop action
```

これは `() [tick; 'a] -> ['a] ()` へ clean に落ちる。

data-position function だけを足した場合も、method 本体は clean で、detached getter にだけ
private evidence が残る。

```text
type box 'e with:
  struct self:
    run: () -> [tick; 'e] ()
  pub b.handle(): ['e] () =
    my loop(x: [_] _) = catch x:
      tick::ping(), k -> loop:k()
    loop:b.run()
```

`box.handle` は `box 'a -> () -> ['a] ()` になる一方、getter `run` は
`box 'a -> () -> [tick, 'a#1[AllExcept(tick)]] ()` のように evidence を持つ。

一方で handler 内に callback を足すと、`ref.update` と同じ public leak が再現する。

```text
act tick 'a:
  pub ping: 'a -> 'a

type box 'e 'a with:
  struct self:
    run: () -> [tick 'a; 'e] ()
  pub b.handle(f: 'a -> 'a): ['e] () =
    my loop(x: [_] _) = catch x:
      tick::ping v, k -> loop:k:f v
    loop:b.run()
```

この `box.handle` は現状、

```text
box('a#3(1)[AllExcept([tick 'c])] <: 'a, 'b)
  -> ('b -> ['a] 'b)
  -> ['a#3(1)[AllExcept([tick 'c])]] ()
```

になる。したがって最小因子は、少なくとも

1. data-position effectful function (`run/update_effect`)
2. local wildcard handler (`loop(x: [_] _)`)
3. handler arm 内 callback (`f v`)

の三つだと見てよさそうだねぇ。

## full plan 側の設計仮説

full plan での根治候補は、**std の `ref_update/update_effect` 符号化を捨てることではなく、data-position に埋め込まれた関数の返り effect tail を private / existential にすること**だと思う。

`ref_update` は壊れた特殊例ではなく、handler hygiene を検査するかなり良い canary だねぇ。spec 自身もこの符号化から、hidden evidence を消した

```text
ref (e & b) a -> (a -> [b] a) -> [e; b] unit
```

を導いている。

普通の `modify` フィールドへ置き換えると、問題を消すというより、

* callback effect polymorphism をフィールド型へ押し込む
* 各 ref 実装に handler hygiene の責任を移す
* 同じ形を持つ別の data field では再発する

という API 変更になる。標準ライブラリ上の便利な別 API としてはありだけど、型推論の修正にはならないよ〜。

---

## 漏れの本体

現在の data lowering は、open row

```text
[ref_update a; e]
```

に対して、**public signature variable `e` そのもの**を

```text
Stack(e, take(AllExcept(ref_update)))
```

で包んでいる。さらに、その subtract fact を declaration 由来として `e` に登録している。

synthetic getter は同じ `signature_vars` map で、

```text
ref e a -> field-signature
```

の owner と field return を lower する。つまり field return 用の evidence と receiver の public `e` が、最初から同じ変数になっている。

その結果が観測済みの

```text
Bounds(
  PWeight(pop(1); take(AllExcept(ref_update)), e),
  e
)
```

だねぇ。これは表示だけの漏れではなく、public scheme 内に weighted self-alias が入っている。

さらに receiver は getter の関数引数なので反変になる。`swapped()` は左 weight から右へ移すとき、active take を運ばず pop だけを `RightConstraintWeight` にする。

そのため、もともと lexical boundary 内では balanced だった

```text
pop(s); take_s(AllExcept(ref_update))
```

が public alias graph を一周すると、

```text
right-pop(s)
right-pop(s)^2
right-pop(s)^3
...
```

として観測されうる。これは `9c1afc92` の key が捕まえられない形だよ〜。

bad commit の追加 key は、

```text
(lower, upper, left-pop-id-list, exact-right)
```

で、しかも **nonempty left-pop-only の var-var replay** にしか適用されない。

だから今回の仮説、

> escaping take が variance を通って right-pop / ordinary bounds replay の増殖を作り、var-var left-pop-only key の外で回る

は、そのまま当たっていると見るのがよさそうだねぇ。

---

## private evidence の正しいスコープ

private にすべき単位は **型変数 `e` ではなく、data 内の各 function arrow の latent return-effect boundary** になる。

`update_effect` なら内部型は概念的にこうなる。

```text
ref e a
  -> ∃ κ s.
       erase(κ) = e
       × (() -> [ref_update a; PWeight(s, κ)] unit)
```

ここで、

* `e` は public な ref effect parameter
* `κ` は field return 専用の private effect tail
* `s` はその data-function boundary 専用の private stack id
* `erase(κ) = e` は ordinary row 内容だけの対応
* `κ` と `e` の間に普通の双方向 subtype alias は張らない

という分離が要る。

普通の `κ <: e` と `e <: κ` を入れるだけだと、weighted bound がその alias を通って再び `e` に輸出されるので、existential にした意味が薄くなる。必要なのは **scope-close 時の projection** であって、solver graph 上の恒久的な equality edge ではない。

### 導入・open・close

具体的な寿命はこの形がよさそうだねぇ。

```text
type declaration lowering
  └─ synthetic getter codomain に ∃κ,s を導入

field getter instantiation
  └─ κ,s を freshen

field projection/use
  └─ package を open
     r.update_effect() : [ref_update a; PWeight(s,κ)] unit

enclosing method body
  └─ handler と callback の制約を private κ,s 上で解く

method/generalization boundary
  └─ private evidence を close
     erase(κ) を public e へ射影
     κ,s 自体は public scheme へ出さない
```

つまり scope は、

* owner `ref e a` 全体では広すぎる
* `update_effect` の row tailだけでは狭すぎて利用時まで evidence が生きない
* **synthetic getter の codomain から、その field value の利用を含む lexical regionまで**

になる。

`struct self` の private field なら、実装上は getter scheme に sealed/private-tail metadata を持たせ、companion method bodyで open、method scheme 作成前に closeする形でも足りる。将来 public field や constructor payloadにも広げるなら、IR 上の existential packageとして持つ方が自然だねぇ。

### lowering の変更位置

中心になる変更は `lower_data_effect_row_{pos,neg}` のここ。

```rust
let tail = self.signature_var(tail);
let weight = self.data_effect_tail_stack(tail, row)?;
let tail = self.alloc_*((*::Var(tail)));
self.wrap_*_with_stack(tail, &weight)
```

これを概念的には、

```rust
let public_tail = self.signature_var(tail);
let private_tail = scope.private_tail_for(row_occurrence, public_tail);
let private_id = scope.private_stack_id_for(row_occurrence);

scope.bind_erased_tail(private_tail, public_tail);

wrap(
    Var(private_tail),
    push(private_id, AllExcept(heads)),
)
```

へ変える。

重要なのは次の三点。

1. `declared_subtract_fact` を public `e` に登録しない
2. owner signature は private scope の外で bare `e` として lower する
3. 同じ field signature の positive/negative projection は同じ private binderを共有する

private ID は annotation/protect siteごとに一つ作り、scheme instantiateごとに freshenする。これは proof の static-ID / fresh-renaming 前提とも一致する。

handler 内の callback `f v` 用 `take(Empty)` は別の private boundaryとしてそのまま必要になる。rigid variable setなどは要らず、spec が述べる `take(Empty)` の lexical protectionで十分だねぇ。

close 後は、

```text
private residual κ
callback residual b
```

が普通の public rowとして `e` と `b` へ射影される。ここから既存の co-occurrence / invariant compact が

```text
receiver: ref (e & b) a
result:   [e; b] unit
```

を作り、private stack occurrenceはどこにも残らない。

---

## clamp を置き換える replay key

ここは大事で、**pop countを捨てる新しい有限 keyは要らない**。

private scopeを直して source graphを再び cycle-balancedにした後は、証明で使っている exact keyが有限になる。

理論側の key はこう。

```text
ReplayKey =
  (
    fact-kind,
    source,
    target,
    row-head-if-any,
    canonical-full-directed-label
  )
```

row-only proofにも、seen keyは fact kind・source・target・head・正規化済み label の全成分を含むと明記されている。

現在の IRへ寄せるなら、例えばこうなる。

```rust
enum ReplayFact {
    Var {
        source: TypeVar,
        target: TypeVar,
    },
    RowEndpoint {
        source: TypeVar,
        head: CanonicalEffectFamilies,
        target: TypeVar,
    },
    Structural {
        lower: PosId,
        upper: NegId,
    },
}

struct ReplayKey {
    fact: ReplayFact,
    label: CanonicalDirectedLabel,
}

struct CanonicalDirectedLabel {
    left: Vec<CanonicalLeftEntry>,
    right: Vec<CanonicalRightEntry>,
}

struct CanonicalLeftEntry {
    id: SubtractId,
    leading_pops: u32,
    pushes: u32,
    family: Option<CanonicalSubtractability>,
}

struct CanonicalRightEntry {
    id: SubtractId,
    pops: u32,
}
```

canonicalizationでは、

* ID順に整列
* zero entryを削除
* family集合をpath順に正規化
* 同一IDを `pop^m; take(F)^n` に正規化
* `take; pop` だけをexactにcancel
* W-Mixを一度適用
* filterはcheck後に消す
* pop countは一切丸めない

という形になる。

実際、`SubtypeConstraint { lower, upper, weights }` は `PosId` / `NegId` がhash-cons済みなら、ほぼこの exact keyになっている。問題は var-varだけを別経路へ出して、

```text
seen
var_var_seen
var_var_pop_replay_seen
```

という三つの異なるdedup意味論を持たせていることだねぇ。

私は var-var replayもqueueへ戻し、可能な限り

```text
(resulting lower endpoint,
 resulting upper endpoint,
 canonical exact full label)
```

の単一keyで処理する方がいいと思う。direct bound updateを残すとしても、その入口で同じ `ReplayKey` を通すべきになる。

### residual key は別物

row splitのresidual memoは従来どおり、

```text
(source, consumed-head J, canonical residual label L - J)
```

で、target tailは含めない。これはreplay seenとは役割が違う。self-tail no-opもreplay前に適用する。

---

## なぜ exact key で有限になるか

証明の有限性は、pop countを丸めることには依存していない。

source-generated graphでは、self-tailを除いた各closed walkのsigned displacementが0になる。

その条件から各SCCに整数potentialが入り、固定endpoint間のcanonical `pop^m take^n` の `m,n` は一様に有界になる。したがってexact full labelの候補自体が有限になる。

逆に言うと、同じendpointで

```text
right-pop(1)
right-pop(2)
right-pop(3)
...
```

が本当に生成されるなら、exactな有限keyは存在しない。

そこでcountを無視したkeyを足すのは、名前を変えたclampにしかならない。まず「なぜsource-generated graphに非zero-displacement cycleが入ったか」を直す必要があり、今回それがpublic schemeへ出たprivate evidenceだと考えられる。

---

## full plan を追う場合の実装順

ここから下は、今回の最小修正ではなく、Pro 案の private evidence / replay key まで進める場合の
未完了メモとして扱う。特に data-position private tail は一度試して runtime の `ref_update` 再送を
壊したので、specialize / control VM の marker guard と同時に設計し直す必要がある。

1. いったん `3daadaaf` のtermination guardを残す
2. full `ref.update` canaryを追加し、`#id[AllExcept(ref_update ...)]` が public scheme に残る現状を固定
3. synthetic field getter codomainへprivate tail/id scopeを導入
4. public owner変数へ`declared_subtract_fact`を付けない
5. getter instantiation時にprivate tail/idをfreshen
6. local defined helper の effectful parameter wildcard evidence を local boundary で close / project する
7. method generalization前にprivate tailをordinary public rowへprojectし、private var/idのescapeをassert
8. replayをcanonical exact full-label keyへ統一
9. self-tail no-opとresidual hash-consを確認
10. clampと`var_var_pop_replay_seen`を同時に外す

追加するcanaryは少なくとも、

```text
synthetic getter:
  receiver argに Stack/weighted self-aliasがない

ref.update:
  local loop(x: [_] _) の private stack id が public scheme に残らない
  ref (e & b) a -> (a -> [b] a) -> [e; b] unit

nested data function:
  exact right-pop countを保ったまま終了する

balanced recursive cycle:
  clampなしで終了する
```

になる。

要するに、

> **std encodingを消して症状を隠すのでなく、field-function boundaryでevidenceをexistentialに閉じる。その後はcanonical full labelを含むexact fact keyを使う。**

これがspecとtermination proofの両方に一番素直に合う修正だよ〜。この環境ではローカルrepoを実行できなかったので動作確認まではしていないけど、両commit・lowering・generalization・proofを突き合わせた限り、この方向がかなり強いと思う。
