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

## 結論

根治は **std の `ref_update/update_effect` 符号化を捨てることではなく、data-position に埋め込まれた関数の返り effect tail を private / existential にすること**だと思う。

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

## 実装順

1. いったん `3daadaaf` のtermination guardを残す
2. synthetic field getter codomainへprivate tail/id scopeを導入
3. public owner変数へ`declared_subtract_fact`を付けない
4. getter instantiation時にprivate tail/idをfreshen
5. method generalization前にprivate tailをordinary public rowへprojectし、private var/idのescapeをassert
6. replayをcanonical exact full-label keyへ統一
7. self-tail no-opとresidual hash-consを確認
8. clampと`var_var_pop_replay_seen`を同時に外す

追加するcanaryは少なくとも、

```text
synthetic getter:
  receiver argに Stack/weighted self-aliasがない

ref.update:
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
