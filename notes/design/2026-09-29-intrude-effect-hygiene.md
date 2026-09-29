# Intrude + effect hygiene design memo

状態: **working memo（未決定・実装指示ではない）**

2026-09-29 の設計検討メモ。

Simple-sub の SCC を壊さずに extrusion 相当を行い、そのまま単一化・単相化まで
つなげる `intrude` 案に、Yulang の effect handler hygiene をどう載せるかを整理する。

このメモの結論候補は次の一文に尽きる。

> **parent は「何を代入するか」を共有し、effect hygiene evidence は
> 「その代入物をどの boundary 越しに見るか」を edge / binder 側に残す。**

型変数の同一性と、handler からの可視性を同じ情報に畳まない。

関連する現行文書:

- `docs/hidden-effect-evidence.ja.md`
- `notes/design/handler-row-subtraction.md`
- `spec/2026-05-31-effect-variable-subtractable.md`
- `spec/2026-06-13-mono-vm-contract.md`
- `crates/infer/src/instantiate.rs`

---

## 1. Intrude 側の狙い

通常の extrusion のように SCC を一度ほどいて fresh variable 群へ写す代わりに、
SCC の共有構造を保ったまま、内部変数に「境界側の parent」を登録する。

概念的には:

```text
child var  ----parent----> boundary var
```

単相化時には parent に決まった代入を child 側へ再利用する。

この方式の期待値は次の通り。

- SCC の共有構造を保持できる。
- extrusion と同程度の bookkeeping で済む可能性がある。
- parent に決まった substitution を使って、その component 内の単相化を
  まとめて行いやすい。
- 同じ graph を何度もほどいて再構築する必要を減らせる可能性がある。

ただし、通常の Simple-sub extrusion が polarity ごとの近似を作る部分まで
単一 parent で置き換えてよいかは別問題であり、このメモでは証明済みとしない。

---

## 2. Effect hygiene で分けるべき二つ

Yulang では、同じ surface type / effect row でも hidden evidence が異なれば
handler からの見え方が異なりうる。

現在の実装・設計では、少なくとも次の情報が型そのものとは別に存在する。

- `ShiftKeep` / `HandlerMatchEdge`
- thunk / handler boundary evidence
- `SubtractId`
- `StackWeight`
- scheme の `stack_quantifiers`
- specialize 後の `FunctionAdapterHygiene`
- runtime の fresh `GuardId`

したがって intrude では、次の二つを分ける。

### A. 型の parent 対応

```text
P : internal TypeVar -> boundary TypeVar
```

これは「この internal variable に、最終的にどの substitution を適用するか」を表す。

### B. hygiene binder / boundary の対応

```text
Theta : internal hygiene binder -> boundary / instantiated hygiene binder
```

これは boundary identity を捕捉回避的に移すための対応である。

重要なのは、**P に hygiene 状態を全部押し込まないこと**。

同じ parent を参照する二つの occurrence があっても、

```text
plain(parent)
hidden_boundary(parent)
```

のように、見え方の差は残りうる。

---

## 3. Parent 共有で消してはいけないもの

危険なのは、各 TypeVar に「現在の effect depth」「現在の weight」などを一個だけ
持たせ、それを parent へ集約する設計である。

effect hygiene evidence は一般に path-sensitive であり、同じ変数へ到達しても
通った boundary の列が違えば意味が違う。

特に stack weight 系では、演算順序が意味を持つ。

`spec/2026-05-31-effect-variable-subtractable.md` の replay は概念的に:

```text
left  = earlier.left ; later.left
right = later.right ; earlier.right
normalize_directed_mix()
```

であり、単純な可換加算ではない。

そのため、

```text
vertex -> one parent
```

は共有してよいが、

```text
all incoming paths -> one accumulated hygiene state
```

へ潰すのは避ける。

候補不変条件:

> **vertex identity は共有しても、boundary evidence の列・edge identity・binder identity は
> 必要な範囲で保持する。**

---

## 4. Intrude の graph 変換候補

重み付き subtype edge を概念的に

```text
a @L <: @R b
```

と書く。

intrude が graph を boundary 側へ移すとき、まず候補として

```text
P(a) @Theta(L) <: @Theta(R) P(b)
```

のような capture-avoiding rename / transport として扱う。

ここで注意する点:

- `P` は TypeVar の対応。
- `Theta` は `SubtractId` 等の hygiene binder の対応。
- `L` / `R` 内に型 payload がある場合は、そこにも `P` を適用する。
- intrude 自体を理由に take / pop / keep / delimiter を増減させない。
- boundary の opening / closing は、それを意味論的に行う既存処理に任せる。

つまり intrude はまず **graph identity の移送** として定義し、
handler boundary の生成そのものとは分離する。

---

## 5. Scheme instantiation との接続

現行 `crates/infer/src/instantiate.rs` は、型変数と `SubtractId` の対応を
別 map として持つ。

概念的には:

```text
type vars:  source TypeVar  -> fresh TypeVar
subtracts:  source SubtractId -> fresh SubtractId
```

intrude でもこの分離を保つ。

component を generalized / frozen な形で保持するなら、候補表現は例えば:

```text
IntrudedComponent {
    graph,
    roots,
    type_binders,
    hygiene_binders,
    parent_map,
}
```

use-site instantiation では:

1. 型 binder を freshen / map する。
2. hygiene binder を freshen / map する。
3. graph の node / edge / evidence 全体へ同じ対応を一貫して適用する。
4. use-site boundary で必要な opening evidence は既存の意味論に従って挿入する。

### Binder freshening の単位

必要そうな不変条件:

> 一つの binder に属する全 occurrence は、一回の instantiation 内では
> 同じ fresh identity へ写す。

逆に、独立した二回の instantiation で local binder を不用意に共有しない。

ただし、imported boundary のように外部と identity を共有するものまで freshen してはいけない。
「SCC に属するか」ではなく「binder の scope / ownership」が freshening 単位になる。

---

## 6. HandlerMatch / ShiftKeep との関係

`docs/hidden-effect-evidence.ja.md` では、handler hygiene を ordinary row 型へ埋め込まず、

```text
HandlerMatchEdge(actual, keep, handled, residual)
```

のような hidden evidence として分離する。

これは intrude と相性がよい。

intrude 後も、

```text
P(actual)
P(residual)
Theta/clone(keep / boundary identity)
handled payloads with P
```

のように evidence を transport すればよい。

特に、

```text
handler_match(epsilon, Surface, {io}, rho)
```

から

```text
epsilon = [io | rest]
```

を発明してはいけない、という既存不変条件はそのまま維持する。

intrude は graph の共有方式を変える案であって、
naked row variable を開く根拠を増やす案ではない。

---

## 7. 単一化・単相化

intrude の大きな利点は、parent に決まった substitution を component 内へ
再利用できることにある。

ただし、

> **型が同じになったこと** と
> **handler から同じように見えること**

は別である。

候補フロー:

```text
solve parent substitution
    |
    v
apply substitution to internal type graph
    |
    v
apply same type substitution to hygiene evidence payloads
    |
    v
preserve / instantiate boundary identities
    |
    v
derive specialize-time FunctionAdapterHygiene
    |
    v
runtime callごとに fresh GuardId
```

つまり、child の型を parent の substitution で具体化しても、
edge / hidden evidence を同時に消さない。

specialize 後に不要だと証明できた evidence だけを落とす。

また、compile-time の `SubtractId` / binder identity と runtime の `GuardId`
を同一視しない。runtime guard は adapter call 等で dynamic fresh に生成される。

---

## 8. 証明を二段に分ける

effect 付き intrude 全体を一気に証明しようとすると論点が混ざる。

まず次の二つに分ける。

### Lemma A: Intrude correctness

effect hygiene を無視した通常の Simple-sub graph について、
SCC を保つ parent-based intrude が extrusion / generalization と同じ解を与える条件を示す。

ここには polarity、lower/upper approximation、recursive SCC の扱いが入る。

### Lemma B: Hygiene transport

capture-avoiding な rename / transport `theta = (P, Theta)` が、
hygiene evidence の意味を保存することを示す。

狙う形:

```text
theta(compose(W1, W2))
  = compose(theta(W1), theta(W2))
```

同様に、

- directed mix
- handler_match
- row split / residual sharing
- family payload constraint
- boundary keep

について可換性を確認する。

Lemma B は、「intrude が graph の形を共有すること」そのものより、
**binder identity と edge evidence を潰さないこと**に依存するはず。

この二段分割なら、intrude 自体の Simple-sub 上の正しさと、
effect hygiene の保存を独立に調べられる。

---

## 9. 最初に固定したい反例 / test

### 9.1 同じ parent、異なる boundary view

同じ row variable が、

```text
plain occurrence
hidden / shifted occurrence
```

の両方に現れる。

期待:

- TypeVar parent は共有される。
- handler 可視性の差は残る。

### 9.2 同じ component の独立 instantiation

同じ generalized component を二箇所で instantiate する。

期待:

- local type binder は独立 fresh。
- local hygiene binder も独立 fresh。
- imported / outer binder は必要なものだけ共有。

### 9.3 異なる path history が同じ vertex に合流

同じ TypeVar へ、異なる stack / boundary sequence で到達する。

期待:

- vertex sharing は維持。
- path evidence を vertex-local state 一個へ潰さない。
- replay 結果が intrude 前後で一致。

### 9.4 function / record / thunk 内部の effect

effectful callback を record や関数値に入れ、別 boundary から呼び出す。

期待:

- parent substitution 後も hidden evidence が値側へ残る。
- specialize が `FunctionAdapterHygiene` を構成できる。
- runtime guard freshnessを壊さない。

### 9.5 naked effect variable

```text
handler_match(epsilon, Surface, {io}, rho)
```

の `epsilon` が naked variable のまま intrude / unify されるケース。

期待:

- intrude を理由に row shape を発明しない。
- pending hidden evidence のまま保持できる。

---

## 10. やらない方がよさそうな設計

現時点では次を避ける。

### parent に hygiene 状態を一個だけ持たせる

```text
parent.hygiene = accumulated_weight
```

のような設計。

複数 path の history が潰れる可能性がある。

### SCC ごとに SubtractId を一個へ統合する

binder の scope と SCC membership は別物。
独立 instantiation や nested boundary の identity を壊しうる。

### parent substitution が決まった時点で evidence を消す

型 equality / substitution は hygiene equivalence を意味しない。

### intrude を理由に handler_match を解く

intrude は row shape を増やす根拠ではない。

---

## 11. 現時点の設計仮説

一番単純な候補は次。

1. SCC graph は intrude により共有したまま保持する。
2. TypeVar には parent mapping を持つ。
3. effect hygiene は node の恒久属性ではなく、既存どおり edge / hidden evidence /
   binder identity として保持する。
4. generalize / instantiate では type binder と hygiene binder を別々に freshen する。
5. parent substitution は graph と evidence payload の両方へ適用する。
6. boundary identity は substitution と別に保持する。
7. specialize が concrete boundary evidence から `FunctionAdapterHygiene` を作る。
8. runtime は compile-time identity を再利用せず、call ごとに fresh `GuardId` を作る。

この形なら、intrude の利点である「SCC を保ったまま substitution を再利用する」を残しつつ、
effect hygiene を親変数へ過剰に押し込まずに済む。

未解決の本丸は、effect hygiene そのものよりむしろ、

> **通常 extrusion の polarity ごとの近似を、SCC を保つ parent-based intrude が
> どの条件で正確に代替できるか**

の方に見える。

そこが証明できれば、hygiene 側は graph / binder transport の補題として
比較的独立に載せられる可能性が高い。
