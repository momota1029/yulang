# Intrude + effect hygiene

Status: Draft
Scope: future Yulang3 Simple-Sub SCC generalization / instantiation design and effect-handler hygiene transport
Approved-by: none
Approved-at: none
Drafted-by: user design discussion + primary assistant
Reviewed-by: none
Supersedes: none

2026-09-29 の設計メモ。

この文書は、Simple-Sub の SCC をほどかずに extrusion 相当を行い、そのまま
単一化・単相化へつなげる `intrude` 案と、将来の effect handler hygiene を
どう合成するかを記録する。

**まだ設計仮説であり、実装指示ではない。**
特に、現行の Authoritative F5 は pure Function subset までを対象としており、
effect generalization はその scope 外にある。本書は F5 を変更・supersede しない。

核となる仮説は次。

> **parent は「何を代入するか」を共有し、effect hygiene evidence は
> 「その代入物をどの boundary 越しに見るか」を edge / binder 側に残す。**

型変数の同一性と、handler からの可視性を同じ情報に畳まない。

## 1. Yulang3 での位置づけ

現在の Yulang3 の scheme / SCC authority は主に次。

- `notes/design/2026-09-21-oracle-aligned-f4-int-scheme-scc-draft.md`
  - static SCC lifecycle
  - internal use は open live root へ接続
  - component 全体を generalize 後に incoming use を instantiate
- `notes/design/2026-09-21-f5-general-function-scheme-foundation-draft.md`
  - polarized Function
  - `Q` / `R` binder
  - closed scheme
  - incoming use ごとの fresh instantiation
  - internal SCC use は fresh binder を作らず live root のまま接続

intrude は、この lifecycle を直ちに置き換える提案ではない。
まず、F5 型の ordinary extrusion / generalization と同じ意味を、
SCC を共有したまま得られるかを検証する研究案として扱う。

Yulang2/main に存在した `StackWeight`, `SubtractId`, `HandlerMatchEdge`,
`ShiftKeep`, `FunctionAdapterHygiene` 等は、effect hygiene を考える際の
**prior art** ではあるが、Yulang3 の現行 authority ではない。
それらの具体的なデータ構造をそのまま移植することは本書の決定ではない。

## 2. Intrude の狙い

通常の extrusion では、境界を越える型変数を fresh variable へ写し、
polarity と level に応じて lower / upper approximation を作る。

intrude 案では、SCC の共有構造を保ったまま、内部変数に
「境界側で対応する parent」を登録する。

概念的には:

```text
internal var ----parent----> boundary var
```

parent 側で substitution が決まれば、component 内部へその substitution を
適用できる。

期待している利点:

- SCC を一度ほどいて再構築しなくてよい。
- component 内の共有構造を保てる。
- generalization と monomorphization の対応が直接残る。
- parent に何を代入したか分かるため、child 側の単相化が簡単になる可能性がある。

ただし、**通常 extrusion が polarity ごとに作る近似を、一つの parent relation で
完全に代替できるかは未証明**である。

ここが intrude 本体の最重要証明義務。

## 3. 型の parent と effect hygiene を分離する

将来 effect hygiene を載せるとき、少なくとも二種類の identity を分ける。

### 3.1 Type parent

```text
P : internal TypeVar -> boundary TypeVar
```

これは substitution の対応。

### 3.2 Hygiene binder / boundary identity

```text
Theta : internal hygiene binder -> instantiated hygiene binder
```

これは「どの boundary を越えた effect か」を capture-avoiding に追跡するための対応。

重要なのは、`P` に hygiene 状態を全部入れないこと。

同じ parent を参照する occurrence でも、

```text
plain(parent)
hidden_boundary(parent)
```

のように handler からの見え方は異なりうる。

したがって、

> **type identity の共有と boundary view の共有は別問題**

として扱う。

## 4. Parent に path history を集約しない

effect hygiene が path-sensitive なら、同じ TypeVar に到達した二つの経路が
異なる boundary history を持つことがある。

危険な形:

```text
parent.hygiene = one_accumulated_state
```

これでは合流した複数経路を一つの node-local state に潰してしまう。

intrude で共有するのは vertex / substitution identity までとし、
hygiene は edge / evidence / binder identity として残す。

候補不変条件:

> **vertex identity は共有してよいが、意味に効く boundary sequence を
> vertex-local な一値へ圧縮してはならない。**

将来の hygiene algebra が非可換なら特に重要になる。

## 5. Graph transport としての intrude

重みや boundary evidence を持つ subtype edge を抽象的に

```text
a @L <: @R b
```

と書く。

intrude 時の最小操作は、

```text
P(a) @Theta(L) <: @Theta(R) P(b)
```

という capture-avoiding transport として定義するのがよさそう。

ここで:

- `P` は TypeVar の対応。
- `Theta` は hygiene binder の対応。
- evidence の payload に型変数があるなら `P` を適用する。
- intrude 自体を理由に boundary の push / pop / keep を発明しない。
- boundary の opening / closing は、その意味論を持つ phase が行う。

つまり intrude はまず **graph identity の移送** として定義し、
effect boundary の生成とは分離する。

## 6. Generalization / instantiation との接続

F5 では、一つの incoming use ごとに `Q` / `R` binder を freshenし、
同じ use 内の同一 binder occurrence は同じ fresh live variable へ写す。
internal SCC use は freshen せず open live root へ接続する。

intrude を導入する場合も、この原則を崩さない。

将来 hygiene binder が加わるなら、候補は:

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

1. type binder を freshen / map する。
2. hygiene binder を freshen / map する。
3. node / edge / evidence 全体へ同じ対応を一貫して適用する。
4. boundary opening evidence が必要なら、その boundary semantics に従って生成する。

### Freshening 単位

必要そうな不変条件:

> 一つの binder に属する全 occurrence は、一回の instantiation 内では
> 同じ fresh identity へ写す。

独立した二回の incoming use は local binder を共有しない。

逆に、outer / imported boundary と共有すべき identity を無条件に freshen しない。

freshening の単位は「同じ SCC か」ではなく、
**binder の lexical / semantic ownership** で決める。

## 7. 単一化・単相化

intrude の魅力は、parent に決まった substitution を内部 graph に再利用できる点にある。

ただし、

> **型が同じになったこと** と
> **handler から同じように見えること**

は別。

候補フロー:

```text
solve parent substitution
    |
    v
apply substitution to internal type graph
    |
    v
apply same type substitution to hygiene-evidence payloads
    |
    v
preserve / instantiate boundary identities
    |
    v
lower concrete boundary evidence to runtime representation
```

child の型を parent substitution で具体化しても、
boundary evidence を同時に消してはいけない。

不要だと証明できた evidence だけを後段で落とす。

compile-time binder identity と runtime の dynamic guard identity も分離する。
runtime freshness が必要な意味論なら、compile-time ID をそのまま runtime ID にしない。

## 8. 証明義務を二段に分ける

effect 付き intrude を一気に証明しようとすると論点が混ざる。

### Lemma A: Intrude correctness

effect hygiene を無視した通常の polarized Simple-Sub graph について、

- SCC を保持する parent-based intrude
- F5 型の generalization / fresh instantiation

が同じ principal solution を表す条件を示す。

少なくとも次を扱う必要がある。

- positive / negative polarity
- lower / upper approximation
- `Q` binder
- productive recursion の `R` binder
- internal SCC use
- incoming use
- alpha-equivalence
- sharing preservation

ここが通らなければ effect hygiene を考える前に intrude 案を修正する。

### Lemma B: Hygiene transport

capture-avoiding な rename / transport

```text
theta = (P, Theta)
```

が hygiene evidence の意味を保存することを示す。

将来の hygiene algebra に composition があるなら、狙う形は:

```text
theta(compose(W1, W2))
  = compose(theta(W1), theta(W2))
```

同様に、

- handler matching
- boundary keep / masking
- residual sharing
- effect-family payload constraints
- delayed boundary evidence

について transport が可換することを確認する。

この二段分割により、

1. intrude 自体の Simple-Sub correctness
2. effect hygiene の保存

を独立に検証できる。

## 9. 最初に固定したい反例 / test

### 9.1 同じ parent、異なる boundary view

同じ effect variable が、

```text
plain occurrence
hidden occurrence
```

の両方に現れる。

期待:

- type parent は共有される。
- handler 可視性の差は残る。

### 9.2 同じ component の独立 instantiation

同じ generalized component を二つの incoming use から instantiate する。

期待:

- local type binder は独立 fresh。
- local hygiene binder も独立 fresh。
- outer identity は必要なものだけ共有。

### 9.3 異なる path history が同じ vertex に合流

同じ TypeVar へ異なる boundary sequence で到達する。

期待:

- vertex sharing は維持。
- path evidence を node-local state 一個へ潰さない。
- intrude 前後で handler visibility が一致する。

### 9.4 recursive SCC

productive recursive Function SCC で `R` binder が生じる。

期待:

- intrude が recursive bound の lower / upper sides を失わない。
- parent sharing が `Q` / `R` identity を混同しない。
- incoming instantiation で recursion sharing が保たれる。

### 9.5 naked effect variable

handler が effect variable の shape をまだ知らないケース。

期待:

- intrude を理由に effect-row shape を発明しない。
- pending hygiene relation のまま保持できる。

## 10. 避けたい設計

現時点では次を避ける。

### parent に hygiene 状態を一個だけ持たせる

複数 path の history が潰れる。

### SCC ごとに hygiene binder を一個へ統合する

binder scope と SCC membership は別物。

### parent substitution が決まった時点で evidence を消す

type equality は hygiene equivalence を意味しない。

### intrude を理由に unknown effect shape を具体化する

graph sharing の変更は effect shape を発明する根拠ではない。

### Yulang2 の hygiene machinery をそのまま移植する

旧 `StackWeight` / `SubtractId` / hidden evidence は prior art。
Yulang3 では必要な意味論を先に定義し、最小 representation を選ぶ。

## 11. 現時点の仮説

一番単純な候補は次。

1. SCC graph は intrude により共有したまま保持する。
2. TypeVar には parent mapping を持つ。
3. effect hygiene は node の恒久属性ではなく edge / hidden evidence /
   binder identity として保持する。
4. generalize / instantiate では type binder と hygiene binder を別々に扱う。
5. parent substitution は graph と evidence payload の両方へ適用する。
6. boundary identity は substitution と別に保持する。
7. runtime representation は compile-time identity から独立して必要な freshness を持つ。

この形なら、

> **SCC を保ったまま substitution を再利用する**

という intrude の利点を残しつつ、effect hygiene を parent へ過剰に押し込まずに済む。

未解決の本丸は effect hygiene そのものより先に、

> **通常 extrusion の polarity ごとの近似を、SCC を保つ parent-based intrude が
> どの条件で正確に代替できるか**

である。

そこが証明できれば、effect hygiene は graph / binder transport の補題として
比較的独立に載せられる可能性が高い。

## 12. 次にやるなら

実装ではなく、まず paper proof / executable characterization を作る。

最小対象は F5 の pure subset:

1. identity Function
2. two-use fresh instantiation
3. productive recursive Function SCC
4. polarity が反転する nested Function
5. ordinary extrusion と intrude の closed scheme alpha-equivalence 比較

この pure subset で intrude correctness が成立してから、
effect binder と hygiene transport を追加する。
