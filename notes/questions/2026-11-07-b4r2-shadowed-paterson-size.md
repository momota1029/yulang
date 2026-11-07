# B4r2: Paterson のサイズ検査から、型の意味で消える部分を除く案

状態: **E2 証明済み。以下の宣言検査変更は未承認**。
主定理は `CommonRoleFiniteShadowObstruction.finite_tree_registry_undecidable`。
承認済みの再帰型 root / head constructor 検査拒否と、旧 root-only E2 は変更していない。

## 推奨する修正

**impl head と where のサイズ・変数出現回数は、隠れた同名 field を型同値どおり除去した後で検査する。**
型の意味から消える ground field に、停止証明のためのサイズを与えない。
この正規化を既存の宣言検査へ適用することを、承認対象の amended statement として提案する。
RoleRank、深さ上限、fuel、無限辞書は使わない。

最小構成の目視例は、role 一つ、impl 一つ、型変数なし、recursive graph なしの次である。

```yulang
role R 't:
    type value

impl R ({x: int, x: int}):
    where {x: int}: R
    type value = int
```

raw head/child サイズは 5/3 なので既存 checker は受理する。しかし型の意味は両方とも `{x:int}`。
goal `R {x:int}` には構造的再帰型が一つもなく、承認済み K2 の両拒否規則は作用しない。
head の第二 field を除いて検査すればサイズは 3/3 で、真に小さいという条件を満たさない。

同じ goal の cache だけで足りない例も、型変数一つで作れる。以下は上の例と別の registry である。

```yulang
role S 't:
    type value

impl S ({x: 'a, x: int}):
    where {x: :{tick 'a}}: S
    type value = int
```

raw サイズは 5/4、変数出現回数は 1/1 で受理される。
`S {x:int}` → `S {x::tick int}` → `S {x::tick (:tick int)}` → … と、
すべて有限木で互いに Common 同値でない goal が続く。
正規化後は 3/4 なので宣言時に拒否される。
`normalized_examples_rejected` は、この二例についての実 checker の結果を Lean で示す。
実 checker 自体は変更していない。

## 有限 chain だけではなく、算法の非存在まで示した理由

目視例や自然数の減少関数の非存在だけでは、別算法による全域判定を否定できない。
今回の強い E2 は、任意有限 program の各線形 data rule left→right を次へ翻訳する。

```text
head  R {x:left, x:G^k int}
where S {x:right}
k = rawSize(right) + 1
```

第二 field は閉じた有限木なので、HDA と where の変数の決まり方に問題を加えない。
型同値では消えるが、raw checker は数えるため任意の線形 rule に十分な padding が入る。
その実 registry の独立 amended 有限辞書の存在 iff program の停止を証明した。
実 head/where/key/associated RHS/signature と有限 goal の wire を入力とする
finite tape machine の全域成功判定を対角化で否定している。

## 修正後 statement の提案

有限宣言構文の正規化 N を明示し、少なくとも同名 field の隠れる部分を除く。
N は head 照合の Common 意味を保存することを別に証明する。
宣言 checker は raw な head/where に直接サイズを付ける代わりに、N(head)/N(where) へ既存の
真のサイズ下降と変数出現回数の検査を行う。関連型 RHS が正規化後 head から決まるという HDA は維持する。

```text
任意有限 D/V、任意型・行が確定した有限 regular goal g に対し、
  NormalizedPaterson D ∧ HeadDeterminesAssociated D
の下で、承認済み root+constructor 検査拒否を含む実有限 resolver は必ず停止し、
独立 semantics の selection / rejection / ambiguity と全実 dictionary に iff で対応する。
未確定 qualified constraints は任意 Common 代入で解釈する。
```

変更するのは宣言 checker の前提であり、任意有限 goal の量化や where の呼出側 visible 集合は変えない。
N の全言語に対する定義、soundness、decidability と、この強化が full B4 の E1 に十分であることは未証明。
同名 field を除くだけで全 Common 型・row のすべての同値則に対して停止が保証される、と先取りしない。
今回の二例と padding family を排除する具体的な修正案である。

関連型の既存承認条件は、右辺で使う変数の一意性を扱う。この ground padding を
自動的にサイズ検査から除く規則にはならないので、追加の変更として記録する。
単に実 head matching を raw な構文一致へ戻す案は、型の正本が定める同名 field の型同値を変える。
今回の提案はその型同値を維持する。
