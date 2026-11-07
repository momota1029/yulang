# B4 redo: role goal の root に到達しない再帰型

状態: **E2 証明済み、修正案は未承認**。spec の K2 を書き換えていない。
主定理は `CommonRoleReachedRootObstruction.reached_root_registry_undecidable`。
定義の理由は [reached-root semantics](../design/2026-11-07-b4r-reached-root-semantics.md)。

## 一問

**推奨: role goal だけでなく、head 照合が構造的再帰型の constructor を調べる時点でも拒否する。**
次の impl に `R (:box μ)`（μ は名前の無い再帰型 `μ ≈ :tick μ`）を解決させる場合、
内部の μ を head の `:tick 'a` に照合する時点で拒否する規則へ広げてよいか。

```yulang
role R 't:
    type value

impl R (:box (:tick 'a)):
    where (:box 'a): R
    type value = int
```

これは宣言の Yulang 構文例である。μ の等式は推論された型 graph の数学的表示であり、
再帰型注釈の構文を新設したものではない。receiver-less method は使っていない。

1. **推奨案**: 一意候補を決めるための head 照合で、非変数 pattern が名前の無い循環成分の
   constructor を調べる必要が出たときにも「再帰型のため解決できない」と拒否する。
   `Len (list μ)` の `list 'a` は μ を変数に捕まえるだけなのでそのまま通る。
   `Show (list μ)` の `where Show 'a` は従来どおり `Show μ` へ降りたときに拒否する。
   名前付き型の body は展開しない。深さ制限や RoleRank は導入しない。
2. **単純な強化案**: where を実行する goal は、引数の下のどこに構造的な再帰型があっても拒否する。
   where の無い `Len (list μ)` は通るが、例えば循環部分に触れない定数の where まで拒否する。
   `Show (list μ)` も child に降りる前に拒否され、確定済みの拒否位置を変更する。
3. **現在の規則を維持**: 一般の全域 exact resolver の要求を変更し、未完了を含む部分手続きなどを
   仕様として採る。有限辞書を残しても、全入力で必ず停止する成功判定は得られない。

推奨案でも、重なる候補の一つが循環部分の検査を要求する場合の拒否と曖昧性の優先順序、
全 Common head matching の完全性、停止性は改めて形式化する必要がある。今回の E2 を排除する
具体案であり、推奨案で full B4 の E1 が既に得られるという主張ではない。

## なぜ現在の拒否位置では足りないか

この例の head/where サイズは 3/2、変数の出現回数は 1/1 で、実宣言 checker を通る。
`R (:box μ)` の root は box、循環成分は tick なので、root は自分へ戻らない。
head の照合は `'a := μ` で成立し、where の child はまた `R (:box μ)` になる。
`R μ` という goal は一度も呼ばれない。関連型 RHS は定数 int であり、HDA も妨げにならない。

Lean の `CommonRoleReachedRootExamples` が、実 checker の受理、head 照合、同じ child、
root の非再帰性、再帰型拒否への全有限経路の非存在を示す。
role・impl・型変数・正則 node がそれぞれ一つの最小構成である。
全構文に対する文字数や構文 node 数の最小性は主張しない。

この同一 goal の循環だけなら、cache を持つ算法で扱える可能性がある。
したがってこの例だけから全 resolver 不可能とは結論しない。
既存の pair growing-chain 例 `R(pair(G(G a),b)) requires R(pair(a,G b))` では、
循環 clock を pair の中に残したまま、互いに同値でない無限個の goal を作れる。
今回の強い E2 は、任意有限 program の旧二引数還元を一引数の pair に包み直し、
実 guarded 有限 Dictionary の存在 iff その program の停止を証明して得たものである。

## 提案する amended statement

元の任意有限 description の量化は維持し、成功／拒否／曖昧性の全域 exactness を要求する。
変更するのは独立 semantics の拒否規則である。

```text
任意有限 verified D と caller-visible V、任意型・行が確定した有限 regular goal g に対し、
  WellFormed D ∧ HeadDeterminesAssociated D
の下で、実有限 resolver は必ず停止し、
  (a) g 自身が構造的再帰型を role 引数にする場合、または
  (b) head 照合が構造的再帰型の constructor を検査する必要がある場合
を独立 semantics と同じ拒否として報告し、それ以外の selection / rejection / ambiguity と
全 where child を含む実 dictionary は同 semantics に iff で対応する。
nominal 宣言 body の再帰は展開せず、未解決 qualified constraints は任意 Common 代入で解釈する。
```

新しい外部前提として finite-tree / fuel / support / residual を足す案ではない。
ただし (b) はソースから観測できる規則変更なので、承認前の theorem には用いていない。
宣言 checker と RoleRank の方針も変えていない。推奨案に対する full E1、finite-tree agreement、
nominal agreement、qualified generation の全 family は今後の証明対象となる。
