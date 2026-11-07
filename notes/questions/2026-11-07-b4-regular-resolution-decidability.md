# B4 / K2: 正則 goal と宣言時 Paterson 条件の計算可能性

状態: **K2 の E2 を Lean で証明済み**。ユーザー決定（2026-11-07）: 下の第一案 `RoleRank`（role 単位の非巡回）は採らない。引数が小さくなる再帰は許す。
この決定だけでは E2 は解消しない（構造的に小さい規則は既に宣言 checker にあり、反例はそれを通る）。再帰型の goal の扱いが未決で、`spec/06-roles.md` の K2 に移した。

## 承認済み条件と今回の対象

関連型については、監督者からユーザーの承認を受けた意味的条件
`HeadDeterminesAssociated D` を使う。これは、任意の所属 impl と任意の Common 代入 σ,τ に対し、
head の解釈が要求同値なら全 associated RHS の解釈も要求同値になる条件である。
修正後 B4 の宣言前提は `WellFormed D ∧ HeadDeterminesAssociated D`。

今回の構成では、すべての associated RHS は実宣言の定数 `int` であり、この条件を満たす。
同じ有限 visible 集合をすべての where child に使う。どの到達 goal にも異なる候補の overlap はない。
したがって今回の停止問題は、関連型の未決定性や候補の曖昧性とは別である。

## 証明した還元と非存在

任意の有限 Code program と有限 Tree input を、有限の linear root rewrite 規則へ翻訳する。
コピーは有限個の線形規則による明示的な処理であり、変数を複製する規則を混ぜない。
各規則を、実 `Roles.Impl` の一つの where child に翻訳する。

第一引数の clock に、既存の一 node / 一 back edge の正則型 `A ≈ variant 7 A` を使う。
head clock に十分な個数の variant を付けるため、実 `CheckedRoles.checkImpl` の
構文サイズと変数出現回数の条件を通る。しかし Common では同じ clock へ戻れるので、
有限木のサイズ下降は計算の実行回数を制限しない。

`CommonRoleRegularHalting.resolves_exact` / `dictionary_exact` は、任意 code/input に対して、
追加の安全性・停止性・成功前提なしで、生成した registry の独立 Common 解決／有限辞書の存在 iff
その program の停止を示す。

`CommonRoleRegularWire` は、実有限 registry、関連型 RHS、五つの有限 role signature、
一 node の正則 clock を含む有限 goal を具体的な Tree に符号化し、固定の有限 program が
その query を生成することを証明する。任意 decoder や意味的述語を含む入力ではない。
`CommonRoleActualEvidence` は、実 `Roles.Impl` の head / constraints fields を直接読む独立辞書判断と
上の辞書判断を双方向につなぎ、既存 `RoleDictionaries.Plan` の全 child を保存する。

主定理 `CommonRoleRegularResolutionObstruction.amended_registry_undecidable` は前提なしで次を示す。

1. 任意有限 Code program に対し、生成した実 environment は実宣言 checker を通り、
   独立 `Roles.WellFormed`、実 associated scope / completeness、実 stored RHSs に対する
   承認済み `HeadDeterminesAssociated` を満たす。
2. 任意 code/input の上記有限 query で停止し、true iff 独立した実有限辞書が存在する、
   という契約を満たす有限 binary-tape machine は存在しない。

成功／拒否／曖昧性と実辞書を正確に返す全域算法なら、この成功 bit も判定できるため、
修正後 `common_role_registry_exact` の必要成分に対する E2 である。
非計算的な任意 Bool 関数の非存在を述べているのではない。
全体 build は 622 jobs、trust=0 Audit の allowlist は 52025 declarations で通過した。
詳細は [B4 結果](../handoff/2026-11-07-m1-b4-results.md)。

## 修正した statement の提案

元の有限 goal の量化と独立した有限 evidence / dictionary の意味を保つなら、
宣言または利用可能な goal の範囲を、停止を保証する実検査で制限する必要がある。
少なくとも今回の有限計算の埋込みを許さない条件が必要になる。

一つの具体的な修正案は、宣言時に role dependency graph の非巡回性を検査することである。
有限 registry D に対し

```text
RoleRank D := ∃ rank : RoleId → Nat,
  ∀ impl ∈ D, ∀ child ∈ impl.constraints,
    rank child.role < rank impl.role
```

を追加する。finite graph の topological check は decidable で、role rank により
正則型でも再帰 where の深さが有限になる。この案は同じ role への構造的な再帰も拒否するため、
`Display (list a)` が `Display a` を要求する通常の宣言まで制限する。
この使い勝手の変更をユーザーの判断なしに採用しない。

修正後の定理案は次である。

```text
任意の有限 D/V について、
  WellFormed D ∧ HeadDeterminesAssociated D ∧ RoleRank D
の下で、任意の型・行が確定した有限正則 goal description に対する実有限 resolver の
selection / rejection / ambiguity iff 独立 evidence と実 dictionary。
未確定 goal の有限 qualified constraints は任意 Common 代入について解釈する。
```

これは再帰 where の停止に対する修正案であり、一般 Common head matching の決定可能性や
qualified generator の全 family まで、この条件だけで証明済みとするものではない。

別案は、再帰 role SCC で減少に使う引数が非循環であることを実 goal 検査で保証することである。
この案なら有限木上の通常の再帰を残せるが、任意の有限正則 goal を受理する元の量化を変える。
どの引数を制限すれば十分かという checker と、その十分性は未証明である。

coinductive な evidence、無限辞書、fuel による失敗扱いへの変更は、既存の有限 dictionary と
rejection の意味を変える。停止修正の名目で無言に採用しない。

## K1 / qualified 側

この還元には receiver のない method を使わないので、K1 の選択に依存しない。
qualified generator の有限制約生成単体の不可能性は示していない。
実 use-site resolution を含む B4 全体には、ここで示す registry 成分の障害が残る。

## 決定（2026-11-07, ユーザー）

構造的な再帰型が role の型引数に現れる goal は、解決に入る前に拒否する（`spec/06-roles.md` K2）。
B4 の修正 statement は、`RoleRank` ではなく「goal の型・行が有限木であること」を前提にする形に書き直す必要がある。
この前提の下で、全域の実 resolver が存在するかは未証明（E1 の候補）。深い位置の再帰型と nominal な再帰型の扱いは、上の spec の「要確認」を待つ。
