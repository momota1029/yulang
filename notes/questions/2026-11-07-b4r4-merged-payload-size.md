# B4r4: variant の合流 payload も、大きさを数える前に冪等化するか

状態: **未承認の一問**（2026-11-07）。spec の変更ではない。
record の canonical residual、隠れた record field を除く N、K2 の両拒否は承認済みとして維持する。

## 問い

**推奨は選択肢1**。同じ tag の合流で生じた同一 payload の重複も、
impl の size と変数出現回数を数える前に取り除く規則にするか。

```yulang
role R 't:
    type value

impl R (:{tick 'a, tick 'a}):
    where :{tick :{box 'a}}: R
    type value = int
```

この source 構文を parser が読むことは確認した。以下の議論の Lean bridge は、
source 全 elaborator ではなく、実 `Variants.Merged.normalize` から実 core head までである。
同名 tag を合流すると、tag は一つだが payload は `union('a,'a)` になる。
型の意味は `:{tick 'a}` と同じである。
record 用 N はこの構文を変えず、現在の実 Paterson 検査は head size4 / child size3、
変数出現回数2 / 1として受理する。一意な捕捉 `'a := T` で、child は `:{tick :{box T}}` になる。
record tail、未解決 goal、再帰型、associated type の展開は使わない。

1. **推奨: 合流 payload の同一 union branch も正規化し、その後に size / 出現回数を数える。**
   この例の head は size2 / 出現回数1となり、size3の child を宣言時に拒否する。
   すでに承認済みの first-field-wins 正規化と canonical residual はそのまま併用する。
   少なくとも `union(P,P) → P` の再帰的縮約を必須とし、より一般の union の並べ替え・結合・分配や
   record/row の同値のどこまでを採用するかは、実 declaration grammar と停止証明で別途詰める。
   この一変更で full B4 E1 が証明できるとはまだ主張しない。
2. **現在の record 限定 N を維持する。**
   その場合、現在の任意 verified core registry に対する「全域かつ exact な有限 resolver」は成立しない。
   意味を保ったまま E1 を主張するには、この core family を除外する追加 checker / source bridge など、
   別の明示された契約変更が必要になる。

推奨案は、解決の深さを切らず、RoleRank を導入せず、nominal body も展開しない。
`CommonRoleMergedExamples.proposed_rejects_minimal` / `proposed_rejects_growing` は、
この family の head を冪等縮約してから実 checker へ渡すと小例を拒否することだけを証明する。
提案全体の soundness / full E1 の証明ではない。

## 障害の強さと、修正 statement

小さい self-loop は `:{tick int, tick int}` を head、`:{tick int}` を where にした一宣言。
head size4 / child size2、変数なしであり、有限辞書は存在しない。
これはこの重複tag recipe の最小構成であって、あらゆる宣言文法にわたる絶対最小性を証明したものではない。

強い E2 は `CommonRoleMergedObstruction.canonical_merged_registry_undecidable`。
任意有限 program を実 registry へ compile し、全宣言が N 固定、実 WF / checker / HDA / AssocWF を満たし、
全 goal は有限木、全 where を含む実有限辞書存在 iff program 停止、を証明した。
したがって、停止するかどうかを正確に答える全域有限 machine も存在しない。
単なる visited cache による self-loop 検出だけでは、この全 program family を解けない。

`CommonRoleMergedSemantic.head_determines_requirements` は、任意 Code の全実宣言について、
任意二 Common 代入の head が同値なら全 where child も同値、という強い条件まで示す。
今回の障害を `HeadDeterminesRequirements` の追加だけで除くことはできない。
一般の複数 tail / open variant row にその条件が必要か、十分か、はこの定理からは出ない。

修正した E1 の**提案**は、元と同じ全有限 verified registry / 全有限 regular goal の量化を保ち、
宣言検査を「record の隠れた field の除去に加え、合流 payload の冪等縮約を実行した後の
size と出現回数」で定義し直したうえで、canonical residual と K2 を含む独立意味論に対する
実全域 resolver の selection / rejection / ambiguity と全実辞書の iff を証明すること。
fuel / success / support / residual を theorem の外部前提に移す案ではない。
この提案は承認待ちであり、現在の theorem 名に追加仮定を入れて E1 として扱っていない。

拒否と曖昧性の優先順位は、既存の
[別の未決質問](2026-11-07-b4r2-rejection-priority.md) のまま。今回の一問では確定させない。
設計と qualified の正確な残りは [設計 note](../design/2026-11-07-b4r4-canonical-residual-and-merged-payload.md)。
