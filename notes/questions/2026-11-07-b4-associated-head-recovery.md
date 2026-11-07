# B4: head から関連型の変数を回収する条件

状態: Lean / build / Audit で確認した E2 障害と、未承認の修正案。K1 / K2 の回答ではない。

出典: `spec/04-types.md` §4.3 の隠れた同名 field の型同値（決定40）、
`spec/06-roles.md` §6.3 の「associated type は head の型引数から決まる一つの型」、
`Roles.AssocHeadVars` / `AssocWellFormed` / `assoc_derivation_agrees`、
`Common.common_shadowed_head_equivalent`。

## 有限の反例

次は一般 union annotation を使わず、named-record type の既存文法に収まる。

```yulang
role R 't:
    type value

impl R ({x: int, x: 'a}):
    type value = 'a
```

where は空である。現在の checker は syntactic な head 内に `'a` が現れることを確認する。
しかし Common の意味では、任意の型 A について `{x:int,x:A} ≈ {x:int}`。
有限の確定 goal `R {x:int}` に対して A=int と A=bool の両方が head instance になる。
二つは同じ impl identity なので、現在の「別の impl 候補が複数」の曖昧性条件に当たらない。
関連型 value はそれぞれ int と bool であり、要求同値でない。

parser の受理と意味的宣言検証は別である。Lean の反例では実 `CheckedRoles.checkDatabase`
と実 `Roles.AssocWellFormed` を検証する。source 全体の elaborator の完成は仮定しない。
実 parser probe も recovery なしで通過した（結果ノート参照）。

主定理 `CommonRoleAssociatedExactness.no_common_associated_registry_extension` は、
実 `assocOf` が二つの ground goal `{x:int,x:int}` / `{x:int,x:bool}` に返す結果を保存し、
Common で同値な goal に同値な関連型を返す関数が存在しないことを示す。
両方が実際に成功するため、ここでは失敗の新しい意味や関連型証拠の transport を仮定しない。
一宣言・一関連型・一変数・空 where の例であり、正則再帰や任意述語の行葉は不要である。

これは ordinary equation を既存 store に連言で追加する法則の反例ではない。
追加後の等式が既存 bounds と矛盾する場合に拒否する規則は、そのまま正しい。

## 承認を求める修正 statement 案

現行 well-formedness だけでは、意味を保つ head matching と既存の全 associated derivation
の一致を同時に要求できない。推奨案は、関連型 RHS の意味が head から決まることを
独立した宣言条件にすること。必要な整合条件の提案であり、全 solver の十分条件や
条件の最小性を証明したものではない。

```text
HeadDeterminesAssociated(D) :=
  ∀ impl ∈ D, ∀ σ τ,
    interpretHead impl σ ≈ interpretHead impl τ →
      ∀ associated RHS rhs of impl, interpret rhs σ ≈ interpret rhs τ
```

修正案は `common_role_registry_exact` の宣言前提を現行 `WellFormed D` から
`WellFormed D ∧ HeadDeterminesAssociated D` へ変えること。
ここで `WellFormed D` は現在の Paterson 条件と `AssocWellFormed` を含む。
`σ,τ` は任意の Common 代入。式・goal・任意 Common 代入の量化は変えない。
これを採用する場合も、有限宣言を実際に検証する check とこの独立条件の関係、正則 where の停止、
qualified generation / 全 parameter family は別に証明する必要がある。
この条件を単に solver の成功前提に置いて E1 完了としない。

具体的な宣言検査案は、head の隠れた同名 field を先に除去し、関連型 RHS が使う
変数の全出現が消える宣言を拒否すること。この例は拒否できるが、全 Common 文法で
これだけが十分とは未証明。where child についても照合代入によらない意味が必要になる可能性があるが、
それは今回の関連型の反例だけから決めず、別に精査する。
別案は、複数の非同値な照合代入を同一 impl 内の曖昧性と定めること、または canonical な代入を
仕様に定めて独立 evidence の意味を変更すること。どちらも現在の意味を変更するため未採用。

K1 は method を使わないこの反例に関係しない。K2 は独立に未解決であり、この修正だけでは解消しない。

結果: [B4 E2 最終報告](../handoff/2026-11-07-m1-b4-results.md)。
この案を採用するかはユーザーの判断であり、今回 `spec/` や既存 checker は変更していない。
