# B4: head から関連型の変数を回収する条件

状態: 検証中の障害と修正案。仕様変更は未承認。K1 / K2 の回答ではない。

出典: `spec/04-types.md` §4.3 の隠れた同名 field の型同値（決定40）、
`spec/06-roles.md` §6.3 の「associated type は head の型引数から決まる一つの型」、
`Roles.AssocHeadVars` / `AssocWellFormed` / `assoc_derivation_agrees`、
`Common.common_shadowed_head_equivalent`。

## 有限の反例候補

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

## 承認を求める修正 statement 案

現行 well-formedness だけでは、意味を保つ head matching と既存の全 associated derivation
の一致を同時に要求できない。推奨する最小条件は、使用する変数の意味的回収可能性である。

```text
HeadDeterminesUses(D) :=
  ∀ impl ∈ D, ∀ σ τ,
    interpretHead impl σ ≈ interpretHead impl τ →
      (∀ associated RHS rhs of impl, interpret rhs σ ≈ interpret rhs τ)
      ∧ (∀ where child of impl, interpretGoal child σ ≈ interpretGoal child τ)
```

修正案は `common_role_registry_exact` の宣言前提を現行 `WellFormed D` から
`WellFormed D ∧ HeadDeterminesUses D` へ変えること。式・goal・任意 Common 代入の量化は変えない。
これを採用する場合も、有限宣言を実際に検証する check とこの独立条件の関係、正則 where の停止、
qualified generation / 全 parameter family は別に証明する必要がある。
この条件を単に solver の成功前提に置いて E1 完了としない。

実装可能な十分条件の候補は、head の隠れた同名 field を先に除去し、関連型 RHS / where が使う
変数の全出現が消える宣言を拒否すること。ただし全 Common 文法でこれだけが十分とは未証明。
別案は、複数の非同値な照合代入を同一 impl 内の曖昧性と定めること、または canonical な代入を
仕様に定めて独立 evidence の意味を変更すること。どちらも現在の意味を変更するため未採用。

K1 は method を使わないこの反例に関係しない。K2 は独立に未解決であり、この修正だけでは解消しない。
