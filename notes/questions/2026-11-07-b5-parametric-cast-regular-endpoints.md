# B5: non-growing cast の endpoint 有限性は正則型へそのまま広がらない

状態: **障害 theorem は Lean 検査済み。仕様修正は未承認。B5 全体の E2 ではない。**

## 確認したい点

`spec/06-roles.md` 6.5 の型サイズ・変数出現数条件から有限な到達 endpoint 集合が出るという説明は、
有限 first-order tree の定理として保持し、正則型では別の探索 theorem を必要とする、と明示するか。

これは `2026-11-07-b5-regular-structural-cast-plans.md` の再帰的 structural traversal の量とは別の問題である。
今回の変換は常に**nominal F 全体の明示 cast**であり、不変型引数の内部への implicit lifting ではない。

## 利用者が書く形

```yulang
struct G 'a { raw: 'a }
struct F 'a 'b { left: 'a, right: 'b }

cast(x: F (G 'a) 'b): F 'a (G 'b) =
    F { left: x.left.raw, right: G { raw: x.right } }
```

source pattern と target pattern はともにサイズ 4 で、`'a` / `'b` の出現数は各一回。
既存の実 `ParametricCasts.Rule.check` はこの endpoint rule を受理する。
本体の意図は純粋な unpack / pack だが、この元 source 本体の Common Typing そのものはまだ接続していない。

引数に有限な一状態 nominal graph `A ≈ G A` を使うと、

```text
F(A,C) → F(A,G C) → F(A,G(G C)) → ...
```

が生じる。`C` は G と別の nominal ID。
各 endpoint description は有限 regular syntax だが、異なる段階の endpoint は nominal invariance により要求同値でもない。

## Lean の正確な statement

`lean/Yulang/CommonParametricCastRegularObstruction.lean`:

- `declaration_accepted` / `declaration_valid`: 上の一つの実 `ParametricCasts.Rule` が既存 checker を通り、その既存 Valid を満たす。
- `loop_unfold`: 専用 nominal 一状態 block の `loop` は `G loop` と要求同値。
- `fire_chain`: 任意 `n : Nat` について、二段の有限 pattern を読む実計算 `fire (chain n) = some (chain (n+1))`。
- `chain_step`: 任意 n について、同じ rule の新 nominal carrier 上の独立 semantic instantiation が chain n → chain (n+1) を与える。
- `chain_equivalent_iff`: 任意 m/n について `Equivalent (chain m) (chain n) ↔ m=n`。
- `chain_reachable`: 任意 n は chain 0 から同じ一規則で到達する。
- `no_finite_regular_endpoint_universe`:

  ```text
  ¬ ∃ candidates : List 新Ty,
      ∀ target, Reach (chain 0) target →
        ∃ candidate ∈ candidates, Equivalent candidate target
  ```

  候補の任意の要求同値正規化を許しても、有限 endpoint universe は存在しない。
  nominal を pair/variant へ置き換えていない。

## 修正案

1. **推奨: 有限 endpoint 列挙の結論を有限 tree に限定し、正則型の探索は別 theorem にする。**

   ```text
   任意有限 verified cast declaration 集合 D と、有限 first-order ground tree の出発型 S について、
   既存 non-growing size/count 条件から、明示 cast の有限到達 endpoint 集合と有限 graph 探索の停止を導く。

   S が有限 regular graph の場合、同じ endpoint 有限性は主張しない。
   既存の受理条件は変更しないが、全 regular boundary の実 keep/search/failure exactness は、
   endpoint 列挙に依らない symbolic reachability 等の独立した停止・完全性 theorem を必要とする。
   ```

   `common_cast_plan_exact_and_pure` の全 regular description という元目標は弱めない。
   その必要な symbolic solver は現時点で未実装・未証明である。

2. **regular endpoint も有限に保つため、parametric cast の受理条件を強める。**

   たとえば「target は source pattern の一つの syntactic subtree」とする computable な条件なら、
   regular instance の既存 substate を返す方向に制限できる。
   この案自体の有限性 theorem はまだ証明していない。
   上のような現在受理される cast を拒否するため、ユーザー承認なしに採用しない。

## 終了判定の境界

この theorem は、正則型に対する**endpoint 有限性**という結論を反証する。
元 B5 cast statement 自体は有限 endpoint universe を結論に含めないので、symbolic な完全算法の可能性は残る。
また、元の nominal source 本体の Common 検証と source からの boundary 実生成は未証明。
したがって、B5 全体が偽／決定不能だと宣言したり、この theorem を B5 終了の E2 として数えたりしない。
