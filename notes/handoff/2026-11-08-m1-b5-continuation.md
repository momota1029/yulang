# B5/B1: 宣言ごとの variance の継続結果 (2026-11-08)

状態: 部分。B5/B1 の E1/E2 には達していない。
作業 0 の監査に従い、旧 all-invariant carrier を一般 nominal model として使わない。
`spec/06-roles.md` 6.5 の宣言時 variance と中心なし区間を基準とする。

## 1. 宣言表を参照する実有限 inspector

`lean/Yulang/CommonDeclaredNominalInspection.lean`。
既存 `CommonNominalConstraints.ArgumentTerm` / `HeadTerm` と
`CommonNominalHeads.Argument` / `Head` を再利用し、別の型 carrier を導入しない。
有限宣言表は nominal ID を添字とし、各引数の kind と variance を保持する。
この表の variance は宣言時に既に計算されたものを受け取る。

主要定理 `inspect_exact`:

> 任意の有限宣言表 `registry`、任意の二つの nominal head 記述 `first, last`
> （順序を持つ、任意の元 Common 型項・行項の引数列）、任意の独立な元 computation
> assignment `ρ` について、実 `inspect registry first last` が返す有限の通常型／行不等式を
> 同じ `ρ` がすべて満たすことと、同じ表の宣言が見つかり、両引数列の arity/kind が宣言に合い、
> 宣言 variance を使う既存 nominal demand 順序で `first.eval ρ ≤ last.eval ρ` が成り立つことは同値である。

covariant は正方向、contravariant は逆方向、invariant は両方向、unused は不等式なし。
unused の位置でも kind/arity を検証するため、欠けた表要素を `modeAt = unused` として
無検査で受理しない。元型／行項をそのまま不等式に入れ、共有された変数と元順序を保持する。
未知の ID、異なる ID、arity/kind の不一致は、実 inspector の `none` によって拒否する。

補助 `arguments_demand_exact` は、任意宣言と任意実 head 二つについて、
検証済み kind/arity と既存 head-demand 順序の組を、宣言各位置の独立な比較判断へ結ぶ。

この定理は actual instance 間の比較であり、open 不変区間の中心を選ぶ規則ではない。
open bounds は元共有 slot に別途積む。再帰的な source 宣言から variance を導く checker、
全再帰 nominal carrier、source construction、weak variable の後の利用／EOF、
元 source branch の union/readback は未証明である。

検証: `lake build --wfail Yulang.CommonDeclaredNominalInspection` と
`lake build --wfail` は終了コード 0。新主要 theorem 三つの直接 `trust=0` 公理監査は
すべて `[propext, Quot.sound]` のみ。共有 `Audit.lean` への登録と統合後の全体監査は親が行う。

## 2. 元共有 slot への特殊化と solver 文法の内部導出

`lean/Yulang/CommonDeclaredNominalSlots.lean` は、上の実 inspector に、元の型／行変数を
そのまま引数として渡す。別の比較アルゴリズムへ置き換えていない。

- `inspect_all_exact`: 任意の有限宣言表、任意の有限 nominal 比較列、任意の独立な元 computation
  assignment について、実 `inspectAll` の返す有限 atom 列の全充足 iff 同じ assignment での
  全元比較の declaration-validated demand 順序。複数比較と複数引数に同じ slot が現れれば、
  一つの値／行をそのまま共有する。
- `inspect_all_grammar`: 任意の有限宣言表・任意の元 slot 比較列・任意の実返却 atom 列について、
  返却 atom は既存 `CommonBoundRefSolvedExact` が要求する child grammar・width atoms・row shape
  の三つをすべて満たす。これらは inspector の出力から証明され、parameter への条件ではない。

このため、既存 source が生成した clause に宣言 variance の slot 制約を追加しても、
既存の Common worklist と全 parameter family を再利用できる。次の packet で接続する。
full nominal source の構築や、再帰 nominal carrier の実装を完了したとは主張しない。

検証: 対象 module の `lake build --wfail` と全体 build が成功。
上の二定理の直接 `trust=0` 監査は `[propext, Quot.sound]` のみ。
