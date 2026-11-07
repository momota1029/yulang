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

## 3. 元 source の全共有 slot と既存 solved worklist への接続

`lean/Yulang/CommonDeclaredNominalSourceFamily.lean`。
実 `inspectAll` の atom を元 clause に追記し、全体を **一回の既存 Common graph compiler / solved worklist** に渡す。
別の scalar solver、nominal 専用 semantic carrier、外部 compatibility oracle を増設しない。
scheme に格納するのは、実有限 atom 列と既存 solved scheme の有限構文だけである。

主要定理:

- `all_parameters_models`: 任意の有限宣言表、任意の元有限 Common atom 列、任意の元共有 slot 上の
  nominal 比較列、実 `solve` が返す任意の scheme、任意の全 row parameter vector と
  その scheme の全 value parameter tuple に対して、実 instantiate の **全元 slot** は、
  元 atom 列と全 declaration-aware nominal 比較を同時に満たす。
  parameter に Models・Consistent・ResidualHolds・support の条件を課さない。
- `solve_all_instances_exact`: 同じ任意の表／atom 列／比較列について、元 atom 列が既存 child grammar・
  width atoms・row shape の三つを満たすとき、任意の独立な元 computation assignment が
  元 atom と全 nominal 比較を同時に満たすこと iff 実返却 scheme と無制約の parameter が存在し、
  **全元行を literal equality、全元型を Common の要求同値で同時に回収する**。
  nominal inspector 側の三つの文法条件は §2 から内部で導く。
- `generated_models_exact`: 任意の実 `Inference.Expr`、その元 principal generator の normalise が返す
  任意の clause、任意の有限宣言表、任意の元 packed slot 上の nominal 比較列、任意の独立な全元
  computation assignment について、上の全 model／全 scheme-instance の iff。
  元 clause の三つの文法条件も、実生成の事実から内部で導く。
- `generated_core_models_exact`: 同じ主張を、任意の元 `Core.Required.Term` と実 `principalCore` が
  生成する任意の clause に対して証明する。unsupported な source を成功扱いする変更はない。

`AssignmentEquivalent` は出力一個だけでなく、元のすべての局所型 slot とすべての行 slot を比較する。
同じ slot を複数の nominal 引数／異なる比較で使う共有は変えない。
旧 `Common` の record/default/arrow の相関を、別々の scalar family に分解して失わない。

範囲の限界: 元 source clause の Common 型 slot に declaration-aware nominal **metadata 制約**を追加する橋である。
nominal 値を `Common.Ty` の中に新設したり、list/struct の source AST を元 generator が処理できるようにしたりしたわけではない。
open 不変区間の具体的な source 生成、宣言からの variance 導出、full nominal carrier、source construction/cast/EOF は残る。
この部分結果を B5/B1 の E1/E2 とは数えない。

検証: 対象 module の `lake build --wfail`（190 jobs）と全体 build（1009 jobs）が終了コード 0。
直接 `trust=0` 監査では、compile の主要定理は `[propext, Quot.sound]`、solver/source の主要定理は
`[propext, Classical.choice, Quot.sound]` のみ。追加の公理・`sorry`・`native_decide` は導入していない。

## 4. 宣言上 invariant の元引数だけへの中心なし区間 attachment

`lean/Yulang/CommonDeclaredInvariantBounds.lean`。
有限 occurrence 記述は元 head、引数位置、下限と上限の元 slot 参照だけを持つ。
actual はその head のその位置から読み、区間の中心を別に選んだり保存したりしない。

主要定理 `inspect_all_exact`:

> 任意の有限宣言表、任意の元 slot を参照する有限 occurrence 列、任意の独立な元 computation
> assignment について、実 interval inspector の返却 atom 列を同じ assignment がすべて
> 満たすこと iff 各 occurrence の宣言／位置が実表に存在し、その位置の宣言 variance が
> invariant であり、head 全体の arity/kind が宣言と一致し、同じ元 actual が同じ kind の
> 下限以上かつ上限以下にある。

covariant・contravariant・unused の位置にこの操作を適用すると `none` になる。
head 全体を同じ既存 declaration-aware inspector で検査するため、選ばれた一位置だけが
正しくて残りの arity/kind が壊れた head を受理しない。
補助 `select_exact` は実有限 lookup と独立な selection 判断の同値、`value_interval_exact` は
値引数について旧世代の中心なし `CommonInvariantIntervals.Holds` と同じ不等式であることを示す。
返却 atom はすべて元型／行変数二つの通常の不等式である（`inspect_all_slots`）。

occurrence の出所は外部であり、この packet は source がどこで deferred cast や interval
attachment を生成するかを定義しない。同じ元 slot を複数 occurrence が参照する共有は保持する。
未確定の cast 適用範囲、recursive variance 判定、full nominal source を新たに決定した結果ではない。
§3 の Core 系の corollary は legacy `CoreRules.principalCore` / `InferenceSyntax.supported`
の境界であり、より新しい `CommonSyntax` の default/case generator を扱ったとは主張しない。

検証: 対象 module の warning-as-error build と全体 build が成功。
`select_exact`・`interval_atoms_exact`・`inspect_all_exact`・`inspect_all_slots` の直接 `trust=0`
監査は `[propext, Quot.sound]` のみ。

## 5. 宣言 variance と不変区間を同じ source family で同時に充足

`lean/Yulang/CommonDeclaredInvariantSourceFamily.lean` の `all_parameters_models`:

> 任意の有限宣言表、任意の元有限 atom 列、任意の元 slot 上の nominal 比較列と interval
> occurrence 列、実 `solve` が返す任意の scheme、任意の row parameter vector とその scheme の
> value parameter tuple に対して、実 instantiate の全元 slot は、元 atom、全宣言 variance
> 比較、全宣言上 invariant の同じ actual に対する下限／上限を同時に満たす。

元の nominal source family に実 interval inspector の返却 atom を渡すだけであり、全体が
一つの既存 Common graph compiler / solved worklist に入る。二つ目の solver や parameter
条件は追加しない。元 source、比較、区間の間で同じ slot が共有されることも変わらない。
この packet は全 parameter の健全性であり、全元 model の回収は次の補題で結ぶ。

検証: 対象 module の `lake build --wfail`（194 jobs）成功。
主要定理の直接 `trust=0` 監査は `[propext, Classical.choice, Quot.sound]` のみ。
