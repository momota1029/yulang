# B5 → B1: 宣言 variance / 不変区間の途中結果 (2026-11-08)

状態: **作業中。B5/B1 全体の E1/E2 は未達。**
二回目までのユーザー訂正を反映した [設計ノート](../design/2026-11-08-b5-interval-invariance.md) が解釈の基準。
nominal 全引数の不変性は仮定しない。box は共変、無限に入れ子となる list/tree の引数は不変。
以下の nominal reconciliation は **不変と宣言された位置の補助**であり、一般 nominal carrier の theorem ではない。

## 1. 区間代数と既存 finite constraints の再利用

`lean/Yulang/CommonInvariantIntervals.lean`。endpoint carrier は既存 Common.Ty のままで、区間 data は lower/upper の組だけ。

- `holds_merge_exact`: 任意 Common interval I/J と任意実型 t について、`(I.lower | J.lower, I.upper & J.upper)` が同じ t を含む iff I と J の両方がその t を含む。
- `merge_consistent_exact`: 任意 I/J について、merge の lower≤upper iff 元各区間二つの lower≤upper と、I.lower≤J.upper・J.lower≤I.upper の二つの交差条件。
- `consistent_iff_actual` / `shared_actual_exact`: 任意区間（または同じ実引数の区間対）で、lower≤upper（または元二条件＋全交差条件）iff 元全 bounds を満たす一つの実型がある。証明 witness は lower（merge のときは union lower）。これは代数的存在と既存 bounds の最小解であり、source cast の target を任意に選ぶ規則ではない。
- `collapsed_merge_exact`: 任意 Common 型 T/U について、(T,T) と (U,U) の同一不変 slot merge が整合する iff T と U が要求同値。
- `shared_bound_variables_equal`: 任意 I/t/x/y について、x/y のそれぞれが I.lower 以下かつ I.upper 以上にあり、I が t を含むなら x と y は要求同値。区間の両側に出る変数の局所等式に対応する。具体 constructor の global sandwich と同一視しない。
- `compile_models_exact`: 任意 slots 数、任意 `(元slot, lower/upper)` 有限 occurrence 列、任意元 flow 列・全 actual assignment で、実 LayerBoundTemplates への compile の CommonBoundCoalescing.Models iff 全元 interval occurrence/flow の独立 Models。同じ元 slot の各 occurrence は一つの actual assignment を共有する。
- `all_models_recovered` / `models_family_exact`: 同じ任意 finite problem について、既存 expand をそのまま使い全元 slot の全 model を同値で回収する。任意 fixed endpoints の Consistent はこの代数 theorem の明示条件であり、この段階だけで実 checker 完了とはしない。

直接 warnings-as-errors、全体 build 716 jobs、fresh 独立 trust=0 検査を通過。独立公理 allowlist 全 8337 宣言を通過。

## 2. closed scalar endpoints の実 checker と全 parameter family

`lean/Yulang/CommonGroundIntervalSolver.lean`。

- `check_exact`: 任意 slots 数と、既存 scalar finite syntax を固定 endpoint とする任意 LayerBoundTemplates problem（lower/upper/flow/check）で、実 rigid comparison 列を既存 CommonGroundScalarCasts.check で計算した Bool が true iff 元 Consistent。
- `all_parameters_models`: 任意同 problem、実 solve が返す任意 scheme、任意 **Fin slots→Common.Ty 全体**の parameter で、既存 expand の全元 Models。parameter は scalar/finite type に制限せず、regular graphs/default/mask/arrows も含む。前提は実 membership だけで、Models/Consistent を parameter の条件に残さない。
- `solve_all_instances_exact`: 同じ任意 problem と任意元全 actual assignment で、元全 Models iff 実返却 scheme と無制約 parameter が全元 slot を同値で回収する。実装は既存 expand で、回収 tuple は元 assignment 自体。
- `interval_solve_all_instances_exact`: 任意 scalar lower/upper occurrence 列と任意元 flow・全 actual assignment で、同じ独立 interval Models iff 同じ実返却 family の全元 slot 回収。
- `rejected_iff`: 同じ任意 problem で、返却リストが空 iff 元 Models が存在しない。

外部 compatibility oracle は受け取らない。直接 warnings-as-errors、全体 build 717 jobs、fresh trust=0 / 公理 allowlist 全 9509 宣言を通過。
この endpoint grammar の solver を、一般 nominal/source/row solver の完了とはしない。

## 3. 不変位置に限る nominal metadata reconciliation

`lean/Yulang/CommonNominalIntervalReconciliation.lean`。既存 CommonNominalHeads.Head と既存 Common 型/行を actual model に使い、新 carrier/order を導入しない。

- `row_merge_exact`: 任意の二つの arbitrary signed-occurrence-set row bounds と任意同じ actual row に対して、lower union/upper intersection merge の充足 iff 元二区間の同時充足。
- `nominal_merge_models_exact`: 任意 nominal ID 二つ、任意長の型／行 interval argument 列二つ、任意既存 actual Head について、実 merge の返却記述の充足 iff 元二記述の同じ actual Head に対する充足。実関数が ID/arity/ordered kind の不一致を拒否し、各下界・上界と元位置を保持する。**全対象位置が Invariant の局所補題**で、共変 box の merge には使わない。
- `arguments_holds_length`: 任意 interval argument 列と actual argument 列の充足から、全元 arity の一致を導く。
- `point_head_holds_exact`: 任意既存 Head 二つで、元各引数を collapsed bounds にした充足 iff ID/arity 一致・全対応引数の要求同値。これは Invariant の collapsed case に限る旧 point rule の位置付け。

直接 warnings-as-errors、全体 build 718 jobs、fresh trust=0 / 公理 allowlist 全 8573 宣言を通過。

## 4. 実行した関門と未実行

再開時 baseline 715 jobs、以後 716/717/718 の各 `lake build --wfail` は終了コード 0。
最新の build 末尾:

```text
✔ [716/718] Built Yulang.CommonNominalIntervalReconciliation (802ms)
✔ [717/718] Built Yulang (478ms)
Build completed successfully (718 jobs).
```

各新 packet の独立 trust=0 検査・公理 allowlist は上記。新三 module を含む全体 Audit は次の関門で更新する。
旧点モデル時点の full Audit の成功を、今回の三 module 全体の Audit として報告しない。

## 5. 続ける義務

1. 宣言時の per-argument variance を参照する比較の独立 demand exactness と実有限 inspection。Covariant は正方向、Contravariant は逆方向、Invariant だけ区間／双方向、Unused は既定の無使用位置の扱い。
2. 実 finite declaration の recursive parameter/位置解析から、その表を実計算する検証 theorem。任意の表を受け取る局所 theorem はこの代用ではない。
3. general ground checker の declaration-aware 化。旧 Casts.Compatibility.nominalInvariant は共変 box に強すぎる。旧 checker の保存は all-Invariant collapsed case に限る。
4. recursive nominal endpoints と existing CommonBoundRef*/row families の接続、全 source-generated constraints / 全元 Models / 全自由 parameters。
5. 全 fields/sites・構築位置の不変 deferred pure casts・後の利用／EOF・一度評価と元順序、有限共変 wrapper の実行橋、B1 nil/cons/list/nominal-data と Float。
6. 原因 key による fresh constraint 再 collect、global all-occurrence sandwich と captured/level 保護の保存。

旧未完成 point TypingReflection は未 import のまま進めていない。一般 nominal の invariance、一般 cast、construction、B1 が証明済みとは主張しない。
