# dots cycle 95 — 実状態からの Form 再生成と有限仕事領域

## 結果と部分目標

**実 ordinary atoms の int 等式を使って構造を持つ interval Form を再生成し、その全診断 frontier が状態に依存しない計算済み有限領域へ入る橋を閉じた。** 元の Form の全 constructor（var/int/pair/join/tick）、任意数の上下端点・引数、任意の slot map と共有を扱う。固定具体例だけの定理ではない。

新規 `CommonRoleStateMaterializedFrontier` は225行、13公開定理。int の明示的な両方向の ordinary 証拠を実 detector が見つける断片で部分目標は閉じた。一般の interval 意味論的含意を決定したわけではなく、**B4 主定理には主要橋が5本残る**。

今回の実計算は ordinary atoms から original goal を materialize し直し、候補を再 inspect して子 tree を再生成する。前回の固定 tree に atoms を加えるだけの `advance_exact` より先へ進んだ。状態列を回す飽和 driver、source 生成の完全性、安定後分類までは進めていない。

## 定理の量化・前提と日本語の主張

以下は全て `Yulang.CommonRoleStateMaterializedFrontier`。

1. `materialize_meaning`: 任意 n、atoms、slots、Form と、その atoms を満たす任意 assignment に対し、materialize 後の Form.eval は元の Form.eval と Common.Equivalent。モデルを計算に渡さず、全モデルについて証明した。
2. `detected_int_persists`: 任意 before/after atoms、before の全 atom が after に属するという前提、after を満たす任意 assignment、任意 slot に対し、before で実 detect が int なら after でも int。順序や重複の一致は不要。
3. `rematerialize_fusion`: 同じ inclusion と later-model 前提、同じ任意 slots、任意 Form で、before で materialize した Form を after で再 materialize する結果は、元の Form を after で materialize する結果と構文として等しい。
4. `materialize_present`: 任意状態・slots・Form の materialize は、その元 Form だけから計算した variants に入る。整合性前提はない。
5. `arguments_present`: 任意個数の元上下端点対について同じ所属を証明。空引数も扱う。
6. `goal_present`: 任意状態・slots・元 goal の再生成結果は、元 goal だけから計算した goalVariants に入る。
7. `domain_exact`: 任意 Checked registry、元 goal、target で、有限 domain への所属と、一つの計算済み variant から独立 Reach で target に達することが iff。
8. `workDomain_exact`: 任意 registry、元 goal、bound で、public workDomain がその bound を返すことと、Checked かつその bound が計算済み domain であることが iff。checker を caller の証明に置き換えない。
9. `regenerated_reach_present`: 任意 Checked registry、任意状態・slots・元 goal と、その materialize 結果からの任意 Reach target は同じ有限 domain に入る。状態の単調性やモデルの存在を仮定しない。
10. `run_models_exact`: 任意 registry/slots/Sources/atoms/old/original/assignment で、実 run の graph がその assignment を表すことと、Checked、元 atoms、単一 source valuation による old と materialized goal の独立 Derives が iff。
11. `run_work_present`: 任意 public run の成功出力と、その診断 tree の任意 node に対し、Checked と計算済み domain 所属が得られる。complete plan/graph/model の存在は仮定しない。
12. `run_computed_bound`: 同じ任意成功実行・任意 tree node に対し、public workDomain が実際に返す bound が存在し、その node が含まれる。caller の fuel、check proof、仕事列は不要。
13. `domain_child_closed`: 任意 Checked registry、任意元 goal と domain 中の goal、その実 Edge の child は同じ domain に含まれる。別の materialization 由来の node にも使える。

## 確かめた境界と未達

- Form の int だけを materialize する。str/bool/unit、片方向だけの証拠、証拠なしは元の source variable を保つ。unique impl の存在からは絞らない。
- detector は最初の scalar candidate を選ぶ。矛盾した状態で paired str を paired int より先に置くと元変数のまま、逆順なら int になる。両順序を回帰で確認した。全モデル保存はこの矛盾状態ではモデルがなく、有限 domain 所属はそれでも成立する。
- later-model 前提のない fusion は成立しない。before が paired int、after が paired str ++ paired int の負例を実行して前提の必要性を確認した。
- `Sources : Goal → Declaration → Nat → Nat` は元からの caller 入力で、Goal が変わるとキーと旧需要との alias が変わり得る。今回の Derives は materialized goal に対するもの。元 goal の Derives と等しい、または状態間の全 graph モデルが単調に減るとは証明していない。
- Form.eval の意味保存と、syntax-sensitive な候補照合の不変性は別。後者を主張していない。fusion も異なる状態の tree 同一性を主張しない。
- domain は診断 tree の `List Goal`。ordinary graph 内部頂点の一様上限ではない。変数の各 occurrence を独立に列挙するので、共有と両立しない組合せも含む有限 overapproximation。最小領域でも効率の証明でもない。
- source template の集合は固定。任意の新しい Form constructor や一般構造を状態から発見する仕組みではない。一般 generated_work_closed、Paterson/K2 driver、四分類、dictionary 観察同値は未達。
- 新意味論判断0件。新質問0件。変化する invocation キーの問題は既存 `notes/questions/2026-11-10-cycle70-invocation-sharing-boundary.md` と同じ未決境界として残し、台帳 AF に明記した。

## 検証

最終 production source に対して以下を実行し、全て exit 0。

```text
cd lean
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build Yulang.CommonRoleStateMaterializedFrontier --wfail
✔ [311/311] Built Yulang.CommonRoleStateMaterializedFrontier (1.1s)
Build completed successfully (311 jobs).
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang95/boundary-check.lean
exit 0, no diagnostics
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang95/axioms.lean
'Yulang.CommonRoleStateMaterializedFrontier.materialize_meaning' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStateMaterializedFrontier.detected_int_persists' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStateMaterializedFrontier.rematerialize_fusion' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStateMaterializedFrontier.materialize_present' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStateMaterializedFrontier.arguments_present' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStateMaterializedFrontier.goal_present' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStateMaterializedFrontier.domain_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStateMaterializedFrontier.workDomain_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStateMaterializedFrontier.regenerated_reach_present' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStateMaterializedFrontier.run_models_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleStateMaterializedFrontier.run_work_present' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStateMaterializedFrontier.run_computed_bound' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleStateMaterializedFrontier.domain_child_closed' depends on axioms: [propext, Quot.sound]
```

26個の実行可能な #guard と3個の kernel example。nested pair/join/tick、同名の反復、別名の slot alias、片方向証拠、別 slot、str/bool/unit、下上端点の全組合せ、空引数、複数引数、矛盾証拠の両順序、row 保存、重複宣言、global checker 拒否、public bound を検査した。

親 `tick 'a` が Left と int head の Right を要求する例で、最初は Right が unsupported の0 plan、実 paired int atoms の追加後は全 child が残ったまま1 graph に変わる。前後の全 tree node は同じ計算済み domain に含まれる。kernel example は一般 nested Form 意味保存、append 後の fusion、矛盾を含む元 atoms が全 graph モデルを排除することを確認した。実行チェックを kernel 定理とは呼ばない。期待値の変更なし。

```text
python3 tools/boundary-input-inventory.py --check
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=262; Main=93; Audit=262; ledger mentioned=135. Mention counts are not audit completion counts.
bash tools/verify-lean.sh . origin/integration/m1-final --no-build
verify-lean: . @ 33d3849e7 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

`git diff --check` も exit 0。全ローカル build・全 Audit・全 AxiomGate は指示どおり未実行。verify は diff-only の PASS。今回の13定理の公理は propext / Classical.choice / Quot.sound の範囲。

独立 read-only review で定理レベルの soundness 問題なし。reviewer が指摘した detector 順序、Sources の変化、domain の対象、later consistency の必要性を文書と回帰に反映した。reviewer は build を実行していない。追加した workDomain の public wrapper は自己 review と focused build で確認した。

初回から production Lean は focused build が通った。回帰 script 内の proposition 定義に linter warning が1件あり、同じ命題を theorem 宣言へ変更して消した。inventory script に存在しない --write を一度渡したが、実際の no-argument 生成方法へ直して --check が通った。GitHub 書き込みの拒否・不確定再試行なし。

## 公開と復旧

source commit: `c0d67f39bba0537e6c710d12eb142e3d47eda7d0`。
source tree: `1348a5e587fd54150003321eda8595f93fc08d54`。
local source checkpoint: `33d3849e78502f6fcbcf698a3f3de5e93dbb59e0`。

9変更 path を個別 blob として公開し、全返却 SHA が local hash-object と一致。
live work tree を base に SHA-only tree を作成し、全 tree SHA が local write-tree と一致。
非 force・expected-head 更新後に ref を再読し、非 truncated recursive tree 2343 entries と9変更 blob を照合した。他 path は保持した。production Lean は source 公開後に変更していない。

startup heartbeat `23c60215`、source 公開 `c0d67f39`、10分 heartbeat `ff828993`。
最後にこの報告と completed heartbeat を同じ tree で公開して照合する。報告を含む今回の変更は10 path。

開始は2026-11-10T19:27:24Z、期限19:52:19Z。live integration/work は開始時ともに af7ad0e0。
standing orders/inbox を取得して再読し ACTIVE と上限なしを確認した。前 cycle94 は completed と報告あり、前 writer/Lean process もなし。crash recovery ではなく通常再開。integration を通常 merge し、一つの既存 workspace/cache を再利用した。

開始/終了時の空きはともに48G（63G中13G使用）。新 clone・cache コピーなし。使用量の枠は不明。ログは `../cache/yulang95`。この報告準備時刻は 2026-11-10T19:39:26.177289+00:00、経過 12.0 分。時間を埋めるための補題は追加していない。

## B4に残る5橋と次の候補

1. `source_boundary_adequate`: parser/declからscope、annotation、source occurrence/invocationを実導出。
2. `generated_work_closed`: 今回の固定 template・明示 int evidence から、一般の state 依存 interval materialization と生成仕事へ拡張。
3. `saturate_terminates_and_closes`: 兄弟更新と再生成を安定まで回す Paterson/K2 driver。
4. `saturated_frontier_exact`: 実飽和に接続した安定後の独立4分類。
5. `resolve_dictionary_order_sound`: 正準 source obligation 順の dictionary 観察同値。

次の候補は (a) 既存 invocation-sharing 境界を解決して再生成間の source 需要を比較する橋、(b) 実 ordinary 生成と今回の有限 domain を結ぶ bounded driver、(c) int 証拠以外の interval materialization に対する有限 template/provenance 導出。未解決の source identity を無条件の入力へ隠して飽和完成とはしない。

## 再実行用の回帰 script

```lean
import Yulang.CommonRoleStateMaterializedFrontier
open Yulang
open CommonRoleCaptureNormalization (Form)
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal)
open CommonRoleGuardedIntervalPlans (Sources Plan)
open CommonRoleStateMaterializedFrontier
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (Atom All)
namespace Cycle95BoundaryCheck
set_option maxRecDepth 8192
set_option synthInstance.maxSize 1024
set_option maxHeartbeats 4000000

def slots : Nat → Fin 2 := fun n => ⟨n % 2, Nat.mod_lt n (by decide)⟩
def sources : Sources := fun _ _ binder => binder
def equality (i : Fin 2) (base : Inference.Base) := CommonRoleCandidateStateFrontier.equality i base

def parent : Declaration := ⟨0,0,[.tick (.var 0)],[(1,[.var 0]),(2,[.var 0])]⟩
def left : Declaration := ⟨1,1,[.var 0],[]⟩
def right : Declaration := ⟨2,2,[.int],[]⟩
def goal : Goal := ⟨0,[(.tick (.var 0),.tick (.var 0))]⟩
def summary (atoms : List (Atom (Fin 2))) :=
  (run [parent,left,right] slots sources atoms [] goal).map fun out =>
    ((CommonRoleFrontierReachability.goals out.1).map (·.role),
      (CommonRoleFrontierReachability.boundaries out.1).map (fun e => (e.1.role,e.2.key)),
      out.2.length)

-- Unknown receiver keeps the source name and every unfinished child.
#guard materialize [] slots (.var 0) = .var 0
#guard summary [] = some ([0,1,2],[(2,2)],0)
-- Actual paired ordinary evidence causes a previously unsupported rigid child to resolve.
#guard materialize (equality 0 .int) slots (.var 0) = .int
#guard summary (equality 0 .int) = some ([0,1,2],[],1)
-- Single-sided evidence is insufficient, and unrelated slots do not materialize.
#guard materialize [.tyLe (.var 0) (.base .int)] slots (.var 0) = .var 0
#guard materialize (equality 1 .int) slots (.var 0) = .var 0
#guard materialize (equality 0 .str) slots (.var 0) = .var 0
#guard materialize (equality 0 .bool) slots (.var 0) = .var 0
#guard materialize (equality 0 .unit) slots (.var 0) = .var 0
-- Name 2 aliases slot 0 only because that explicit caller map says so.
#guard materialize (equality 0 .int) slots (.pair (.var 0) (.tick (.join (.var 2) (.var 1)))) =
  .pair .int (.tick (.join .int (.var 1)))
-- No silent normalization of a join is performed by materialization.
#guard materialize (equality 0 .int) slots (.join (.var 0) (.var 0)) = .join .int .int
-- All lower/upper combinations are retained, even source-inconsistent ones.
#guard (goalVariants goal).length = 4
#guard (goalVariants goal).contains ⟨0,[(.tick (.var 0),.tick .int)]⟩
#guard (goalVariants ⟨0,[]⟩).length = 1
#guard (goalVariants ⟨0,[(.var 0,.var 0),(.var 1,.var 1)]⟩).length = 16
-- Inconsistent states retain the detector's first-evidence behavior.
#guard materialize (equality 0 .str ++ equality 0 .int) slots (.var 0) = .var 0
#guard materialize (equality 0 .int ++ equality 0 .str) slots (.var 0) = .int
-- Graph existence is structural, not model existence or solver success.
#guard summary (equality 0 .int ++ equality 0 .str) = some ([0,1,2],[],1)
-- Old row constraints remain in the actual ordinary graph, without reindexing rows.
#guard (run [parent,left,right] slots sources
  (equality 0 .int ++ [.rowLe (.var 0) (.var 1)]) [] goal).map
  (fun out => out.2.map (fun g => g.rows.length)) = some [1]
-- The computed state-independent finite domain covers both actual traversals.
theorem checked : CommonRoleIntervalWorkClosure.Checked [parent,left,right] := by
  decide +kernel
#guard (CommonRoleFrontierReachability.goals
  (CommonRoleGuardedIntervalFrontier.build [parent,left,right] checked slots sources goal)).all
  (fun g => (domain [parent,left,right] checked goal).contains g)
#guard (CommonRoleFrontierReachability.goals
  (CommonRoleGuardedIntervalFrontier.build [parent,left,right] checked slots sources
    (materializeGoal (equality 0 .int) slots goal))).all
  (fun g => (domain [parent,left,right] checked goal).contains g)
-- An invalid declaration is still rejected globally.
def growing : Declaration := ⟨9,9,[.var 0],[(9,[.tick (.var 0)])]⟩
#guard (run [parent,left,right,growing] slots sources (equality 0 .int) [] goal).isNone

-- Duplicate declarations retain duplicate complete plans, and bound calculation is public.
#guard (run [parent,parent,left,right] slots sources (equality 0 .int) [] goal).map
  (fun out => out.2.length) = some 2
#guard (workDomain [parent,left,right] goal).isSome
#guard (workDomain [parent,left,right,growing] goal).isNone
-- Without later consistency, fusion really can fail despite atom inclusion.
#guard materialize (equality 0 .str ++ equality 0 .int) slots
  (materialize (equality 0 .int) slots (.var 0)) !=
    materialize (equality 0 .str ++ equality 0 .int) slots (.var 0)

-- Kernel-checked general all-model preservation, including sharing and deep forms.
example (atoms : List (Atom (Fin 2))) (assignment : Fin 2 → Comp Common.model)
    (models : All Common.model assignment atoms) (a b : Form) :
    Common.Equivalent
      ((materialize atoms slots (.pair (.join a b) (.tick a))).eval
        (fun k => (assignment (slots k)).1))
      ((Form.pair (.join a b) (.tick a)).eval (fun k => (assignment (slots k)).1)) :=
  materialize_meaning atoms slots assignment models _

-- Consistent extension can safely rematerialize from a previously materialized template.
example (before fresh : List (Atom (Fin 2))) (assignment : Fin 2 → Comp Common.model)
    (models : All Common.model assignment (before ++ fresh)) (form : Form) :
    materialize (before ++ fresh) slots (materialize before slots form) =
      materialize (before ++ fresh) slots form :=
  rematerialize_fusion before (before ++ fresh)
    (fun _ member => List.mem_append_left fresh member) slots assignment models form

-- Both contradictory pairs eliminate every represented model, despite a structural graph.
example (old : Plan (Fin 2)) (output)
    (returned : run [parent,left,right] slots sources
      (equality 0 .int ++ equality 0 .str) old goal = some output)
    (assignment : Fin 2 → Comp Common.model) :
    ¬ CommonRoleFrontierGraphs.Represents output.2 assignment := by
  intro represented
  have models := ((run_models_exact [parent,left,right] slots sources
    (equality 0 .int ++ equality 0 .str) old goal assignment).mp ⟨output,returned,represented⟩).2.1
  have hi : CommonRoleOrdinaryKnownness.Evidence (equality 0 .int ++ equality 0 .str) 0 .int := by
    constructor <;> simp [equality,CommonRoleCandidateStateFrontier.equality]
  have hs : CommonRoleOrdinaryKnownness.Evidence (equality 0 .int ++ equality 0 .str) 0 .str := by
    constructor <;> simp [equality,CommonRoleCandidateStateFrontier.equality]
  have impossible := CommonRoleOrdinaryKnownness.evidence_unique _ 0 assignment models .int .str hi hs
  cases impossible
end Cycle95BoundaryCheck
```

## Exact-source CI と最終公開準備（2026-11-10T19:39:59.283243+00:00）

source `c0d67f39bba0537e6c710d12eb142e3d47eda7d0` に対する Core CI と
Lean inference kernel は両方 completed/success。Lean proof job の全 build、
全宣言 Audit、source/value/regular/semantic record examples の各 step も success。
remote CI の結果であり、ローカル全体検証とは区別する。production Lean の後続変更なし。

- Core: https://github.com/momota1029/yulang/actions/runs/42887040999
- Lean: https://github.com/momota1029/yulang/actions/runs/42887040986

経過 12.6 分で部分目標・検証・source 公開・CI確認が完了。この報告と
completed heartbeat を公開し、最終 ref/tree/変更blob を照合して終了する。
