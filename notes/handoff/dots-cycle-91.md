# dots cycle 91 — 候補を分けた再帰的区間planと共有sourceモデル

## 結果と部分目標

**固定されたForm区間の有限文法で、候補の選択肢とwhereの子の連言を区別した再帰的plan生成を計算し、実ordinary制約の全モデルと独立な宣言導出のiffを閉じた。**

新規 `CommonRoleGuardedIntervalPlans` は251行、8公開定理。部分目標はcycle90の第二候補 `guarded_interval_work_models_exact` に相当する。構造的な潜在仕事だけでなく、親の一つの候補に属する全where子が再帰的に導出されるplanを列挙し、元のordinary制約生成へ接続した。異なる宣言候補の制約は連言しない。全B4の主定理は未達で、主要橋は5本のまま。

当初調べた一般Formのstate materializationは、既存int-only/unary Stateとはcarrierが異なり、翻訳を得ていない。そこを同一視せず、前回明記されたもう一つの部分目標へ進んだ。任意の将来stateを今回の有限領域が含むとは主張しない。

## 正確な範囲と境界

- `products` は子ごとのplan集合のCartesian積を取り、各planのdemandsを順番に連結する。子0個なら空continuationが一つ、どれかの子にplanが無ければ親のその候補もplan0個。順序・重複は保持する。
- `candidates` は実inspectが成功した宣言と独立Acceptsの証明を保持する。`compile` は宣言間をflatMapし、同じ宣言の全子だけをproductsで連言する。複数planを一つの制約集合に連結しない。
- `Derives` はregistry所属、独立Accepts、元のheadのHeadFits、全where子のDerivesから成る独立な有限導出。compileの出力所属で定義していない。
- sourceの値 `values` は、子ごとに別々に選ばない。一つの値割当を、親・全子・old demandsに通して使う。`ordinary` はplan全体とoldをまとめて実 `SourceIntervalBatches.generate` に渡すため、兄弟をまたぐ共有sourceの比較も失わない。
- `Sources := Goal → Declaration → Nat → Nat` はcaller入力。**同じgoal/declaration/binderの組には必ず同じsource keyが返り、同じ組の別occurrenceを独立に命名できない。** occurrenceを識別する一般allocatorやfresh invocationの方針は証明・決定していない。この制限はdocstring、設計ノート、台帳ABにも明記した。
- ambient endpointの `slots`、元のdemands、registryとgoalのsourceからの生成もcaller境界。有限visit列、fuel、子solverの成功、modelの存在は入力ではない。
- `compile` と補助定理にはChecked前提があるが、公開 `run` は実checkerを計算し、`run_models_exact` はCheckedを結果側に置く。無関係な宣言でもchecker不合格ならrunはnone。
- `run` の第二成分はcycle90の全潜在仕事領域にあるoutside scan。正確には**accepted edgeで到達するgoal**でのunsupported inspectionを返す。unsupported captureだけから生成できる仮想の子は含まない。
- planが空でも言語のrejectedとは言わない。outsideが残っていても別のaccepted branchのplanが返る。複数planは曖昧性の最終判定ではなく、存在モデルの選択肢。planは辞書のidentityを保持するデータではない。
- これは固定endpoint syntaxでの有限proof-plan。ordinary stateの絞り込み後の再materialization、K2、未完成diagnostic treeの最終4分類、辞書同値、全言語の主型性は証明していない。

## 追加定理とM1のどの側に効くか

全て `Yulang.CommonRoleGuardedIntervalPlans`。以下の健全性・完全性はこの明示した断片の対応を指す。

1. `shared_append`: 任意assignment/values/二demand列で、連結列を同じvaluesが満たすことと両列を満たすことがiff。**補助**。
2. `products_exact`: 任意assignment/固定values/有限なplan集合列で、productsに同じvaluesを満たすplanが存在することと、各子のplan集合に同じvaluesを満たすplanが存在することがiff。**健全性・完全性**。子ごとの独立な存在値ではない。
3. `candidates_complete`: 任意registry/goal/declaration/bindingsで、registry所属と独立Acceptsがあれば、実candidate列にその対が存在する。**完全性**。
4. `local_models_exact`: 任意slots/source map/assignment/values/declaration/goal/bindingsで、Acceptsの下、実captured demandsのSharedFitsと元headのHeadFitsがiff。**健全性・完全性**。成功captureはこの局所定理の明示前提。
5. `compile_exact`: 任意Checked registry/slots/source map/assignment/values/goalで、実compileにSharedFitsを満たすplanが存在することと独立Derivesがiff。**健全性・完全性**。全子の導出は結果側であり仮定ではない。
6. `ordinary_exact`: 任意Checked registry/slots/source map/old/goal/assignmentで、実ordinary出力にAllを満たすatom列が存在することと、一つのvaluesがoldと再帰的Derivesを満たすことがiff。**健全性・完全性**。実生成された比較に達する。
7. `run_models_exact`: 任意registry/slots/source map/old/goal/assignmentで、runが返す出力のordinary選択肢にAllモデルがあることと、Checkedかつ一つのvaluesがoldとDerivesを満たすことがiff。callerのChecked前提なし。**外側の健全性・完全性**。
8. `run_boundaries_exact`: 任意runの成功出力と任意goal/declarationで、第二成分への所属と、独立Reach＋registry所属＋実inspectのnoneがiff。**境界診断の健全性・完全性**。成功出力は局所payload対応の前提。

新しい主型性・全B4・dictionary observational equivalenceの定理はない。既存Lean定義・定理は変更していない。Yulang/Audit import、8定理のAudit登録、README、設計INDEX、台帳AB、coverage表を追加更新した。

## 検証

最終production Leanに対し以下は全てexit 0。

```text
cd lean
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake build Yulang.CommonRoleGuardedIntervalPlans --wfail
✔ [307/307] Built Yulang.CommonRoleGuardedIntervalPlans (1.4s)
Build completed successfully (307 jobs).
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang91/boundary-check.lean
exit 0 (26 examples and one scratch conflict-refutation helper; no diagnostic output)
ELAN_HOME=../../elan timeout 180 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang91/axioms.lean
'Yulang.CommonRoleGuardedIntervalPlans.shared_append' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGuardedIntervalPlans.products_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGuardedIntervalPlans.candidates_complete' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGuardedIntervalPlans.local_models_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGuardedIntervalPlans.compile_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleGuardedIntervalPlans.ordinary_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleGuardedIntervalPlans.run_models_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleGuardedIntervalPlans.run_boundaries_exact' depends on axioms: [propext, Quot.sound]
```

26 examples: 候補OR、全兄弟AND、欠けた子、候補と子の重複、registry順、rigid mismatchとoutsideの区別、accepted branchとunsupported branchの共存、無関係な不正宣言、深さ8の再帰、元endpointの別名、共有sourceの兄弟間衝突と別sourceの場合、外側run theorem。共有source衝突は単なるcheckフラグだけでなく、actual emitted atom列にどんなassignmentでもモデルがないことを証明した。一方、conflict=falseはsolverの完全性やモデル存在とは扱わない。深いplanの個数検査も、そのsource mapでの整合性を主張しない。

```text
python3 tools/boundary-input-inventory.py --check
CommonRole import scope=258; Main=93; Audit=258; ledger mentioned=131. Mention counts are not audit completion counts.
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=258; Main=93; Audit=258; ledger mentioned=131. Mention counts are not audit completion counts.
bash tools/verify-lean.sh . origin/integration/m1-final --no-build
verify-lean: yulang @ 445090802 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
```

`git diff --check`もexit 0。上はローカルのdiff-only gateであり、全体verifyのPASSではない。全体lake build、全Audit、AxiomGate、全体verifyは指示に従いローカルでは実行していない。8定理の依存公理はpropext/Classical.choice/Quot.soundだけ。

## 公開とexact-source CI

source commit: `138417b741ed17a1ade4452f7ff6ce597d18db3b`。

- Core CI: completed / success — https://github.com/momota1029/yulang/actions/runs/42867517207
- Lean inference kernel: completed / success — https://github.com/momota1029/yulang/actions/runs/42867516926

このexact-source SHAを指定して確認した。Lean proof jobのLean action、全宣言Audit、source/value/regular/semantic-record examplesが全てsuccess。ローカル実行とは記載しない。source公開後にproduction Leanを変更していない。報告・heartbeatを含む最終commitのCIとは区別する。

公開tree `7931923497f914a7aa6a666fc7ef2b428ffdae4e` を取得: 2,331 entries、非truncated、9変更pathのblob SHA全一致、全体treeがlocal checkpoint `445090802` と同一。明示tracking ref付きfetch後もlocal/remoteの全tree差分は空だった。

## 独立レビュー、Yulang2、質問

読み取り専用reviewerは定理レベルの欠陥を見つけなかった。独立Derives、OR/AND、全体で共有するvalues、実ordinary generate、checker由来の両endpoint減少を確認した。最初にsource tuple keyのalias制限とoutsideの公開方法を指摘したため、docstring/設計/台帳を明確化し、公開runの第二成分とboundary iffを追加した。追加後と全26例のうち最初の24例を再reviewし、重大な過大主張なしとの結果だった。reviewerはbuildを実行していない。最後の追加2例（モデル不在の証明と候補ごとのatom列の分離）は親がtrust=0で実行した。

新定義前にspec 6.3とwork/dots-auditの `notes/audit/x-oracle.md` C3-PARENT/C3-PARENT-NEGを読んだ。兄弟の連言・順序と必須child欠如の過去観測を参照した。今回の一般guarded planをYulang2で新規実行してはいない。過去oracleを今回の完全性や全区間飽和の証拠にはしない。

新規質問ノート0件。source allocatorの未回答事項は既存の台帳・質問の境界を保持した。今回のSources型の制限を一般の言語意味論として採用していない。I-13台帳ABを追加したが、全moduleの意味監査の完了は主張しない。

## 残る5主要橋と次の候補

B4主定理への主要橋は5本のまま。
1. `source_boundary_adequate`: parser/declからscope、grouped clause、associated annotation、occurrence-sensitive source keyを実際に導く一般橋。
2. `generated_work_closed`: 固定区間の有限workと今回のguarded planモデルは閉じたが、state-dependent materialization後の一般childを有限source-template領域へ入れる橋が未完。
3. `saturate_terminates_and_closes`: 兄弟の状態更新・再生成を安定まで回すPaterson/K2 driver。今回の静的plan再帰はこのdriverではない。
4. `saturated_frontier_exact`: 未完成diagnostic treeと全言語の4分類。今回のplan存在やoutside一覧では代替しない。
5. `resolve_dictionary_order_sound`: 正準source obligation順のdictionary観察同値。demands列だけでは辞書のidentityを表さない。

次の候補:
- `interval_materialized_child_all_states`: Form intervalと実ordinary stateのmaterialization carrierをまず定義して接続し、元source ownerを保持するchild templateを得る。任意future-stateの構造を無制限に許すだけの有限性主張にしない。
- `occurrence_guarded_plan_models_exact`: 現在のGoal/declarationキーの限界を越える、実source occurrence/invocationからのkey導出。意味論の未回答点を勝手にfreshness規則へ置換しない。
- `guarded_plan_frontier`: chosen declaration/child結果を残す診断treeへplanを接続し、候補が複数という理由だけで兄弟の途中結果を最終曖昧にしない。

## 復旧、時刻、資源

- 開始2026-11-10T17:28:36Z。integration/work liveはfaa10631。standing orders/inboxをliveから再読、ACTIVEと上限なしを確認。cycle90のcompleted heartbeatとreportあり。前writer/buildは見つからず、新cycleの復旧処理は不要だった。
- 同じworkspaceとLean cacheを継続し、integrationをmergeしてから変更。clone/cacheを増やしていない。空きは開始・source照合後とも48G/63G（使用13G）。使用量の枠は不明。
- 開始heartbeat0100cefc、約10分heartbeat3d90cb9d、source138417b7をwork/dots-mainだけへ公開。個別blobを完全内容で作成し、各SHA検証後にSHA-only treeをlive treeから構成した。非forceとexpected-headで更新した。拒否・不確定なwriteなし。
- 初期proofは予約語、dependent match、再帰proofのgoal等式、公開result tupleの明示が必要でelaboration失敗した。修正後の最終focused build、trust=0全26例、公理監査は全て通った。既存の期待値や定理を弱めていない。
- 新規boundary検査のoutside数は初期草稿でrootだけを数えていた。実定義は左/右childにもunsupported宣言をinspectするため、独立Reachの3箇所を検査する期待値に直した。言語挙動の変更ではない。
- source/doc8path、heartbeat、最終reportの計10path。sourceは既に全tree照合済み。最終report/heartbeatも公開後に照合する。未公開production Leanはない。
- ログは `../cache/yulang91`。実行期限は2026-11-10T17:52:19Z。

報告作成: 2026-11-10T17:44:46Z。経過16.2分。部分目標の後は検証・独立review・CI・報告を行い、時間を埋める補題は追加していない。

## 再実行用boundary検査全文

```lean
import Yulang.CommonRoleGuardedIntervalPlans
import Yulang.CommonRoleRecursiveConflicts
open Yulang
open CommonRoleCaptureNormalization (Form)
open CommonRoleStablePaterson (Declaration)
open CommonRoleIntervalPaterson (Goal)
open CommonRoleGuardedIntervalPlans
namespace Cycle91BoundaryCheck
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def mk (role : Nat) (lo hi : Form) : Goal := ⟨role, [(lo,hi)]⟩
def parent : Declaration := ⟨0, 0, [.tick (.var 0)], [(1,[.var 0]),(2,[.var 0])]⟩
def left : Declaration := ⟨1, 1, [.var 0], []⟩
def right : Declaration := ⟨2, 2, [.var 0], []⟩
def sources : Sources := fun _ _ binder => binder
def counts (ds : List Declaration) (g : Goal) :=
  (run ds (id : Nat → Nat) sources [] g).map fun output =>
    (output.1.map List.length, output.2.length)
def root := mk 0 (.tick .int) (.tick .int)
example : counts [parent,left,right] root = some ([9],0) := by decide +kernel
example : counts [parent,right,left] root = some ([9],0) := by decide +kernel
example : counts [parent,left] root = some ([],0) := by decide +kernel
example : counts [parent,right] root = some ([],0) := by decide +kernel
example : counts [parent,left,left,right] root = some ([9,9],0) := by decide +kernel
example : counts [parent,left,right,right] root = some ([9,9],0) := by decide +kernel
example : counts [parent,parent,left,right] root = some ([9,9],0) := by decide +kernel
example : counts [] root = some ([],0) := by decide +kernel
example : counts [left] (mk 1 .int .int) = some ([1],0) := by decide +kernel
example : counts [left] (mk 99 .int .int) = some ([],0) := by decide +kernel
example : counts [parent,left,right] (mk 0 .int .int) = some ([],0) := by decide +kernel
example : counts [parent,left,right] (mk 0 (.var 7) (.var 8)) = some ([],1) := by decide +kernel

def joined : Declaration := ⟨0,3,[.join (.var 0) (.var 1)],[]⟩
example : counts [parent,left,right,joined] root = some ([9],3) := by decide +kernel
example : counts [joined] root = some ([],1) := by decide +kernel

def growing : Declaration := ⟨0,4,[.var 0],[(0,[.tick (.var 0)])]⟩
example : counts [growing] root = none := by decide +kernel
example : counts [parent,left,right,growing] root = none := by decide +kernel

def recursive : Declaration := ⟨0,5,[.tick (.var 0)],[(0,[.var 0])]⟩
def terminal : Declaration := ⟨0,6,[.int],[]⟩
def tower : Nat → Form
  | 0 => .int
  | n+1 => .tick (tower n)
example : counts [recursive,terminal] (mk 0 (tower 8) (tower 8)) = some ([64],0) := by decide +kernel
example : counts [recursive] (mk 0 (tower 8) (tower 8)) = some ([],0) := by decide +kernel

def duplicate : Declaration := ⟨0,7,[.tick (.var 0)],[(1,[.var 0]),(1,[.var 0])]⟩
example : counts [duplicate,left] root = some ([9],0) := by decide +kernel
example : counts [duplicate,left,left] root = some ([9,9,9,9],0) := by decide +kernel
example : counts [parent,left,right] (mk 0 (.tick (.var 7)) (.tick (.var 8))) = some ([9],0) := by decide +kernel

-- Actual generated comparisons expose a shared-source conflict across children.
def differentParent : Declaration :=
  ⟨0,8,[.tick (.pair (.var 0) (.var 1))],[(1,[.var 0]),(2,[.var 1])]⟩
def differentRoot := mk 0 (.tick (.pair .int (.tick .int))) (.tick (.pair .int (.tick .int)))
def aliasSources : Sources := fun _ d binder => if d.key = 8 then binder else 2
def separateSources : Sources := fun _ d binder => if d.key = 8 then binder else d.key + 2
def conflict : PresenceNormalForm.Atom Nat → Bool
  | .tyLe l r => CommonRoleRecursiveConflicts.check l r
  | .rowLe _ _ => false
def conflicts (src : Sources) :=
  (run [differentParent,left,right] (id : Nat → Nat) src [] differentRoot).map fun o =>
    o.1.map (fun atoms => atoms.any conflict)
example : conflicts aliasSources = some [true] := by decide +kernel
example : conflicts separateSources = some [false] := by decide +kernel
example (registry : List Declaration) (slots : Nat → α) (src : Sources)
    (old : Plan α) (goal : Goal) (assignment : α → Core.PresenceGeneration.Comp Common.model) :
    (∃ out, run registry slots src old goal = some out ∧
      ∃ atoms ∈ out.1, PresenceNormalForm.All Common.model assignment atoms) ↔
      CommonRoleIntervalWorkClosure.Checked registry ∧ ∃ values,
        CommonRoleCaptureBatchModels.SharedFits assignment values old ∧
          Derives registry slots src assignment values goal :=
  run_models_exact registry slots src old goal assignment
theorem conflict_refutes (atoms : List (PresenceNormalForm.Atom Nat))
    (found : atoms.any conflict = true)
    (assignment : Nat → Core.PresenceGeneration.Comp Common.model) :
    ¬ PresenceNormalForm.All Common.model assignment atoms := by
  obtain ⟨atom, member, hit⟩ := List.any_eq_true.mp found
  intro models
  have holds := models atom member
  cases atom with
  | tyLe l r => exact CommonRoleRecursiveConflicts.checked_no_subtype l r hit assignment holds
  | rowLe l r => cases hit

-- This is semantic inconsistency, not just a syntactic conflict flag.
example (output) (returned : run [differentParent,left,right] (id : Nat → Nat)
    aliasSources [] differentRoot = some output)
    (atoms : List (PresenceNormalForm.Atom Nat)) (member : atoms ∈ output.1)
    (assignment : Nat → Core.PresenceGeneration.Comp Common.model) :
    ¬ PresenceNormalForm.All Common.model assignment atoms := by
  have flags : output.1.map (fun atoms => atoms.any conflict) = [true] := by
    have computed : conflicts aliasSources = some [true] := by decide +kernel
    simpa [conflicts, returned] using computed
  have hit : atoms.any conflict ∈ output.1.map (fun atoms => atoms.any conflict) :=
    List.mem_map.mpr ⟨atoms,member,rfl⟩
  rw [flags] at hit
  exact conflict_refutes atoms (List.mem_singleton.mp hit) assignment

-- Every declaration here is viable in isolation; alternatives are kept separate.
def pairHead : Declaration := ⟨0,9,[.pair (.var 0) (.var 1)],[]⟩
def sharedPair : Goal := mk 0 (.pair .int (.tick .int)) (.pair .int (.tick .int))
def keyed : Sources := fun _ d binder => if d.key = 9 then binder else binder + 2
example : (run [pairHead,pairHead] (id : Nat → Nat) keyed [] sharedPair).map
    (fun o => o.1.map List.length) = some [2,2] := by decide +kernel
end Cycle91BoundaryCheck
```
