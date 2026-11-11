# dots cycle 106 — source から任意深さの失敗保持診断木へ

## 所要時間・部分目標

開始 2026-11-11T00:58:45Z。報告準備 2026-11-11T01:24:52.235610+00:00、約26.1分。
**部分目標は25分以内に閉じた。** 証明・focused build・境界検査・公理確認まで約18分、
検証済みsourceの途中公開とtree照合まで約22.6分。残りの時間を埋めるための補題は足さない。
最終報告の公開・照合時刻はcompleted heartbeatとcommit時刻で確認できる。
今回の1時間モードでは、固定例の追加でなく、任意深さの再帰と外側source入口の両方向の橋を選んだ。

**閉じた部分目標: 実mixed閉包が計算したsource evidenceから、実宣言のwhereを任意深さまで生成し、
失敗した子も含む診断木の到達先を、独立なsource導出・構造的materialization・宣言由来のPathと一致させた。**
callerにfuel、work table、有限visit列、成功した子、head map、Stateを渡させない。
唯一の親に「候補なしの子」と「候補が重なる子」が同居しても、両方の子と位置を残す。

新規2モジュール、266行+297行=563行、公開定理30本。一般T1c/B4の全体完成ではない。
新しい言語意味論の判断0件、質問ノート0件。B4の未完パッケージは引き続き5本。

## 公開と照合

source commit `92b1e026cd7a66fcaf3316e5e7ff7f4795026ac8`、tree `7271fa8d3792956a074b53b4a15fbae9a9ec2ffa`。
9 authored source pathsと、integrationからそのまま取り込んだinbox 1 pathを単一commitで公開。
各blobを個別作成してlocal git blob SHAとの一致を検査し、SHAだけのtreeをlive tree上に作った。
`work/dots-main`だけをexpected-head付きnonforceで更新した。

公開後にfetchしてcommit/treeを検査し、全10pathのblob SHAが一致。`lean/`、`notes/design/`、
`notes/plan/`の公開treeと検証済みlocal treeの差分は空。
`integration/m1-final` 125bf6e603499dc36c51db402d86f524a6467220が公開commitの祖先であることもexit0で確認。

integration125bfの変更はI-14 inboxのみだった。live heartbeatを維持し、inbox blob
17aead0c84e05fd698fe0f822c8eed2339030bd0を改変なしで取り込み、live workとintegrationの両親を保持した。
古いinboxを使ったmerge結果でI-14を消さないための同期であり、指示本文を独自に編集していない。

## 主定理の量化子・独立性・残る境界

- `diagnose_represents`: 任意の有限impls、`wf : WellFormed impls`、任意rigid goal gで、
  実diagnoseの木が独立な`Represents impls g`を満たす。各where childの停止は既存Patersonから導く。
  Representsのconstructorは独立Matches/Unique、正確なchild goal列と各childの表現を読む。
  builder、fuel、resolver statusは判断の定義に現れない。
- `represents_status`: 任意g/treeの独立Representsから、そのtreeの互換statusが既存Roles.resolveと等しい。
  `diagnose_status`と`diagnose_success_iff`も同じ既存rigid resolverへ接続する。
  この互換statusの優先順位を、sourceの新しい最終分類として採用しない。
- `diagnose_follow_exact`: 任意g、任意`path : List Nat`、任意tree tについて、実診断木のpath lookupがtを返すiff、
  独立Pathでそのgoalへ到達し、tが到達先の**全診断subtree**と等しい。成功した子は前提にしない。
  childの順序・重複を位置で保持し、成功状態の集合だけには弱めない。
- `run_exists_iff`: 任意の有限mixed sourceについて、外側入口がreportを返すiff既存ValidSource。
  ordinaryモデル存在もrole成功も診断を得るための前提ではない。
- `run_spec`: 任意env/roles/wf/awf/srcと実行結果reportで、source row列のerasureが元の句列と文字通り等しい。
  bare roleも残り、各rowのscalar候補は独立source Derivesとiff。
  supported attemptは構造的materializationと独立recursive Representsを持ち、unsupportedはmaterializationが存在しない。
  report.ordinary=true iff独立Models。`computed`は返ったreportを指すだけで、role成功の仮定ではない。
- `run_materialized_exact`: 任意の返ったrowと同じraw clause c、scalar b、tree tで、
  materialized b tが保持されるiff source Derivesがbを導き、構造的に埋めたgの全diagnoseがtである。
- **`run_path_exact`**: 任意env/roles/wf/awf/src、実report、元句c、scalar b、任意のchild address pathとtarget goalについて、
  cのrowのmaterialized attemptにtargetのchildが残るiff、元sourceがc.receiver:bを導き、
  cを構造的に埋めたgから独立Pathがtargetへ到達する。外側からslot map、head map、State、fuel、table、child成功を仮定しない。
  source由来と実再帰childの対応は両方向であり、固定深さの具体例だけの結果ではない。
- `observation_projection` / `run_success_iff`: tree情報を忘れた観測はcycle105と等しく、
  some(true,true) iff ValidSourceかつModelsかつAllDischarged。木を追加して受理規則を変えていない。

registryの同じImpl値の重複参照は既存Roles.candidatesが除く。異なる宣言keyは別の候補。
実overlap列は既存candidate列の順を保持するが、独立Representsはoverlap集合とNodupを述べ、
その順序までは指定しない。child列とsource row列の順序・重複は保持する。
source evidenceの同一scalarが重複する場合もattemptを残す。全言語の辞書観察同値を主張しない。

有限なscope解決済み句・ordinary不等式、placeholder0、既存int/str encoderの断片である。
ground templateもcycle105のreceiver evidenceを必要とする。bool/unitはunsupportedとして残る。
一般ordinary entailment、parser/式のlowering、動的にfresh slotを作るunknown where、一般Formは未完成。

## 追加定理の名前

- `CommonRoleRecursiveDiagnostics`: `unique_iff`, `diagnose_goal`, `diagnose_selected`, `diagnose_missing`, `diagnose_overlap`, `diagnose_status`, `diagnose_represents`, `diagnose_success_iff`, `represents_goal`, `represents_status`, `path_nil`, `path_cons`, `diagnose_follow_exact`.
- `CommonRoleSourceDiagnosticForest`: `attempt_base`, `materializes_iff`, `attempt_explains`, `attempt_accepted`, `inspect_explains`, `inspect_accepted`, `output_rows`, `output_explains`, `observation_projection`, `run_spec`, `run_exists_iff`, `run_success_iff`, `attempt_materialized_iff`, `inspect_materialized_exact`, `run_materialized_exact`, `run_clause_retained`, `run_path_exact`.

## 検証

focused 365 jobs、31実行guard、5 kernel example、30公理確認を通した。
公理はpropext / Classical.choice / Quot.soundのみ。
全体lake build、全Audit、build付きverify-leanは実行していない。以下のgateはdiff-only。

```text
cd lean; ELAN_HOME=../../elan timeout 150 ../../elan/bin/lake build Yulang.CommonRoleSourceDiagnosticForest --wfail
✔ [365/365] Built Yulang.CommonRoleSourceDiagnosticForest (1.1s)
Build completed successfully (365 jobs).
exit 0
```

```text
cd lean; ELAN_HOME=../../elan timeout 150 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang106/boundary.lean
(no output)
exit 0
```

```text
cd lean; ELAN_HOME=../../elan timeout 150 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang106/axioms.lean
'Yulang.CommonRoleRecursiveDiagnostics.unique_iff' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRecursiveDiagnostics.diagnose_goal' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRecursiveDiagnostics.diagnose_selected' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRecursiveDiagnostics.diagnose_missing' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRecursiveDiagnostics.diagnose_overlap' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRecursiveDiagnostics.diagnose_status' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRecursiveDiagnostics.diagnose_represents' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRecursiveDiagnostics.diagnose_success_iff' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleRecursiveDiagnostics.represents_goal' depends on axioms: [propext]
'Yulang.CommonRoleRecursiveDiagnostics.represents_status' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleRecursiveDiagnostics.path_nil' depends on axioms: [propext]
'Yulang.CommonRoleRecursiveDiagnostics.path_cons' depends on axioms: [propext]
'Yulang.CommonRoleRecursiveDiagnostics.diagnose_follow_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceDiagnosticForest.attempt_base' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceDiagnosticForest.materializes_iff' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceDiagnosticForest.attempt_explains' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceDiagnosticForest.attempt_accepted' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceDiagnosticForest.inspect_explains' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceDiagnosticForest.inspect_accepted' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceDiagnosticForest.output_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceDiagnosticForest.output_explains' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceDiagnosticForest.observation_projection' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleSourceDiagnosticForest.run_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceDiagnosticForest.run_success_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceDiagnosticForest.attempt_materialized_iff' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceDiagnosticForest.inspect_materialized_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleSourceDiagnosticForest.run_materialized_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleSourceDiagnosticForest.run_clause_retained' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceDiagnosticForest.run_path_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceDiagnosticForest.run_exists_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

```text
python3 tools/boundary-input-inventory.py --check
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=275; Main=93; Audit=275; ledger mentioned=148. Mention counts are not audit completion counts.
exit 0
```

```text
bash tools/verify-lean.sh . origin/integration/m1-final --no-build
verify-lean: . @ 95add7c56 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
exit 0
```

git diff --checkとstaged diff --checkも成功。ソースSHA256:
- CommonRoleRecursiveDiagnostics: 57039f44e9e34d0e589ea680230921a65e2a9f9928f04a9780238baa9fd0ade9
- CommonRoleSourceDiagnosticForest: 2ef73271f27005d466237b07ede6cdbc763f2eeed7a748d1c080da71ba7b78c4

境界suiteは深さ32の成功・失敗、範囲外のchild index、overlap親で探索を止めること、
missing/overlap兄弟の同居、重複childの異なる位置、同一impl参照の重複と異なるkey、
bare role、空evidence、unsupported bool、不正scope/arity、ordinary矛盾、空sourceを検査する。
5 kernel exampleは独立Represents、既存missing例への一般status適用、3 childの保持、
独立Pathの構成、実source reportから失敗childの保持への一般path定理の適用。
深さ32そのものの実行guardを、具体的なkernel展開の証明とは数えない。

初回の新規境界fixtureは同一scalar attemptが1つだと誤って期待していた。
実行出力を調べると、既存mixed closureが両input bound由来の証拠を保持し、2 attemptになる。
本adapterは候補をdeduplicateしない契約なので、その2件と両方のchild列を明示して検査し直した。
production挙動や既存の期待値は変更していない。

探索中のコンパイルでは存在しないList補題名、let簡約、ローカルbinder名、有限checkerの存在証明を修正。
report ordinary projectionの自動展開は200k/1.6m heartbeatで時間切れになり、
`output`のprojectionだけを明示simpして、最終focused buildは約1秒に戻した。
初回と最終のログをcache/yulang106に分けて保持している。未完のbuild processはない。

## independent review とCI

独立read-only reviewは2モジュール、関連定義、spec6.2/6.3と設計を確認し、
semanticなmissing hypothesisや循環的specificationのblocking指摘はなかった。
「registry重複も保持する」という設計文だけが広すぎたので、既存candidate dedupと
independent overlap順序の範囲に修正した。reviewerはbuild/公理監査を実行していない。
提案された境界例はsuiteに含め、最終検査を通した。

exact-source remote CIは未確認。GitHub connectorのworkflow取得はPR-triggerのみで空、
combined statusも空だった。gh CLIは未ログイン(exit4)、公式Actions APIの匿名readはHTTP403で停止。
これはCI成功・失敗の証拠ではない。監督役はsource commit92b1e026に対するCore/Lean CIを確認すること。
この制約はlocal focused/axiom/regressionの成功を取り消さないが、全体PASSとは呼ばない。

## 復旧・運用・残り

前cycle105のcompleted heartbeatとreportを確認。live work166d1de06、integration125bf6e60を取得。
ACTIVE、STOPなし、上限なし、I-14の途中公開・心拍・full build禁止を確認。
さらに親から最新ユーザーの毎時55分上限の指示が届いた。上限を使い切るための作業はしない。
保持cloneをそのまま使い、integrationをmerge、別writer/前cycle processなし。復旧不要。
開始空き47G、終了準備空き47G。clone/cacheの増設や削除なし。使用量の枠は不明。

開始heartbeat fbc9ab787、10分heartbeat699239ff、20分heartbeat9271fb144。
sourceは開始約22分で公開したため25分checkpointを満たす。source以後のproduction変更はない。
最終はreportとcompleted heartbeatのみを公開・照合する。異なる公開pathは計12。

B4に残る5パッケージ:
1. source_boundary_adequate: checked finite sourceからdiagnosticまでは接続。実parser/式/宣言、scope/invocation導出が未完成。
2. generated_work_closed: rigid materialized goalの全where childとPathは内部生成できた。
   unknown materializationでfresh source/slotが増える一般の動的領域閉包は未完成。
3. saturate_terminates_and_closes: finite mixed closureとrigid Patersonを接続。
   一般Formのstate更新・動的仕事・fairnessを含む停止と閉包は未完成。
4. saturated_frontier_exact: source evidenceから失敗保持のrecursive treeへは接続。
   ファイル終端の安定化、全四分類、診断の最終写像は未完成。
5. resolve_dictionary_order_sound: 子の位置は保持するが、source義務の正準順と
   language-level辞書の観察同値・解釈への橋は未完成。

次候補は(a) rigid treeの成功部分と実dictionary Planの構造的一致、
(b) source式からordinary不等式の意味保存、(c) unknown whereの実生成child領域閉包。
固定例を一般定理の代わりにしない。未完成のB4橋をcaller前提として外へ隠さない。

## 再実行可能な境界suite

```lean
import Yulang.CommonRoleSourceDiagnosticForest
open Yulang Roles Roles.Examples
open CommonRoleRecursiveDiagnostics
namespace Cycle106
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 4096

def deep : Nat → Term → Term
  | 0,t => t
  | n+1,t => list (deep n t)
def good (g : Goal) := diagnose goodImpls goodImpls_wellFormed g
#guard (good (display (deep 32 int))).status = .resolved
#guard ((good (display (deep 32 int))).follow (List.replicate 32 0)).map Tree.goal = some (display int)
#guard ((good (display (deep 32 int))).follow (List.replicate 33 0)).isNone
#guard (good (display (deep 32 str))).status = .noImpl
#guard ((good (display (deep 32 str))).follow (List.replicate 32 0)).map Tree.status = some .noImpl
#guard ((good (display (deep 32 str))).follow [1]).isNone
#guard ((diagnose overlappingImpls overlappingImpls_wellFormed (display (list int))).children).isEmpty
#guard (diagnose overlappingImpls overlappingImpls_wellFormed (display (list int))).status = .ambiguous

def parent : Impl := ⟨9,[list (.var 0)],[display (.var 0),foo (.var 0),display (.var 0)],90⟩
def foo1 : Impl := ⟨1,[str],[],91⟩
def foo2 : Impl := ⟨1,[str],[],92⟩
def mixed : List Impl := [parent,foo1,foo2]
theorem mixed_wf : WellFormed mixed := by
  simp [WellFormed,mixed,Impl.WellFormed,parent,foo1,foo2,display,foo,list,
    argsSize,Term.size,argsOccurrences,Term.occurrences]
def goal : Goal := ⟨9,[list str]⟩
def tree := diagnose mixed mixed_wf goal
#guard tree.status = .ambiguous
#guard tree.children.map Tree.status = [.noImpl,.ambiguous,.noImpl]
#guard tree.children.map Tree.goal = [display str,foo str,display str]
#guard (tree.follow [0]).map Tree.status = some .noImpl
#guard (tree.follow [1]).map Tree.status = some .ambiguous
#guard (tree.follow [2]).map Tree.status = some .noImpl
#guard (tree.follow [1,0]).isNone
#guard (tree.follow [3]).isNone

def liftImpl (i : Impl) : AssocImpl := ⟨i,[],by decide⟩
def env (xs : List Impl) : AssocEnv where
  impls := xs.map liftImpl
  coherent := by
    intro i hi j hj _
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hi
    obtain ⟨b,_,rfl⟩ := List.mem_map.mp hj
    rfl

theorem cores (xs : List Impl) : (env xs).cores = xs := by
  simp [env,AssocEnv.cores,Function.comp_def,liftImpl]
def roles : RoleDecls := fun _ => ⟨1,fun _ => none,by intros; contradiction⟩
theorem env_wf : WellFormed (env mixed).cores := by rw [cores]; exact mixed_wf
theorem env_awf : AssocWellFormed (env mixed) roles := by
  intro i hi
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  simp only [mixed,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl | rfl <;>
    simp [AssocHeadVars,AssocComplete,AssocDeclared,liftImpl,roles,parent,foo1,foo2]

def clause : CommonRoleAssociatedClauseExtraction.Clause := ⟨10,⟨9,[list (.var 0)]⟩,[]⟩
def seed : CommonRoleNamedOrdinaryInputs.Input := [(.var 10,.base .str),(.base .str,.var 10)]
def source : CommonRoleCheckedMixedSource.Source := ⟨[clause],seed⟩
def run := CommonRoleSourceDiagnosticForest.run (env mixed) roles env_wf
open CommonRoleSourceDiagnosticForest (Attempt Row Report)
def trees (r : Report) : List Tree := r.rows.flatMap fun row => row.attempts.filterMap fun
  | .materialized _ t => some t
  | .unsupported _ => none
#guard (run source).map Report.observation = some (true,false)
-- Both input bounds survive mixed closure, producing two evidence attempts.
#guard ((run source).map trees).map (List.map Tree.status) = some [.ambiguous,.ambiguous]
#guard ((run source).map trees).map (fun ts => ts.flatMap (fun t => t.children.map Tree.status)) =
  some [.noImpl,.ambiguous,.noImpl,.noImpl,.ambiguous,.noImpl]
#guard ((run ⟨[clause,clause],seed⟩).map Report.rows).map List.length = some 2
#guard ((run ⟨[clause],[]⟩).map Report.rows).map (fun rs => rs.flatMap Row.attempts |>.length) = some 0
#guard ((run ⟨[clause],[(.var 10,.base .bool),(.base .bool,.var 10)]⟩).map trees).map List.length = some 0
#guard ((run ⟨[clause],[(.var 10,.base .bool),(.base .bool,.var 10)]⟩).map Report.rows).map
  (fun rs => rs.flatMap Row.attempts |>.map Attempt.base) = some [.bool,.bool]
#guard (run ⟨[⟨10,⟨9,[.var 1]⟩,[]⟩],seed⟩).isNone
#guard (run ⟨[⟨10,⟨9,[]⟩,[]⟩],seed⟩).isNone
#guard (run ⟨[clause],seed ++ [(.var 10,.base .int),(.base .int,.var 10)]⟩).map Report.ordinary = some false
#guard (run ⟨[],[]⟩).map Report.observation = some (true,true)
#guard (run ⟨[],[(.base .str,.base .int)]⟩).map Report.observation = some (false,true)

example : Represents mixed goal tree := diagnose_represents mixed mixed_wf goal
example : (good (display (list str))).status = .noImpl := by
  rw [good,diagnose_status]
  exact missing_str_noImpl
example : tree.children.length = 3 := by
  rw [tree,diagnose_selected mixed mixed_wf goal parent (by decide)]
  simp only [Tree.children,List.length_map]
  rfl
example : CommonRoleRecursiveDiagnostics.Path mixed goal [0] (display str) := by
  apply Path.step parent (display (.var 0)) ((unique_iff mixed goal parent).mpr (by decide)) (by decide)
  have eq : (display (.var 0)).subst (matchingSubst parent.head goal.args) = display str := by decide
  rw [eq]
  exact Path.root (display str)
example (r : Report) (computed : run source = some r) :
    ∃ row ∈ r.rows, row.obligation = CommonRoleSourceRoleObligations.raw clause ∧
      ∃ t, Attempt.materialized .str t ∈ row.attempts ∧
        ∃ child, t.follow [0] = some child ∧ child.goal = display str := by
  apply (CommonRoleSourceDiagnosticForest.run_path_exact (env mixed) roles env_wf env_awf
    source r computed clause (by simp [source]) .str [0] (display str)).mpr
  refine ⟨.initial (by simp [source,seed,clause]) (by simp [source,seed,clause]),goal,?_,?_⟩
  · exact ⟨str,rfl,rfl,by
      apply (CommonRoleStructuralAssociatedTemplates.fills_exact str clause.goal.args goal.args (by decide)).mpr
      decide⟩
  · rw [cores]
    apply Path.step parent (display (.var 0)) ((unique_iff mixed goal parent).mpr (by decide)) (by decide)
    have eq : (display (.var 0)).subst (matchingSubst parent.head goal.args) = display str := by decide
    rw [eq]
    exact Path.root (display str)
theorem duplicate_wf : WellFormed [listImpl,listImpl] := by
  simp [WellFormed,listImpl_wellFormed]
#guard (diagnose [listImpl,listImpl] duplicate_wf (display (list str))).status = .noImpl
#guard (diagnose [listImpl,listImpl] duplicate_wf (display (list str))).children.length = 1
#guard (tree.follow [1]).map (fun t => match t with
  | .overlap _ hs => hs.map Impl.key
  | _ => []) = some [91,92]
end Cycle106
```
