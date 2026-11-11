# dots cycle 107 — source 診断木から実辞書 Plan への完全な対応

## 所要時間・部分目標

開始 2026-11-11T02:23:42Z。報告準備 2026-11-11T02:42:05.055106+00:00、約18.4分。
**部分目標は25分以内に閉じた。** 核とsourceの証明・focused buildは約7分、
境界suiteと公理確認は約12分、検証済みsourceの公開・tree照合は約16分。
時間を埋めるための補題は足さず、今回の部分目標を閉じて終了する。
最終報告の公開・照合時刻はcompleted heartbeatとcommit時刻で確認できる。

**閉じた部分目標: 計算されたsource evidenceから得た再帰診断木の成功部分を、
既存の型付きDictionaryの完全なPlanと両方向で一致させた。選ばれた宣言の同一性、
whereの順序・重複、任意深さの子位置を保持し、失敗した診断は元のreportに丸ごと残す。**
単なるsuccess bitの一致ではない。sourceの実入口で実行し、callerに成功木、辞書、
head map、State、fuel、work table、実行traceを渡させない。

新規2モジュール、173行+200行=373行、公開定理23本。
一般T1c/B4の全体完成ではない。新しい意味論の判断0件、質問ノート0件。
全体B4の未完パッケージは5本のまま。

## 公開と照合

source commit `1ed83de41d779782b413d49c85cb15c2837c0ee6`、tree
`d312771de0740a52aee1d123283dc6cd3d75b44f`。
9 authored source pathsを単一commitで公開。各blobのSHAをlocal git blobと照合し、
live tree上にSHAだけのtreeを作り、`work/dots-main`だけをexpected-head付きnonforceで更新した。
公開直前に両枝を再取得し、ownerによる同時変更がないことを確認した。

公開後に明示的refspecでfetchし、公開commit/treeを照合。
`git diff --exit-code HEAD origin/work/dots-main -- lean notes/design notes/plan` はexit0。
全9pathのblob一致を確認し、integration `3fdc8fe2d5e0024975a6ac1a6455c2064dbff164`
が公開commitの祖先であることもexit0で確認した。source以後にproduction変更なし。
最後の公開はこのreportとcompleted heartbeatの2pathだけ。異なる公開pathは計11。

## 定理の正確な範囲

- `project`はTreeだけを読む実行可能な構造再帰。missing/overlapはPlanを返さず、
  selectedは全childを順にprojectできたときだけ既存Plan.nodeを返す。
  適当に作ったTreeに対する`project_success`はstatusとの構造的一致だけであり、
  そのTreeが正しい辞書だとは主張しない。
- **`dictionary_projects`**: 任意の有限impls、`wf : WellFormed impls`、goal g、
  既存`d : RoleDictionaries.Dictionary impls g`に対し、
  `project (diagnose impls wf g) = some d.erase`。
  dは比較対象として全量化され、実行への外部入力ではない。宣言とchild列の完全な等式である。
- **`diagnose_project_exact`**: 任意impls/wf/g/Plan pで、実診断のprojectionがpを返すiff、
  既存の独立な型付きDictionaryが存在し、そのeraseがpと等しい。
  `diagnose_project_elaborate`は既存の実`RoleDictionaries.elaborate`とも一致させる。
- `project_follow_exact`: 任意Tree tと、そのprojectionが実際にpを返した等式、任意address path、
  Plan qに対し、pのpath lookupがqを返すiff、tの同じ位置のchildがあり、そのprojectionがqを返す。
  同じchild値の重複も別の位置に残る。
- **`diagnose_plan_path_exact`**: 任意impls/wf/g、実際に返ったroot Plan、任意path/qで、
  lookupがqを返すiff、独立な宣言由来Pathのtargetと、そのtargetのDictionaryが存在し、
  Dictionary.eraseがqと等しい。深さの固定上限や成功child traceは前提にしない。
- `enrich_erase` / `run_erasure`: sourceの全rowと全scalar attemptにoptional Planを足すが、
  literal erasureでcycle106のreportそのものに戻る。失敗tree、unsupported、空evidence、
  source行の順序・重複を削除しない。
- **`run_plan_exact`**: 任意env、roles、wf、`awf : AssocWellFormed env roles`、有限src、
  実runの返ったreport r、rに属するrow、同じraw obligationを持つClause c、scalar b、Plan pで、
  rowにbの成功Plan pがあるiff、独立source Derivesがc.receiver:bを導き、
  構造的Materializes c b gが成り立つgoal gとDictionary env.cores gが存在し、eraseがpと等しい。
  row membership、same obligation、well-formednessを省略していない。
- **`run_plan_path_exact`**: 上と同じsource/row境界と任意path/qに対して、
  rowの返ったroot Planからqへ辿れるiff、source Derives、Materializesに加えて、
  **rootの独立Resolves**と独立Path、およびtargetのDictionary.erase=qが成り立つ。
  root成功は右辺の特徴づけに明記し、実行の入力にはしない。
  あるchildが成功しても、兄弟が失敗すればroot Planは作れない。
- `run_plan_visible`: 返ったPlanの任意深さの全宣言は根のcaller-visible env.coresに属する。
- `run_spec` / `run_success_iff`: source行は元の句列と文字通り対応し、ordinary=true iff Models。
  全体のsome(true,true) iff ValidSource ∧ Models ∧ AllDischarged。
  個々のPlan存在にはordinary整合性を要求しない。矛盾するordinary sourceにもPlanが残りうるが、
  そのreportを全体成功とはしない。

source boundaryは以前と同じ有限scope解決済み句とnamed ordinary不等式、placeholder0、
int/str encodingの断片である。一般Form、parser/式/宣言のlowering、動的fresh slot、
source義務の正準順と辞書の観察同値、method実行、最終四分類を証明していない。
複数scalar evidenceから全体として一つの辞書を選ぶ機能も追加していない。
今回の順序は既存Dictionaryが採用する宣言内where列であり、任意source順への不変性ではない。

## 追加定理

- `CommonRoleDiagnosticDictionaries`: `mapM_isSome`, `mapM_some_of_pointwise`, `project_success`, `dictionary_projects`, `diagnose_project_exact`, `diagnose_project_elaborate`, `project_all_visible`, `mapM_getElem`, `project_children`, `project_follow_exact`, `diagnose_plan_path_exact`.
- `CommonRoleSourceDictionaryForest`: `enrichRow_erase`, `enrich_erase`, `run_erasure`, `attach_accepted`, `enrich_observation`, `run_success_iff`, `run_exists_iff`, `run_spec`, `enrichRow_plan_exact`, `run_plan_exact`, `run_plan_visible`, `run_plan_path_exact`.

## 検証

focused367 jobs、62実行guard、9kernel example、23新定理の公理確認が成功。
公理はpropext / Classical.choice / Quot.soundのみ。
全体lake build、全Audit、build付きverify-leanは常設指示により実行していない。
verify-leanの下のPASSはdiff-onlyであり、全体PASSではない。

```text
cd lean; ELAN_HOME=../../elan timeout 150 ../../elan/bin/lake build Yulang.CommonRoleSourceDictionaryForest --wfail
✔ [367/367] Built Yulang.CommonRoleSourceDictionaryForest (1.2s)
Build completed successfully (367 jobs).
exit 0
```

```text
cd lean; ELAN_HOME=../../elan timeout 150 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang107/boundary.lean
(no output)
exit 0
```

```text
cd lean; ELAN_HOME=../../elan timeout 150 ../../elan/bin/lake env lean --trust=0 ../../cache/yulang107/axioms.lean
'Yulang.CommonRoleDiagnosticDictionaries.mapM_isSome' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDiagnosticDictionaries.mapM_some_of_pointwise' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDiagnosticDictionaries.project_success' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDiagnosticDictionaries.dictionary_projects' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDiagnosticDictionaries.diagnose_project_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDiagnosticDictionaries.diagnose_project_elaborate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDiagnosticDictionaries.project_all_visible' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleDiagnosticDictionaries.mapM_getElem' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDiagnosticDictionaries.project_children' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleDiagnosticDictionaries.project_follow_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleDiagnosticDictionaries.diagnose_plan_path_exact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Yulang.CommonRoleSourceDictionaryForest.enrichRow_erase' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceDictionaryForest.enrich_erase' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceDictionaryForest.run_erasure' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceDictionaryForest.attach_accepted' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceDictionaryForest.enrich_observation' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceDictionaryForest.run_success_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceDictionaryForest.run_exists_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceDictionaryForest.run_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceDictionaryForest.enrichRow_plan_exact' depends on axioms: [propext, Quot.sound]
'Yulang.CommonRoleSourceDictionaryForest.run_plan_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceDictionaryForest.run_plan_visible' depends on axioms: [propext, Classical.choice, Quot.sound]
'Yulang.CommonRoleSourceDictionaryForest.run_plan_path_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
exit 0
```

```text
bash tools/verify-lean.sh . origin/integration/m1-final --no-build
verify-lean: . @ 55ffedf314 (base origin/integration/m1-final)
ok: no removed lines in lean/ since origin/integration/m1-final
ok: no sorry/native_decide/axiom-like constructs in added lines
ok: lake config unchanged (or only SpecExamples*/Main* libs added)
ok: new files are Yulang modules only
ok: Audit.lean only appended (plus top import lines)
verify-lean: PASS (diff checks only, NO build)
exit 0
```

```text
python3 tools/boundary-input-inventory.py --check
PASS: inventory matches source hashes, imports, and ledger mentions.
CommonRole import scope=277; Main=93; Audit=277; ledger mentioned=150. Mention counts are not audit completion counts.
exit 0
```

git diff --checkとstaged diff --checkも成功。source SHA256:
- CommonRoleDiagnosticDictionaries: 293a3acd92edadee2ec82ad9ec4c8fdbfa43bcf6c4cd7c5abf0ba738801e6e3b
- CommonRoleSourceDictionaryForest: e45aa424c6975338b3282d7d649e1d3dd7c9e4e6c2a20f631d08382c7a1a601d

境界suiteはcycle106の31guard/5exampleを保持し、今回31guard/4exampleを追加した。
深さ32の辞書・末端lookup、空path、leafの外、異なる宣言を含む[A,B,A]の三兄弟、
範囲外index、missing/overlap、成功childと失敗兄弟の同居、source重複、bare role、
empty evidence、unsupported bool、不正scope/arity、空source、ordinary矛盾と成功Planの同居を確認した。
深さ32の実行guardを、kernelによる具体的展開の証明とは数えない。
reportのrepr比較は補助実行検査であり、完全なerasure等式は一般定理で証明した。

初回のtest-only fixtureは旧namespaceの開き方に由来するReport名の曖昧性と、
well-founded診断/resolveをrflやdecideだけで展開できない箇所で失敗した。
完全修飾名と既存の一段展開定理で直し、期待値やproduction挙動は変更していない。
探索中のproofではnested recursorのbinderとattach/mapMの等式の向きを直した。
axiom runnerの最初の起動はcwd/toolchain指定誤りで未実行だったが、正しいlean cwdで再実行し成功。
最終ログと初回失敗ログを分けて保持。実行中のbuildはない。

## 独立reviewとCI

独立read-only reviewは新規2モジュール、既存の診断・Dictionary、設計を調べ、
missing hypothesisや循環的specificationのblocking指摘はなかった。
source主張の設計文にawfとmatching row条件を明記する指摘を反映した。
reviewerはbuildや公理監査を実行していない。提案された境界例を上記suiteで検査した。

exact-source CIは未確認。source commit1ed83de4に対するGitHub workflow取得は
PR-trigger限定のwrapperで空、combined statusも空。push-trigger CIの成功/失敗を示さない。
このサイクルでは前回失敗した匿名APIや未認証CLIを繰り返していない。
監督役はこの正確なsource commitのCore/Lean CIと全体検証を確認すること。

## 復旧・時間・残る橋

cycle106のcompleted heartbeatと対応reportを確認。live integration/workは共に3fdc8fe2。
ACTIVE、STOPなし、回数上限なし、I-14の心拍・途中公開・全体build禁止を確認。
前cycleのwriterやLean processなし。保持cloneを継続し、integrationをmergeした。復旧不要。
開始のdateは02:23:42。開始ログ用ファイル作成は02:24:03で、心拍には最初のdateを使った。
開始空き45G、終了準備空き45G。clone/cacheの増設や削除なし。使用量の枠は不明。

開始heartbeat1087e895、10分heartbeat041e0811。sourceを約16分で公開・照合し、
25分checkpointより前に検証済み成果を保存した。最終はreportとcompleted heartbeatのみ。
remote.origin.fetchの設定がintegrationのみだったため、work枝の明示refspecで最新の
remote-tracking refを更新した。古いtracking refを公開先headと誤認した更新はしていない。

B4に残る5パッケージ:
1. source_boundary_adequate: finite checked source→diagnostic→実Planは接続。
   実parser/式/宣言のlowering、scope/invocation導出は未完成。
2. generated_work_closed: rigid goalのwhereとchild位置は内部生成。
   unknown materializationでfresh source/slotを増やす一般の動的領域閉包は未完成。
3. saturate_terminates_and_closes: finite mixed closureとrigid Patersonの範囲に限る。
   一般Formのstate更新、動的仕事、fairnessを含む停止と意味的閉包は未完成。
4. saturated_frontier_exact: failed diagnosticと成功Planは対応したが、
   ファイル終端安定化、全四分類、診断から最終分類への写像は未完成。
5. resolve_dictionary_order_sound: rigid宣言内whereの順序と実Planは完全一致。
   source義務の正準順、unknown状態の辞書、method解釈とlanguage-level観察同値は未完成。

次候補: (a) source式からordinary不等式の意味保存、
(b) unknown whereの実生成child領域閉包、(c) source義務順から既存Plan順への橋。
未証明のB4橋をcaller前提として隠さない。新規の意味論の判断が必要なら既存の質問境界を使う。

## 再実行可能な境界suite

```lean
import Yulang.CommonRoleSourceDictionaryForest
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

namespace Cycle107
open Yulang Roles Roles.Examples RoleDictionaries
open CommonRoleRecursiveDiagnostics
open CommonRoleDiagnosticDictionaries

def keys (p : Plan) : List Nat := p.declarations.map Impl.key
def rigid (g : Goal) := project (diagnose goodImpls goodImpls_wellFormed g)
#guard (rigid (display int)).map keys = some [1]
#guard (rigid (display (list int))).map keys = some [0,1]
#guard (rigid (display (Cycle106.deep 32 int))).map keys = some (List.replicate 32 0 ++ [1])
#guard ((rigid (display (Cycle106.deep 32 int))).bind fun p => follow p (List.replicate 32 0)).map keys = some [1]
#guard ((rigid (display (Cycle106.deep 32 int))).bind fun p => follow p (List.replicate 33 0)).isNone
#guard (rigid (display (list str))).isNone
#guard (project (diagnose overlappingImpls overlappingImpls_wellFormed (display (list int)))).isNone
#guard ((rigid (display (list int))).bind fun p => follow p []).map keys = some [0,1]
#guard ((rigid (display int)).bind fun p => follow p [0]).isNone

def fooInt : Impl := ⟨1,[int],[],92⟩
def impls : List Impl := [Cycle106.parent,intImpl,fooInt]
theorem wf : WellFormed impls := by
  simp [WellFormed,impls,Impl.WellFormed,Cycle106.parent,intImpl,fooInt,display,foo,list,
    argsSize,Term.size,argsOccurrences,Term.occurrences]
def goal : Goal := ⟨9,[list int]⟩
def tree := diagnose impls wf goal
def plan := project tree
#guard plan.map keys = some [90,1,92,1]
#guard (plan.bind fun p => follow p [0]).map keys = some [1]
#guard (plan.bind fun p => follow p [1]).map keys = some [92]
#guard (plan.bind fun p => follow p [2]).map keys = some [1]
#guard (plan.bind fun p => follow p [3]).isNone
#guard tree.children.map Tree.status = [.resolved,.resolved,.resolved]

def missingImpls : List Impl := [Cycle106.parent,intImpl]
theorem missing_wf : WellFormed missingImpls := by
  simp [WellFormed,missingImpls,Impl.WellFormed,Cycle106.parent,intImpl,display,foo,list,
    argsSize,Term.size,argsOccurrences,Term.occurrences]
def missingTree := diagnose missingImpls missing_wf goal
#guard (project missingTree).isNone
#guard (missingTree.follow [0] |>.bind project).map keys = some [1]
#guard missingTree.children.map Tree.status = [.resolved,.noImpl,.resolved]

def env := Cycle106.env impls
theorem env_wf : WellFormed env.cores := by rw [env,Cycle106.cores]; exact wf
theorem env_awf : AssocWellFormed env Cycle106.roles := by
  intro i hi
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hi
  simp only [impls,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl | rfl <;>
    simp [AssocHeadVars,AssocComplete,AssocDeclared,Cycle106.liftImpl,Cycle106.roles,
      Cycle106.parent,intImpl,fooInt]

def seed : CommonRoleNamedOrdinaryInputs.Input := [(.var 10,.base .int),(.base .int,.var 10)]
def src : CommonRoleCheckedMixedSource.Source := ⟨[Cycle106.clause],seed⟩
def run := CommonRoleSourceDictionaryForest.run env Cycle106.roles env_wf
def payloads (r : Yulang.CommonRoleSourceDictionaryForest.Report) : List (Option (List Nat)) :=
  r.rows.flatMap fun row => row.attempts.map (fun e => e.plan.map keys)
def diagnostics (r : Yulang.CommonRoleSourceDictionaryForest.Report) : List CommonRoleSourceDiagnosticForest.Attempt :=
  r.rows.flatMap fun row => row.attempts.map Yulang.CommonRoleSourceDictionaryForest.Entry.diagnostic
#guard (run src).map Yulang.CommonRoleSourceDictionaryForest.Report.observation = some (true,true)
#guard (run src).map payloads = some [some [90,1,92,1],some [90,1,92,1]]
#guard ((run src).map Yulang.CommonRoleSourceDictionaryForest.Report.erase).map reprStr =
  (CommonRoleSourceDiagnosticForest.run env Cycle106.roles env_wf src).map reprStr
#guard ((run ⟨[Cycle106.clause,Cycle106.clause],seed⟩).map Yulang.CommonRoleSourceDictionaryForest.Report.rows).map List.length = some 2
#guard ((run ⟨[Cycle106.clause],[]⟩).map payloads) = some []
#guard (run ⟨[Cycle106.clause],[]⟩).map Yulang.CommonRoleSourceDictionaryForest.Report.observation = some (true,false)
#guard (run ⟨[Cycle106.clause],[(.var 10,.base .bool),(.base .bool,.var 10)]⟩).map payloads = some [none,none]
#guard ((run ⟨[Cycle106.clause],[(.var 10,.base .bool),(.base .bool,.var 10)]⟩).map diagnostics).map
  (List.map CommonRoleSourceDiagnosticForest.Attempt.base) = some [.bool,.bool]
def contradictory : CommonRoleCheckedMixedSource.Source :=
  ⟨[Cycle106.clause],seed ++ [(.base .str,.base .int)]⟩
#guard (run contradictory).map Yulang.CommonRoleSourceDictionaryForest.Report.observation = some (false,true)
#guard (run contradictory).map payloads = some [some [90,1,92,1],some [90,1,92,1]]
#guard (run ⟨[],[]⟩).map Yulang.CommonRoleSourceDictionaryForest.Report.observation = some (true,true)
#guard (run ⟨[⟨10,⟨9,[.var 1]⟩,[]⟩],seed⟩).isNone
#guard (run ⟨[⟨10,⟨9,[]⟩,[]⟩],seed⟩).isNone

example : rigid (display (list int)) = some (.node listImpl [.node intImpl []]) := by
  have leaf : diagnose goodImpls goodImpls_wellFormed (display int) = .selected (display int) intImpl [] := by
    rw [diagnose_selected goodImpls goodImpls_wellFormed (display int) intImpl (by decide)]
    rfl
  have root : diagnose goodImpls goodImpls_wellFormed (display (list int)) =
      .selected (display (list int)) listImpl [diagnose goodImpls goodImpls_wellFormed (display int)] := by
    rw [diagnose_selected goodImpls goodImpls_wellFormed (display (list int)) listImpl (by decide)]
    rfl
  simp [rigid,root,leaf,project]
example : (project missingTree).isSome = false := by
  have no : missingTree.status = .noImpl := by
    rw [missingTree,diagnose_status]
    have leaf : resolve missingImpls missing_wf (display int) = .resolved := by
      rw [resolve_one missingImpls missing_wf (display int) intImpl (by decide)]
      rfl
    have absent : resolve missingImpls missing_wf (foo int) = .noImpl :=
      resolve_none missingImpls missing_wf (foo int) (by decide)
    rw [resolve_one missingImpls missing_wf goal Cycle106.parent (by decide)]
    change combine [resolve missingImpls missing_wf (display int),
      resolve missingImpls missing_wf (foo int),resolve missingImpls missing_wf (display int)] = .noImpl
    rw [leaf,absent]
    rfl
  cases h : (project missingTree).isSome with
  | false => rfl
  | true => have := (project_success missingTree).mp h; rw [no] at this; cases this
example (p : Plan) (h : project tree = some p) :
    follow p [2] = some (.node intImpl []) ↔
      ∃ target, Path impls goal [2] target ∧
        ∃ d : Dictionary impls target, d.erase = .node intImpl [] :=
  diagnose_plan_path_exact impls wf goal p h [2] (.node intImpl [])
example (r : Yulang.CommonRoleSourceDictionaryForest.Report) (computed : run src = some r) (row : Yulang.CommonRoleSourceDictionaryForest.Row) (member : row ∈ r.rows)
    (same : row.obligation = CommonRoleSourceRoleObligations.raw Cycle106.clause) (p : Plan) :
    (∃ t, Yulang.CommonRoleSourceDictionaryForest.Entry.mk (.materialized .int t) (some p) ∈ row.attempts) ↔
      CommonRoleCheckedMixedSource.Derives env Cycle106.roles src Cycle106.clause.receiver .int ∧
      ∃ g, CommonRoleSourceDiagnosticForest.Materializes Cycle106.clause .int g ∧
        ∃ d : Dictionary env.cores g, d.erase = p :=
  CommonRoleSourceDictionaryForest.run_plan_exact env Cycle106.roles env_wf env_awf src r computed
    row member Cycle106.clause same .int p
end Cycle107
```
