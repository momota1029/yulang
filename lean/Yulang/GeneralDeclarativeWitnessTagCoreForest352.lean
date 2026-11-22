import Yulang.GeneralDeclarativeWitnessTagCoreBranch352
import Yulang.GeneralDeclarativeWitnessMixedCompletion352

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTagCoreForest352
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeWitnessMixedForest352 (Problem Global Code Codes atNode)
open GeneralDeclarativeWitnessTagCoreBranch352 (CoreRoute)
open GeneralDeclarativeWitnessTree349 (Report agrees exact_report)
open GeneralDeclarativeWitnessOrigins350 (attach)
open GeneralSourceMetadataBareBundle291 (compile)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂ Tree Dictionary Result Summarizes classification classification_exact classifications classifications_exact)

structure Replay {p : Problem} (g : Global p) (d : Demand) where
  tree : Tree
  dictionary : Dictionary
  written : classification tree = .selected dictionary
  truth : ∀ m : Assignment, Models p.current m →
    Evidence (registry g.table) (interpretation g.table.snapshot) m d dictionary

structure Children {p : Problem} (g : Global p) (ds : List Demand) where
  trees : List Tree
  dictionaries : List Dictionary
  written : classifications trees = dictionaries.map Result.selected
  truth : ∀ m : Assignment, Models p.current m →
    All₂ (Evidence (registry g.table) (interpretation g.table.snapshot) m) ds dictionaries

mutual
def tree {p : Problem} (g : Global p) (path : List Nat) (d : Demand) : Code → Option (Replay g d)
  | .node (.record _) _ => none
  | .node (.tagged w) childCode => do
    let localNode ← GeneralDeclarativeWitnessTagCoreBranch352.decode (atNode p path d) g.canonical g.live w
    let descendant ← forest g path 0 localNode.kids childCode
    pure ⟨.selected localNode.decl.id descendant.trees,.node localNode.decl.id descendant.dictionaries,
      (classification_exact ..).mpr (.selected ((classifications_exact ..).mp descendant.written) (.selected rfl)),
      fun m fit => .node (localNode.meaning m fit) (descendant.truth m fit)⟩
termination_by c => sizeOf c

def forest {p : Problem} (g : Global p) (path : List Nat) (idx : Nat) (ds : List Demand) :
    Codes → Option (Children g ds)
  | .nil =>
    match ds with
    | [] => some ⟨[],[],rfl,fun _ _ => .nil⟩
    | _::_ => none
  | .cons one more =>
    match ds with
    | [] => none
    | child::kids => do
      let first ← tree g (path ++ [idx]) child one
      let tail ← forest g path (idx+1) kids more
      pure ⟨first.tree :: tail.trees,first.dictionary :: tail.dictionaries,
        by simp only [classifications,first.written,tail.written,List.map_cons],
        fun m fit => .cons (first.truth m fit) (tail.truth m fit)⟩
termination_by c => sizeOf c
end

structure Accepted (p : Problem) (report : Report) where
  global : Global p
  replayed : Replay global p.target
  agreement : agrees (GeneralDeclarativeWitnessMixedWhole352.goal p p.target) replayed.tree report = true

/-- A conservative additional view, only for a legacy-compatible wholly
literal tagged forest. It checks the declared target's entire exact report
after rechecking each current read, actual compiler and ordered child. A
C337-only record branch does not get silently converted into literal heads. -/
def decode (p : Problem) (wire : Code) (report : Report) : Option (Accepted p report) :=
  match compiled : compile p.source with
  | none => none
  | some table => do
    let ownership ← attach p.current p.origins
    let g : Global p := ⟨table,compiled,ownership⟩
    let found ← tree g [] p.target wire
    if ok : agrees (GeneralDeclarativeWitnessMixedWhole352.goal p p.target) found.tree report = true then
      pure ⟨g,found,ok⟩
    else none

def check (p : Problem) (wire : Code) (report : Report) : Bool :=
  (decode p wire report).isSome

theorem semantic_conclusion {p : Problem} {wire : Code} {report : Report} (accepted : check p wire report = true) :
    ∃ (a : Accepted p report) (d : Dictionary), report.tree = a.replayed.tree ∧
      report.result = .selected d ∧ report.outputs = p.target.outputs ∧
      ∀ m : Assignment, Models p.current m →
        Evidence (registry a.global.table) (interpretation a.global.table.snapshot) m p.target d := by
  unfold check at accepted
  cases ran : decode p wire report with
  | none => simp [ran] at accepted
  | some a =>
    have eq := exact_report a.agreement
    exact ⟨a,a.replayed.dictionary,eq.1,eq.2.1.trans a.replayed.written,eq.2.2,a.replayed.truth⟩

end Yulang.GeneralDeclarativeWitnessTagCoreForest352
