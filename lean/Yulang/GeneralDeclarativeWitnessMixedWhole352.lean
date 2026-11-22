import Yulang.GeneralDeclarativeWitnessMixedSound352

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessMixedWhole352
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessOrigins350 (attach)
open GeneralDeclarativeWitnessTree349 (Report agrees exact_report classifies)
open GeneralDeclarativeWitnessTagHeader352 (replay replay_sound)

open GeneralDeclarativeWitnessMixedForest352 (Problem Global Code Replayed Rule replayTree)
open GeneralDeclarativeWitnessForest350 (Fixed)
open GeneralDeclarativeWitnessTagBranch352 (same_table)
open GeneralSourceMetadataBareBundle291 (compile)
open GeneralSourceMetadataBundle291 (SourceBundle registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeWitnessMixedSound352 (dictionary_sound)
open GeneralDeclarativeExactDictionary337 (Evidence)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Classify Result Dictionary)

def goal (p : Problem) (root : Demand) : GeneralDeclarativeWitnessProblem349.Problem := ⟨p.source,p.current,root⟩

structure Accepted (p : Problem) (root : Demand) (report : Report) where
  global : Global p
  diagnostic : Replayed global root
  table : SourceBundle
  header : replay (goal p root) ⟨report.outputs⟩ = some table
  exactResult : agrees (goal p root) diagnostic.tree report = true

/-- Check a finite recursive witness against the real positive rules.
The diagnostic tree, child order and all fixed write receipts are
computed independently of the solver's reported output. -/
def decode (p : Problem) (root : Demand) (w : Code) (report : Report) :
    Option (Accepted p root report) :=
  match compiled : compile p.source with
  | none => none
  | some source => do
    let a ← attach p.current p.origins
    let g : Global p := ⟨source,compiled,a⟩
    let observed ← replayTree g [] root w
    match header : replay (goal p root) ⟨report.outputs⟩ with
    | none => none
    | some table =>
      if ok : agrees (goal p root) observed.tree report = true then
        some ⟨g,observed,table,header,ok⟩
      else none

def check (p : Problem) (root : Demand) (w : Code) (report : Report) : Bool :=
  (decode p root w report).isSome

theorem checked {p : Problem} {root : Demand} {w : Code} {report : Report}
    (ok : check p root w report = true) : Nonempty (Accepted p root report) := by
  unfold check at ok
  cases found : decode p root w report with
  | none => simp [found] at ok
  | some a => exact ⟨a⟩

theorem agreed {p : Problem} {root : Demand} {report : Report} (a : Accepted p root report) :
    report.tree = a.diagnostic.tree ∧ report.outputs = root.outputs ∧
      Classify (Rule a.global a.diagnostic.sidecar) root report.result ∧
      ∀ f ∈ a.diagnostic.fixed, Fixed.Meaning f p.current := by
  have matchOut := exact_report a.exactResult
  exact ⟨matchOut.1,matchOut.2.2,classifies (GeneralDeclarativeWitnessMixedForest352.resolves a.diagnostic)
    a.exactResult,a.diagnostic.fixedMeaning⟩

/-- On every model of the same fixed current state, the checked result
entails the returned dictionary and every recorded fixed output.
No proof of old-solver reachability or universal certificate coverage
is assumed or asserted. -/
theorem selected {p : Problem} {root : Demand} {report : Report} (a : Accepted p root report)
    {d : Dictionary} (result : report.result = .selected d)
    (m : Assignment) (fit : Models p.current m) :
    Evidence (registry a.global.table) (interpretation a.global.table.snapshot) m root d ∧
      ∀ f ∈ a.diagnostic.fixed, f.equations.map GeneralDeclarativeHead320.Equation.left =
        f.demand.outputs.map GeneralSourceState.Output.target ∧
        ∀ e ∈ f.equations,GeneralDeclarativeEntailment320.Holds m e := by
  obtain ⟨_,_,classifiesHere,writes⟩ := agreed a
  rw [result] at classifiesHere
  obtain ⟨_,well,coverage,declared,_⟩ := replay_sound a.header
  have same : a.table = a.global.table := same_table a.header a.global.canonical
  rw [same] at well coverage declared
  refine ⟨dictionary_sound well coverage declared classifiesHere
    (GeneralDeclarativeWitnessMixedForest352.models a.diagnostic m fit),?_⟩
  intro f found
  have meaning := writes f found
  exact ⟨meaning.1,meaning.2 m fit⟩

end Yulang.GeneralDeclarativeWitnessMixedWhole352
