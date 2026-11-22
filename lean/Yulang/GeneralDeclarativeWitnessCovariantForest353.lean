import Yulang.GeneralDeclarativeWitnessCovariantSubtree353
import Yulang.GeneralDeclarativeWitnessCovariantViews353

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCovariantForest353
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem ModelsAt Valuation)
open GeneralDeclarativeWitnessCovariantCompiler353 (Checked confirmed retained)
open GeneralDeclarativeWitnessCovariantSubtree353 (Child ordinarySource problem decodeAt)
open GeneralDeclarativeWitnessForest350 (Layout Fixed)
open GeneralDeclarativeWitnessMixedForest352 (Code)
open GeneralDeclarativeWitnessTree349 (Report agrees exact_report)
open GeneralDeclarativeExactDictionary337 (Evidence)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeWitnessOrigins350 (Table)
open GeneralSourceMetadataBareBundle291 (compile)
open GeneralSourceMetadataBundle291 (SourceBundle registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂ Tree Dictionary Result classification classifications classification_exact classifications_exact)

structure Environment (p : Problem) where
  origins : Table
  layout : List Nat → Demand → Layout

structure ChildWire where
  tree : Code
  report : Report

structure BoxChild (p : Problem) (e : Environment p) (s : State) (idx : Nat) (d : Demand) where
  out : Report
  accepted : Child (problem p s d e.origins e.layout) idx d out
  dictionary : Dictionary
  selected : out.result = .selected dictionary

inductive Children (p : Problem) (e : Environment p) (s : State) : Nat → List Demand → Type where
  | nil : Children p e s i []
  | cons : BoxChild p e s i d → Children p e s (i+1) ds → Children p e s i (d::ds)

def readChildren (p : Problem) (e : Environment p) (s : State) (idx : Nat) :
    (ds : List Demand) → List ChildWire → Option (Children p e s idx ds)
  | [],[] => some .nil
  | d::ds,w::ws => do
    if d.role = p.demand.role then none
    else
      let node ← decodeAt (problem p s d e.origins e.layout) idx d w.tree w.report
      match printed : w.report.result with
      | .selected choice =>
        let tail ← readChildren p e s (idx+1) ds ws
        pure (.cons ⟨w.report,node,choice,printed⟩ tail)
      | _ => none
  | _,_ => none

def Children.trees {p e s i ds} : Children p e s i ds → List Tree
  | .nil => []
  | .cons head tail => head.accepted.actual.diagnostic.tree :: tail.trees

def Children.entries {p e s i ds} : Children p e s i ds → List Dictionary
  | .nil => []
  | .cons head tail => head.dictionary :: tail.entries

theorem Children.agree {p e s i ds} (v : Children p e s i ds) :
    classifications v.trees = v.entries.map Result.selected := by
  induction v with
  | nil => rfl
  | cons head tail ih =>
    have eq := (exact_report head.accepted.actual.exactResult).2.1
    have ok := eq.symm.trans head.selected
    simp only [Children.trees,Children.entries,classifications,ok,List.map_cons,ih]

theorem Children.same_model {p e s i ds} (v : Children p e s i ds) {table : SourceBundle}
    (prepared : compile (ordinarySource p) = some table) (m : Assignment) (fit : Models s m) :
    All₂ (Evidence (registry table) (interpretation table.snapshot) m) ds v.entries := by
  induction v with
  | nil => exact .nil
  | cons head tail ih =>
    have safe := (GeneralDeclarativeWitnessMixedWhole352.selected head.accepted.actual head.selected m fit).1
    have same := Option.some.inj (head.accepted.actual.global.canonical.symm.trans prepared)
    rw [same] at safe
    exact .cons safe ih

structure Wire where
  head : GeneralDeclarativeWitnessCovariantOrigin353.Wire
  rootOut : GeneralDeclarativeWitnessCompiler350.Wire
  children : List ChildWire

structure Accepted (p : Problem) (e : Environment p) (s : State) (w : Wire) (report : Report) where
  head : Checked p w.head s w.rootOut
  ordinary : SourceBundle
  actual : compile (ordinarySource p) = some ordinary
  children : Children p e s 0 head.receipt.compiled.kids
  exact : agrees ⟨p.metadata.sourceInput,s,p.demand⟩ (.selected head.prepared.decl.id children.trees) report = true

def decode (p : Problem) (e : Environment p) (s : State) (w : Wire) (report : Report) :
    Option (Accepted p e s w report) := do
  let h ← GeneralDeclarativeWitnessCovariantCompiler353.check p w.head s w.rootOut
  match source : compile (ordinarySource p) with
  | none => none
  | some table => do
    let cs ← readChildren p e s 0 h.receipt.compiled.kids w.children
    if exact : agrees ⟨p.metadata.sourceInput,s,p.demand⟩ (.selected h.prepared.decl.id cs.trees) report = true then
      pure ⟨h,table,source,cs,exact⟩
    else none

theorem well_formed {p e s w report} (a : Accepted p e s w report) (m : Assignment) (fit : Models s m) :
    report.tree = .selected a.head.prepared.decl.id a.children.trees ∧
    report.result = .selected (.node a.head.prepared.decl.id a.children.entries) ∧
    report.outputs = p.demand.outputs ∧
    All₂ (Evidence (registry a.ordinary) (interpretation a.ordinary.snapshot) m)
      a.head.receipt.compiled.kids a.children.entries ∧
    w.rootOut.outputRows.map Equation.left = p.demand.outputs.map GeneralSourceState.Output.target ∧
    (∀ e ∈ w.rootOut.outputRows,Holds m e) := by
  have eq := exact_report a.exact
  have printed : classification (.selected a.head.prepared.decl.id a.children.trees) =
      .selected (.node a.head.prepared.decl.id a.children.entries) :=
    (classification_exact ..).mpr (.selected ((classifications_exact ..).mp a.children.agree) (.selected rfl))
  exact ⟨eq.1,eq.2.1.trans printed,eq.2.2,a.children.same_model a.actual m fit,
    (confirmed a.head m fit).2.2⟩

end Yulang.GeneralDeclarativeWitnessCovariantForest353
