import Yulang.GeneralDeclarativeWitnessSpineEdgeMeaning355
import Yulang.GeneralDeclarativeWitnessCovariantSubtree353
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessMixedScope356
open GeneralDeclarativeWitnessCovariantOrigin353 (Problem)
open GeneralSourceMetadataBareBundle291 (InputBundle compile preserves_input)
open GeneralSourceMetadataBundle291 (SourceBundle registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeWitnessMixedForest352 (Problem Global Code replayTree)
open GeneralDeclarativeWitnessMixedWhole352 (Accepted goal selected)
open GeneralDeclarativeWitnessOrigins350 (Table attach)
open GeneralDeclarativeWitnessForest350 (Layout Fixed)
open GeneralDeclarativeWitnessTree349 (Report agrees exact_report)
open GeneralDeclarativeWitnessTagHeader352 (replay)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (Dictionary Tree)
open GeneralDeclarativeEntailment320 (Holds)

def filtered (input : InputBundle) (typedRoles : List Nat) : InputBundle :=
  {input with declarations := input.declarations.filter (fun d => !typedRoles.contains d.role)}

theorem keep_exact (source : InputBundle) (typedRoles : List Nat) (d : Declaration) :
    d ∈ (filtered source typedRoles).declarations ↔ d ∈ source.declarations ∧ d.role ∉ typedRoles := by
  simp [filtered]

theorem metadata_unchanged (source : InputBundle) (typedRoles : List Nat) :
    (filtered source typedRoles).declared = source.declared ∧
    (filtered source typedRoles).snapshot = source.snapshot ∧
    (filtered source typedRoles).roles = source.roles :=
  ⟨rfl,rfl,rfl⟩

structure Scope where
  typedRoles : List Nat
  origins : Table
  layout : List Nat → Demand → Layout

def problem (e : Scope) (source : InputBundle) (s : State) (d : Demand) :
    GeneralDeclarativeWitnessMixedForest352.Problem :=
  ⟨filtered source e.typedRoles,s,e.origins,d,e.layout⟩

structure Ordinary (e : Scope) (source : InputBundle) (s : State) (path : List Nat)
    (d : Demand) (report : Report) where
  allowed : d.role ∉ e.typedRoles
  actual : Accepted (problem e source s d) d report
  dictionary : Dictionary
  exactDict : report.result = .selected dictionary
  paths : actual.diagnostic.fixed.map Fixed.path =
    GeneralDeclarativeWitnessPathOrder352.preorder path actual.diagnostic.tree
  doesNotReturnToTyped : ∀ f ∈ actual.diagnostic.fixed,f.demand.role ∉ e.typedRoles

/-- The branch is rerun at its actual absolute compiler position. It
does not take constructor mode, role table, or declarations from a
report, and cannot accidentally return to an excluded typed role. -/
def ordinary (e : Scope) (source : InputBundle) (s : State) (path : List Nat)
    (d : Demand) (w : Code) (out : Report) : Option (Ordinary e source s path d out) :=
  let p := problem e source s d
  if allowed : d.role ∉ e.typedRoles then
    match compiled : compile p.source with
    | none => none
    | some table => do
      let live ← attach s e.origins
      let g : Global p := ⟨table,compiled,live⟩
      match ran : replayTree g path d w with
      | none => none
      | some found =>
        match register : replay (goal p d) ⟨out.outputs⟩ with
        | none => none
        | some header =>
          if safe : found.fixed.all (fun f => !e.typedRoles.contains f.demand.role) = true then
            if exact : agrees (goal p d) found.tree out = true then
              match ok : out.result with
              | .selected result => some ⟨allowed,⟨g,found,header,register,exact⟩,result,ok,
                GeneralDeclarativeWitnessPathOrder352.exact_tree w ran,fun f h => by
                  simpa using List.all_eq_true.mp safe f h⟩
              | _ => none
            else none
          else none
  else none

theorem ordinary_same_model {e source s path d report} (a : Ordinary e source s path d report)
    (m : Assignment) (fit : Models s m) :
    GeneralDeclarativeExactDictionary337.Evidence
      (registry a.actual.global.table) (interpretation a.actual.global.table.snapshot) m d a.dictionary ∧
    (∀ f ∈ a.actual.diagnostic.fixed,f.equations.map Equation.left =
      f.demand.outputs.map GeneralSourceState.Output.target ∧ ∀ q ∈ f.equations,Holds m q) ∧
    report.outputs = d.outputs ∧
    a.actual.diagnostic.fixed.map Fixed.path = GeneralDeclarativeWitnessPathOrder352.preorder path report.tree :=
  let good := selected a.actual a.exactDict m fit
  let reported := exact_report a.actual.exactResult
  ⟨good.1,good.2,reported.2.2,reported.1.symm ▸ a.paths⟩

end Yulang.GeneralDeclarativeWitnessMixedScope356
