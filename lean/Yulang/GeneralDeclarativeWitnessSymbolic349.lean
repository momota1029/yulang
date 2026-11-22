import Yulang.GeneralDeclarativeWitnessPointReplay349
import Yulang.GeneralDeclarativeWitnessLiteral349
import Yulang.GeneralDeclarativeObservedBody347

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessSymbolic349
open GeneralDeclarativeWitnessPointInput349 (PointProblem lit)
open GeneralDeclarativeWitnessPointReplay349 (Accepted runBody)
open GeneralDeclarativeWitnessTree349 (Report)
open GeneralDeclarativeWitnessLiteral349 (sameRows rows_exact)
open GeneralDeclarativeHead320 (Equation Models)
open GeneralDeclarativeEntailment320 (appendFacts Holds model_append)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDeclarativeFrameReadback325 (sourceNames)
open GeneralDeclarativeClausePlacement327 (placement)
open GeneralDeclarativeBatch320 (collect)
open GeneralSourceMetadataBundle291 (SourceBundle registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarations (Declaration)
open GeneralNominalCommonBridge (Assignment)

def outputRows (p : PointProblem) (s : SourceBundle) (impl : Declaration) : Option (List Equation) :=
  let names := sourceNames impl (placement [] [] (fun _ _ => 0)) (fun _ => lit p)
  collect (one (registry s) (interpretation s.snapshot) impl p.problem.demand names.input) p.problem.demand.outputs

theorem actual_readback {p : PointProblem} {report : Report} (a : Accepted p report) :
    ∃ rows, outputRows p a.table a.impl = some rows ∧ a.ordin = appendFacts p.problem.state rows := by
  have noWhere := List.isEmpty_iff.mp a.noWhere
  have facts := a.compiled
  unfold runBody compileBody at facts
  rw [noWhere] at facts
  have merge : GeneralDeclarativeStableAssemble329.merged p.problem.state [] [] (fun _ => lit p) =
      ⟨p.problem.state,fun _ => lit p⟩ := by
    cases p with
    | mk q atName kind =>
      cases q with
      | mk source state demand =>
        cases state
        simp only [GeneralDeclarativeStableAssemble329.merged,GeneralDeclarativeOpaqueShared328.build,
          List.map_nil, GeneralDeclarativeStableAssemble329.tieState, GeneralDeclarativeStableTies329.rows,
          List.filter_nil,appendFacts,List.append_nil]
  rw [merge] at facts
  simp only [GeneralDeclarativeClauseBatch327.prepare,GeneralDeclarativeWhereOutputBatch327.whole,
    GeneralDeclarativeEmissionForest322.children,noWhere,List.map_nil,collect] at facts
  change (do
    let rows ← outputRows p a.table a.impl
    pure (appendFacts (appendFacts p.problem.state []) rows,[])) = some (a.ordin,[]) at facts
  cases out : outputRows p a.table a.impl with
  | none =>
    rw [out] at facts
    cases facts
  | some rows =>
    rw [out] at facts
    have eq : (appendFacts (appendFacts p.problem.state []) rows,[]) = (a.ordin,[]) :=
      Option.some.inj facts
    refine ⟨rows,?_,?_⟩
    · rfl
    · simpa only [appendFacts,List.append_nil] using (congrArg Prod.fst eq).symm

structure SymbolicReport where
  core : Report
  outputEquations : List Equation

def check (p : PointProblem) (w : SymbolicReport) : Bool :=
  (do
    let a ← GeneralDeclarativeWitnessPointReplay349.decode p w.core
    let rows ← outputRows p a.table a.impl
    some (sameRows rows w.outputEquations : Bool) : Option Bool).getD false

theorem exact_writes {p : PointProblem} {w : SymbolicReport} (ok : check p w = true) :
    ∃ a : Accepted p w.core, outputRows p a.table a.impl = some w.outputEquations ∧
      w.outputEquations.map Equation.left = p.problem.demand.outputs.map GeneralSourceState.Output.target ∧
      (∀ m : Assignment, Models p.problem.state m →
        ∀ e ∈ w.outputEquations,Holds m e) := by
  unfold check at ok
  cases q : GeneralDeclarativeWitnessPointReplay349.decode p w.core with
  | none => simp [q] at ok
  | some a =>
    obtain ⟨rows,code,ordinary⟩ := actual_readback a
    rw [q] at ok
    change ((do let rows ← outputRows p a.table a.impl; some (sameRows rows w.outputEquations) : Option Bool).getD false) = true at ok
    rw [code] at ok
    have eq := (rows_exact _ _).mp ok
    rw [eq]
    refine ⟨a,code,GeneralDeclarativeObservedBody347.target_order code,?_⟩
    intro m actual
    have fit := GeneralDeclarativeCurrentReceipt330.relays_models
      (GeneralDeclarativeWitnessGround349.receipt a.kept) m actual
    rw [ordinary] at fit
    exact ((model_append m).mp fit).2

end Yulang.GeneralDeclarativeWitnessSymbolic349
