import Yulang.GeneralDeclarativeWitnessAllocation350
import Yulang.GeneralDeclarativeObservedBody347

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCompiler350
open GeneralDeclarations (Registry Declaration Clause)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralNominalInspection (Interpretation)
open GeneralSourceState (Output)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarativeWitnessLiteral349 (sameRows rows_exact)
open GeneralDeclarativeWitnessReceipt349 (Plan verify same_model)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralDeclarativeCurrentReceipt330 (Receipt)
open GeneralDeclarativeStableAssemble329 (merged)
open GeneralDeclarativeClauseBatch327 (prepare)
open GeneralDeclarativeClausePlacement327 (placement)
open GeneralDeclarativeAppliedClause327 (targetsOnly)
open GeneralDeclarativeFrameReadback325 (sourceNames)
open GeneralDeclarativeWhereOutputBatch327 (whole)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeEntailment320 (appendFacts Holds model_append)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralNominalCommonBridge (Assignment)

abbrev DemandCode := Nat × List (Nat × Nat × Nat) × List (Nat × Nat)

def trip (c : Capture) : Nat × Nat × Nat := (c.lower,c.center,c.upper)
def pair (o : Output) : Nat × Nat := (o.name,o.target)
def printDemand (d : Demand) : DemandCode := (d.role,d.arguments.map trip,d.outputs.map pair)

theorem trip_injective {a b : Capture} (h : trip a = trip b) : a = b := by
  cases a; cases b
  simp [trip,Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl,rfl⟩
  rfl

theorem pair_injective {a b : Output} (h : pair a = pair b) : a = b := by
  cases a; cases b
  simp [pair,Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl⟩
  rfl

theorem map_injective {A B : Type} {f : A → B}
    (one : ∀ {x y}, f x = f y → x = y) {xs ys : List A}
    (h : xs.map f = ys.map f) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> cases h <;> rfl
  | cons head rest ih =>
    cases ys with
    | nil => cases h
    | cons y ys =>
      obtain ⟨part,tail⟩ := List.cons.inj h
      cases one part
      cases ih tail
      rfl

theorem print_injective {a b : Demand} (h : printDemand a = printDemand b) : a = b := by
  cases a; cases b
  simp [printDemand,Prod.mk.injEq] at h
  obtain ⟨rfl,args,outs⟩ := h
  cases map_injective (fun h => trip_injective h) args
  cases map_injective (fun h => pair_injective h) outs
  rfl

structure Context where
  registry : Registry
  interp : Interpretation
  demand : Demand
  decl : Declaration
  named : State
  spans : List (Nat × Capture)
  keep : List Nat
  fallback : Nat → Capture
  targets : Clause → Nat → Nat

structure Finished where
  beforeOutputs : State
  fixed : List Equation
  kids : List Demand

def Finished.state (f : Finished) : State := appendFacts f.beforeOutputs f.fixed

def initial (c : Context) := merged c.named c.keep c.spans c.fallback
def preparation (c : Context) : Option (State × List GeneralDeclarativeClauseBatch327.Port) :=
  prepare c.registry.constructors c.interp (stateNames (initial c).state ++ c.keep)
    (sourceNames c.decl (targetsOnly c.targets) (initial c).captures).input
    (initial c).state c.decl.requirements
def portNames (c : Context) (ports : List GeneralDeclarativeClauseBatch327.Port) :=
  sourceNames c.decl (placement c.decl.requirements ports c.targets) (initial c).captures
def placed (c : Context) (ports : List GeneralDeclarativeClauseBatch327.Port) :=
  placement c.decl.requirements ports c.targets
def whereBatch (c : Context) (ports : List GeneralDeclarativeClauseBatch327.Port) :=
  whole c.registry c.interp c.decl (portNames c ports) c.targets
def fixedBatch (c : Context) (ports : List GeneralDeclarativeClauseBatch327.Port) :=
  collect (one c.registry c.interp c.decl c.demand (portNames c ports).input) c.demand.outputs

/-- This reruns the actual compiler, retaining the exact final write
batch instead of trying to infer it from equalities in the current state. -/
def execute (c : Context) : Option Finished := do
  let (prepared,ports) ← preparation c
  let whereRows ← whereBatch c ports
  let rootRows ← fixedBatch c ports
  pure ⟨appendFacts prepared whereRows,rootRows,children c.decl (portNames c ports) (placed c ports)⟩

theorem compiled (c : Context) :
    compileBody c.registry c.interp c.demand c.decl c.named c.spans c.keep c.fallback c.targets =
      (execute c).map (fun f => (f.state,f.kids)) := by
  change (do
    let (prepared,ports) ← preparation c
    let whereRows ← whereBatch c ports
    let rootRows ← fixedBatch c ports
    pure (appendFacts (appendFacts prepared whereRows) rootRows,
      children c.decl (portNames c ports) (placed c ports))) = _
  unfold execute
  cases prep : preparation c with
  | none => simp
  | some data =>
    rcases data with ⟨s,ports⟩
    cases ws : whereBatch c ports <;> cases rs : fixedBatch c ports <;> simp [ws,rs,Finished.state]

theorem fixed_targets {c : Context} {f : Finished} (e : execute c = some f) :
    f.fixed.map Equation.left = c.demand.outputs.map Output.target := by
  unfold execute at e
  cases prep : preparation c with
  | none => simp [prep] at e
  | some data =>
    rcases data with ⟨s,ports⟩
    cases ws : whereBatch c ports with
    | none => simp [prep,ws] at e
    | some whereRows =>
      cases rs : fixedBatch c ports with
      | none => simp [prep,ws,rs] at e
      | some rows =>
        have same : (⟨appendFacts s whereRows,rows,children c.decl (portNames c ports)
          (placed c ports)⟩ : Finished) = f := by simpa [prep,ws,rs] using e
        cases same
        exact GeneralDeclarativeObservedBody347.target_order rs

structure Wire where
  children : List DemandCode
  outputRows : List Equation
  receipt : Plan

structure Accepted (c : Context) (s : State) (w : Wire) where
  compiled : Finished
  run : execute c = some compiled
  kept : verify compiled.state s w.receipt = true
  printed : w.children = compiled.kids.map printDemand
  fixed : w.outputRows = compiled.fixed

def decode (c : Context) (s : State) (w : Wire) : Option (Accepted c s w) :=
  match ran : execute c with
  | none => none
  | some f =>
    if fit : verify f.state s w.receipt = true then
      if kids : w.children = f.kids.map printDemand then
        if rows : sameRows f.fixed w.outputRows = true then
          some ⟨f,ran,fit,kids,(rows_exact _ _).mp rows⟩
        else none
      else none
    else none

theorem actual {c : Context} {s : State} {w : Wire} (a : Accepted c s w) :
    compileBody c.registry c.interp c.demand c.decl c.named c.spans c.keep c.fallback c.targets =
      some (a.compiled.state,a.compiled.kids) := by
  rw [compiled,a.run]
  rfl

theorem retained {c : Context} {s : State} {w : Wire} (a : Accepted c s w) :
    Receipt a.compiled.state s :=
  GeneralDeclarativeWitnessReceipt349.sound a.kept

theorem fixed_in_current {c : Context} {s : State} {w : Wire} (a : Accepted c s w)
    (m : Assignment) (fit : Models s m) :
    w.outputRows.map Equation.left = c.demand.outputs.map Output.target ∧
    ∀ e ∈ w.outputRows,Holds m e := by
  rw [a.fixed]
  exact ⟨fixed_targets a.run,((model_append m).mp (same_model a.kept m fit)).2⟩

theorem exact_children {c : Context} {s : State} {w : Wire} (a : Accepted c s w)
    {ks : List Demand} (claims : w.children = ks.map printDemand) :
    ks = a.compiled.kids :=
  map_injective (fun h => print_injective h) (claims.symm.trans a.printed)

end Yulang.GeneralDeclarativeWitnessCompiler350
