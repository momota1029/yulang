import Yulang.GeneralDeclarativeWitnessAssociatedDescriptor359
import Yulang.GeneralDeclarativeWitnessNestedDescent360
import Yulang.GeneralDeclarativeWitnessCompiler350

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessNativePreparation360
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey Frame)
open GeneralDeclarativeWitnessCompiler350 (Context preparation whereBatch portNames placed)
open GeneralDeclarativeWitnessLiteral349 (preserves preserves_iff)
open GeneralDeclarativeWitnessModeCoverage357 (checkDecl)
open GeneralDeclarativeWitnessCovariantDescent353 (legal)
open GeneralDeclarativeWitnessProblem349 (declared)
open GeneralDeclarations (Declaration Clause)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeEntailment320 (appendFacts Holds model_append)
open GeneralDeclarativeGrowth327 (restrict)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralNominalCommonBridge (Assignment)

def shape (s : GeneralSourceMetadataBundle291.SourceBundle) (d : Declaration) : Bool :=
  legal s d || GeneralDeclarativeWitnessNestedDescent360.check s d

structure Layout where
  named : State
  spans : List (Nat × Capture)
  keep : List Nat
  fallback : Nat → Capture
  targets : Clause → Nat → Nat

def context (e : Environment) (d : Demand) (impl : Declaration) (l : Layout) : Context :=
  ⟨registry e.source,interpretation e.source.snapshot,d,impl,l.named,l.spans,l.keep,l.fallback,l.targets⟩

/-- A replay of the actual preparation/ordinary-where compiler for a
source-addressed body. This is conditional on independently supplied
captures; it does not elect an implementation or claim a typed output. -/
structure Prepared (e : Environment) (frame : FrameKey) (d : Demand) (l : Layout) where
  impl : Declaration
  identity : impl.id = frame.declaration ∧ impl.role = d.role
  authored : e.source.declarations[frame.sourceOrdinal]? = some impl
  sourceChecked : checkDecl e impl = true
  shapeChecked : shape e.source impl = true
  requestChecked : declared e.source d = true
  before : State
  ports : List GeneralDeclarativeClauseBatch327.Port
  ranPrepare : preparation (context e d impl l) = some (before,ports)
  whereRows : List Equation
  ranWhere : whereBatch (context e d impl l) ports = some whereRows
  retained : preserves l.named (appendFacts before whereRows) = true

def Prepared.stage {e f d l} (p : Prepared e f d l) : State := appendFacts p.before p.whereRows

def Prepared.kids {e f d l} (p : Prepared e f d l) : List Demand :=
  children p.impl (portNames (context e d p.impl l) p.ports) (placed (context e d p.impl l) p.ports)

def Prepared.captures {e f d l} (p : Prepared e f d l) : Frame :=
  ⟨f,p.impl.inputNames.map fun n => (n,(portNames (context e d p.impl l) p.ports).input n)⟩

def prepare (e : Environment) (f : FrameKey) (d : Demand) (l : Layout) : Option (Prepared e f d l) :=
  match source : e.source.declarations[f.sourceOrdinal]? with
  | none => none
  | some impl =>
    if identity : impl.id = f.declaration ∧ impl.role = d.role then
      if sourceOK : checkDecl e impl = true then
        if legalOK : shape e.source impl = true then
          if requestOK : declared e.source d = true then
            let ctx := context e d impl l
            match ranPrepare : preparation ctx with
            | none => none
            | some (before,ports) =>
              match ranWhere : whereBatch ctx ports with
              | none => none
              | some rows =>
                if keeps : preserves l.named (appendFacts before rows) = true then
                  some ⟨impl,identity,source,sourceOK,legalOK,requestOK,before,ports,ranPrepare,rows,ranWhere,keeps⟩
                else none
          else none
        else none
      else none
    else none

theorem from_actual_compiler {e f d l} (p : Prepared e f d l) :
    preparation (context e d p.impl l) = some (p.before,p.ports) ∧
    whereBatch (context e d p.impl l) p.ports = some p.whereRows ∧
    p.kids = children p.impl (portNames (context e d p.impl l) p.ports) (placed (context e d p.impl l) p.ports) :=
  ⟨p.ranPrepare,p.ranWhere,rfl⟩

theorem same_model_of_prepared {e f d l} (p : Prepared e f d l) (m : Assignment)
    (fit : Models p.stage m) : Models l.named m ∧ ∀ row ∈ p.whereRows,Holds m row :=
  ⟨restrict ((preserves_iff ..).mp p.retained) m fit,((model_append m).mp fit).2⟩

theorem actual_source_requirement_smaller {e f d l} (p : Prepared e f d l) :
    ∀ clause ∈ p.impl.requirements,
      GeneralDeclarationPatterns.StableSmaller p.impl.head clause.arguments := by
  intro clause actual
  rcases GeneralDeclarativeWitnessProblem349.splitOr p.shapeChecked with old|new
  · unfold legal at old
    have checked := GeneralDeclarativeWitnessProblem349.splitAnd
      (GeneralDeclarativeWitnessProblem349.splitAnd (GeneralDeclarativeWitnessProblem349.splitAnd old).2).2
    exact (GeneralDeclarativeWitnessCovariantDescent353.descent_sound (List.all_eq_true.mp checked.2 _ actual)).2
  · exact GeneralDeclarativeWitnessNestedDescent360.checked_descent new clause actual

end Yulang.GeneralDeclarativeWitnessNativePreparation360
