import Yulang.GeneralDeclarativeI65I72FixedGoal402

namespace Yulang.GeneralDeclarativeI65.I72
open CommonNominalFullCarrier (Equivalent)
open CommonDeclaredNominalInspection (Kind)
open GeneralDictionaryAssociatedProvenance (Body)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDeclarationPatterns (normalize)

/-- One typed equality at an existing output address. The full original
request, declaration/body frame, output index, atlas expression and
kinded named RHS remain linked by their source indices. No fitting
model, output equivalence, or completion is supplied in this data. -/
structure RetainedEquation (s : State) where
  request : Request
  frame : AuthoredBodyFrame393 s.core request
  outputOrdinal : Fin request.demand.outputs.length
  output : NamedMixedOutput401 s.b6 frame outputOrdinal

namespace RetainedEquation

def occurrence {s} (e : RetainedEquation s) : List Nat := e.request.occurrence
def declarationOrdinal {s} (e : RetainedEquation s) : Nat := e.frame.ordinal
def body {s} (e : RetainedEquation s) : Body := e.output.body
def target {s} (e : RetainedEquation s) : Nat := e.request.demand.outputs[e.outputOrdinal].target

/-- An associated output itself is a value type. Every nested argument
keeps its kind in the dependent RHS, including row-valued arguments. -/
def kind {s} (_ : RetainedEquation s) : Kind := .value

def rhs {s} (e : RetainedEquation s) :
    NamedMixedTree401 s.core (e.frame.slots e.body) false (normalize (bodyPattern e.body)) :=
  e.output.rhs

def Means {s} (e : RetainedEquation s) (m : Model) : Prop :=
  ∃ ty, e.output.receipt.actualEquation m = some (e.target,ty) ∧
    Equivalent (m.assignment e.target).1 ty

end RetainedEquation

/-- Old constraints unchanged, together with a list of exact typed
equalities. A row cannot replace an old equation or relocate itself. -/
structure FullState where
  base : State
  retained : List (RetainedEquation base)

def FitsFull (s : FullState) (m : Model) : Prop :=
  Fits s.base m ∧ ∀ e ∈ s.retained, e.Means m

def liftState (s : State) : FullState := ⟨s,[]⟩

theorem fits_iff_fitsFull_liftState (s : State) (m : Model) :
    Fits s m ↔ FitsFull (liftState s) m := by
  refine ⟨fun fit => ⟨fit, ?_⟩, fun fit => fit.1⟩
  intro e h
  exact (List.not_mem_nil h).elim

end Yulang.GeneralDeclarativeI65.I72
