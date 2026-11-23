import Yulang.GeneralDeclarativeWitnessModeCoverage357
import Yulang.GeneralDeclarativeHead320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessPointModes357
open GeneralDeclarativeWitnessConstructorModes357 (Environment Use Mode readUse)
open GeneralDeclarativeHead320 (State Models)
open GeneralNominalCommonBridge (Assignment)
open CommonDeclaredNominalInspection (Parameter directions inspectArgument inspectArguments)
open CommonDeclaredNominalVariance (Variance)
open CommonNominalConstraints (ArgumentTerm)
open PresenceNormalForm (Atom All)
open Core.PresenceGeneration (TyTerm RowTerm)

def relation (le : α → α → Prop) : Variance → α → α → Prop
  | .covariant,f,g => le f g
  | .contravariant,f,g => le g f
  | .invariant,f,g => le f g ∧ le g f
  | .unused,_,_ => True

def position (m : Assignment) (p : Parameter) : ArgumentTerm Nat → ArgumentTerm Nat → Prop
  | .value f,.value g => p.kind = .value ∧
      relation CommonNominalFullCarrier.Subtype p.variance
        (f.eval CommonNominalFullCarrier.model m) (g.eval CommonNominalFullCarrier.model m)
  | .row f,.row g => p.kind = .row ∧
      relation Common.rowLe p.variance
        (f.eval CommonNominalFullCarrier.model m) (g.eval CommonNominalFullCarrier.model m)
  | _,_ => False

def positions (m : Assignment) : List Parameter → List (ArgumentTerm Nat) → List (ArgumentTerm Nat) → Prop
  | [],[],[] => True
  | p::ps,f::fs,g::gs => position m p f g ∧ positions m ps fs gs
  | _,_,_ => False

def satisfied (m : Assignment) (code : Option (List (Atom Nat))) : Prop :=
  ∃ atoms,code = some atoms ∧ All CommonNominalFullCarrier.model m atoms

theorem position_exact (m : Assignment) (p : Parameter) (lhs rhs : ArgumentTerm Nat) :
    satisfied m (inspectArgument p lhs rhs) ↔ position m p lhs rhs := by
  rcases p with ⟨kind,mode⟩
  cases kind <;> cases mode <;> cases lhs <;> cases rhs <;>
    simp [satisfied,inspectArgument,CommonDeclaredNominalInspection.termKind,directions,position,relation,
      All,Atom.Holds,CommonNominalFullCarrier.model]

theorem for_append (m : Assignment) (f g : Option (List (Atom Nat))) :
    satisfied m (CommonNominalConstraints.append f g) ↔ satisfied m f ∧ satisfied m g := by
  cases f <;> cases g <;> simp [satisfied,CommonNominalConstraints.append,PresenceNormalForm.all_append]

theorem arguments_exact (m : Assignment) (ps : List Parameter) (xs ys : List (ArgumentTerm Nat)) :
    satisfied m (inspectArguments ps xs ys) ↔ positions m ps xs ys := by
  induction ps generalizing xs ys with
  | nil => cases xs <;> cases ys <;> simp [inspectArguments,positions,satisfied,All]
  | cons p ps ih =>
    cases xs with
    | nil => cases ys <;> simp [inspectArguments,positions,satisfied]
    | cons f fs =>
      cases ys with
      | nil => simp [inspectArguments,positions,satisfied]
      | cons g gs =>
        change satisfied m (CommonNominalConstraints.append (inspectArgument p f g) (inspectArguments ps fs gs))
          ↔ position m p f g ∧ positions m ps fs gs
        rw [for_append,position_exact,ih]

/-- Point comparison refers to the actual declaration and current state.
The ordinary atom receipt is exact relative to the original type or row
terms. It is not a nominal value encoded through the legacy carrier. -/
structure Supported (e : Environment) (s : State) (name : Nat)
    (xs ys : List (ArgumentTerm Nat)) where
  use : Use e name xs.length
  parameters : List Parameter
  declared : use.mode = .declared parameters
  atoms : List (Atom Nat)
  calculation : inspectArguments parameters xs ys = some atoms
  written : ∀ atom ∈ atoms,atom ∈ s.normal.ordinary

theorem same_model {e : Environment} {s : State} {name xs ys} (seen : Supported e s name xs ys)
    (m : Assignment) (valid : Models s m) : positions m seen.parameters xs ys := by
  have fit : All CommonNominalFullCarrier.model m seen.atoms :=
    fun atom here => valid.1.1 atom (seen.written atom here)
  exact (arguments_exact ..).mp ⟨_,seen.calculation,fit⟩

def read (e : Environment) (s : State) (name : Nat) (xs ys : List (ArgumentTerm Nat)) :
    Option (Supported e s name xs ys) := do
  let use ← readUse e name xs.length
  match actual : use.mode with
  | .declared ps =>
    match calculation : inspectArguments ps xs ys with
    | some atoms =>
      if exact : atoms.all (fun a => decide (a ∈ s.normal.ordinary)) = true then
        some ⟨use,ps,actual,atoms,calculation,fun a h => of_decide_eq_true (List.all_eq_true.mp exact a h)⟩
      else none
    | none => none
  | _ => none

end Yulang.GeneralDeclarativeWitnessPointModes357
