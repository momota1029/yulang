import Yulang.GeneralSourceDictionaries

/-!
# Instantiated dictionary-head and associated-output equations

This is a concrete semantic component of I-18 item 5, independent of a resolver.
Every term uses globally allocated source type/row IDs in `Assignment`. No
state-local slot is silently interpreted as a global ID, and no type-ID map is
used to rename row IDs. Terms may refer to IDs outside the current snapshot;
source scoping and declaration instantiation must establish their availability.

The component does not define a declaration, choose a capture, check visibility,
or certify the exhaustive where-child list. It says exactly what the retained
head/output equations mean at each assignment and in all models of one state.
It never infers those equations from state satisfaction alone.
-/
namespace Yulang.GeneralSourceDictionaryEquations

open Core.PresenceGeneration (TyTerm)
open PresenceNormalForm (Atom All)
open GeneralSourceState (Assignment Demand State)

/-- One head per positional argument and one RHS per output occurrence. Indexing
by the full output list preserves repeated names, targets, and multiplicity. -/
structure InstanceEquations (demand : Demand roles) where
  head : Fin (roles demand.role).arity → TyTerm Nat
  output : Fin demand.outputs.length → TyTerm Nat

def intervalAtoms (lower upper : Nat) (head : TyTerm Nat) : List (Atom Nat) :=
  [.tyLe (.var lower) head, .tyLe head (.var upper)]

def outputAtoms (target : Nat) (rhs : TyTerm Nat) : List (Atom Nat) :=
  [.tyLe (.var target) rhs, .tyLe rhs (.var target)]

def InstanceEquations.atoms {demand : Demand roles} (equations : InstanceEquations demand) :
    List (Atom Nat) :=
  (List.ofFn (fun index => intervalAtoms (demand.arguments index).1
    (demand.arguments index).2 (equations.head index))).flatten ++
  (List.ofFn (fun index => outputAtoms (demand.outputs[index]).target
    (equations.output index))).flatten

/-- Independent interval and associated-equality meaning at the same shared
assignment. Associated outputs remain ordinary type variables. -/
def InstanceEquations.Holds {demand : Demand roles} (equations : InstanceEquations demand)
    (assignment : Assignment) : Prop :=
  (∀ index, Common.Subtype (assignment (demand.arguments index).1).1
      ((equations.head index).eval Common.model assignment) ∧
    Common.Subtype ((equations.head index).eval Common.model assignment)
      (assignment (demand.arguments index).2).1) ∧
  ∀ index, Common.Equivalent (assignment (demand.outputs[index]).target).1
    ((equations.output index).eval Common.model assignment)

theorem intervalAtoms_exact (lower upper : Nat) (head : TyTerm Nat)
    (assignment : Assignment) :
    All Common.model assignment (intervalAtoms lower upper head) ↔
      Common.Subtype (assignment lower).1 (head.eval Common.model assignment) ∧
        Common.Subtype (head.eval Common.model assignment) (assignment upper).1 := by
  simp [intervalAtoms, All, Atom.Holds, TyTerm.eval, Common.model]

theorem outputAtoms_exact (target : Nat) (rhs : TyTerm Nat) (assignment : Assignment) :
    All Common.model assignment (outputAtoms target rhs) ↔
      Common.Equivalent (assignment target).1 (rhs.eval Common.model assignment) := by
  simp [outputAtoms, All, Atom.Holds, TyTerm.eval, Common.model, Common.Equivalent]

private theorem all_flatten_ofFn (parts : Fin count → List (Atom Nat))
    (assignment : Assignment) :
    All Common.model assignment (List.ofFn parts).flatten ↔
      ∀ index, All Common.model assignment (parts index) := by
  simp only [All, List.mem_flatten, List.mem_ofFn, forall_exists_index, and_imp]
  constructor
  · intro h index atom member; exact h atom (parts index) index rfl member
  · intro h atom part index equal member; subst part; exact h index atom member

/-- Exactness for every multiargument demand, every vector of instantiated head
and output terms, and every global assignment. No successful selection premise. -/
theorem equations_exact {demand : Demand roles} (equations : InstanceEquations demand)
    (assignment : Assignment) :
    All Common.model assignment equations.atoms ↔ equations.Holds assignment := by
  simp only [InstanceEquations.atoms, PresenceNormalForm.all_append,
    all_flatten_ofFn, intervalAtoms_exact, outputAtoms_exact, InstanceEquations.Holds]

/-- Ordinary propagation preserves every existing atom and adds precisely these
head/output obligations. This does not establish that the result is satisfiable. -/
theorem append_equations_exact {demand : Demand roles} (equations : InstanceEquations demand)
    (old : List (Atom Nat)) (assignment : Assignment) :
    All Common.model assignment (old ++ equations.atoms) ↔
      All Common.model assignment old ∧ equations.Holds assignment := by
  rw [PresenceNormalForm.all_append, equations_exact]

/-- This explicit entailment obligation must be supplied by the selected
candidate/state bridge. It is not a field of a completed source boundary. -/
def Entailed (state : State) {demand : Demand roles} (equations : InstanceEquations demand) : Prop :=
  ∀ assignment, GeneralSourceState.Models state assignment →
    All Common.model assignment equations.atoms

theorem entailed_exact (state : State) {demand : Demand roles}
    (equations : InstanceEquations demand) :
    Entailed state equations ↔
      ∀ assignment, GeneralSourceState.Models state assignment → equations.Holds assignment := by
  simp only [Entailed, equations_exact]

/-- Every repeated named output occurrence contributes its own equality, using
its actual target. No lookup or deduplication discards a repeated obligation. -/
theorem output_equality {demand : Demand roles} (equations : InstanceEquations demand)
    (assignment : Assignment) (held : All Common.model assignment equations.atoms)
    (index : Fin demand.outputs.length) :
    Common.Equivalent (assignment (demand.outputs[index]).target).1
      ((equations.output index).eval Common.model assignment) :=
  ((equations_exact equations assignment).mp held).2 index

theorem all_model_output_equality (state : State) {demand : Demand roles}
    (equations : InstanceEquations demand) (entailed : Entailed state equations)
    (assignment : Assignment) (model : GeneralSourceState.Models state assignment)
    (index : Fin demand.outputs.length) :
    Common.Equivalent (assignment (demand.outputs[index]).target).1
      ((equations.output index).eval Common.model assignment) :=
  output_equality equations assignment (entailed assignment model) index

end Yulang.GeneralSourceDictionaryEquations
