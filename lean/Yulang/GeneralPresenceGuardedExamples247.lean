import Yulang.GeneralPresenceGuardedBlock246
import Yulang.GeneralPresenceUsedSupport245

/-! A concrete two-node compiled guarded fragment, not a source-reachability
regression. Whole-record default and arrow nodes depend on each other. Arrow
rows read private names whose row values are preserved, not reallocated. -/
namespace Yulang.GeneralPresenceGuardedExamples247
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceGuardedLayer246
open GeneralPresenceGuardedBlock246
open CommonNominalFullCarrier

def targets (index : Fin 2) : Nat := 2 + index.val

def parametersAt (_ : Fin 1) : Nat := 0

def body : Body Nat 2 1 := fun index =>
  if index.val = 0 then
    .recordDefault 7 (.record 8 (.inr 0) .emptyRecord) (.inl 1)
  else
    .arrow (.inl 0) (.var 2) (.inr 0) (.join (.var 3) .empty)

theorem targets_injective : Function.Injective targets := by
  intro first last same
  apply Fin.ext
  simp only [targets] at same
  omega

theorem parameters_separate : ∀ index parameter, targets index ≠ parametersAt parameter := by
  intro index parameter
  simp only [targets,parametersAt]
  omega

def compiledEntries : List (Entry Nat) := entries body targets parametersAt

theorem entries_exact : compiledEntries =
    [(2,.recordDefault 7 (.record 8 (.var 0) .emptyRecord) (.var 3)),
     (3,.arrow (.var 2) (.var 2) (.var 0) (.join (.var 3) .empty))] := by
  rfl

theorem first_reads_second :
    Sum.inl (1 : Fin 2) ∈ references (body 0) := by
  simp [body,references]

theorem second_reads_first :
    Sum.inl (0 : Fin 2) ∈ references (body 1) := by
  simp [body,references]

theorem private_row_reads :
    GeneralPresenceUsedSupport245.rowReads
      (translate (Sum.elim targets parametersAt) (body 1)) = [2,3] := by
  rfl

def assignment (boundary : Nat → Comp model) : Nat → Comp model :=
  GeneralPresenceGuardedBlock246.extend body targets parametersAt boundary

theorem models (boundary : Nat → Comp model) :
    All model (assignment boundary) (block compiledEntries) :=
  block_satisfied body targets targets_injective parametersAt parameters_separate boundary

theorem rows_preserved (boundary : Nat → Comp model) (name : Nat) :
    (assignment boundary name).2 = (boundary name).2 := rfl

theorem private_incoming_row (boundary : Nat → Comp model) :
    (RowTerm.var 2).eval model (assignment boundary) = (boundary 2).2 := rfl

theorem private_outgoing_row (boundary : Nat → Comp model) :
    (RowTerm.join (.var 3) .empty).eval model (assignment boundary) =
      model.join (boundary 3).2 model.empty := rfl

theorem outside_preserved (boundary : Nat → Comp model) (name : Nat)
    (notFirst : name ≠ 2) (notLast : name ≠ 3) :
    assignment boundary name = boundary name := by
  apply extend_outside
  intro index
  have bound := index.isLt
  simp only [targets]
  omega

theorem arbitrary_public_model (boundary : Nat → Comp model) :
    ∃ values, All model values (block compiledEntries) ∧
      (∀ name, name ≠ 2 → name ≠ 3 → values name = boundary name) ∧
      (∀ name, (values name).2 = (boundary name).2) :=
  ⟨assignment boundary,models boundary,outside_preserved boundary,rows_preserved boundary⟩

end Yulang.GeneralPresenceGuardedExamples247
