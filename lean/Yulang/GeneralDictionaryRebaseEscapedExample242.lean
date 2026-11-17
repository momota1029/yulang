import Yulang.GeneralNominalRebaseEscapedStore242
set_option backward.isDefEq.respectTransparency false
/-! A private type escapes into an ordinary consumer. Replacing its definition
retains the old source constraint and the independent row constraint. -/
namespace Yulang.GeneralDictionaryRebaseEscapedExample242
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalFiniteEquationRealization236
open GeneralNominalRebaseEscapedProjection242
open GeneralNominalRebaseEscapedReplace242
open GeneralNominalRebaseEscapedStore242
open GeneralNominalRebaseInline241
open CommonNominalFullCarrier

def oldEntries : List Entry := [(3,.var 0)]
def newEntries : List Entry := [(3,.var 1)]
def atoms : List (PresenceNormalForm.Atom Nat) :=
 [.tyLe (.var 3) (.var 2),.rowLe (.var 3) (.var 2)]

theorem old_coherent : Coherent oldEntries := by
 intro first member last included _
 cases List.mem_singleton.mp member
 cases List.mem_singleton.mp included
 rfl

theorem new_coherent : Coherent newEntries := by
 intro first member last included _
 cases List.mem_singleton.mp member
 cases List.mem_singleton.mp included
 rfl

theorem old_external : External oldEntries := by
 intro entry member name present target included
 cases List.mem_singleton.mp member
 cases List.mem_singleton.mp included
 have zero : name = 0 := List.mem_singleton.mp present
 subst name
 decide

theorem new_external : External newEntries := by
 intro entry member name present target included
 cases List.mem_singleton.mp member
 cases List.mem_singleton.mp included
 have one : name = 1 := List.mem_singleton.mp present
 subst name
 decide

theorem targets : TargetsWithin newEntries oldEntries := by
 intro entry member
 cases List.mem_singleton.mp member
 exact ⟨(3,.var 0),by simp [oldEntries],rfl⟩

theorem cell_value (model : Assignment) : (patch oldEntries model 3).1 = (model 0).1 :=
 value oldEntries old_coherent (3,.var 0) (by simp [oldEntries])

theorem untouched_two (model : Assignment) : patch oldEntries model 2 = model 2 := by
 apply outside
 intro entry member
 cases List.mem_singleton.mp member
 decide

def SourceConstraint (model : Assignment) : Prop :=
 Subtype (model 0).1 (model 2).1 ∧ Common.rowLe (model 3).2 (model 2).2

theorem inline_exact (model : Assignment) :
 PresenceNormalForm.All CommonNominalFullCarrier.model model (inline oldEntries atoms) ↔
 SourceConstraint model := by
 rw [show inline oldEntries atoms = atoms.map (atomSubst (substitution oldEntries)) from rfl,
   all_inline old_coherent atoms model]
 simp only [atoms,PresenceNormalForm.All,List.mem_cons,List.not_mem_nil,or_false,
   forall_eq_or_imp,forall_eq,PresenceNormalForm.Atom.Holds,Core.PresenceGeneration.TyTerm.eval,
   Core.PresenceGeneration.RowTerm.eval]
 change (Subtype (patch oldEntries model 3).1 (patch oldEntries model 2).1 ∧
   Common.rowLe (patch oldEntries model 3).2 (patch oldEntries model 2).2) ↔ SourceConstraint model
 rw [cell_value,untouched_two,row oldEntries 3]
 rfl

theorem old_projection (model : Assignment) :
 (∃ extension, Preserves oldEntries extension model ∧ Definitions oldEntries extension ∧
   PresenceNormalForm.All CommonNominalFullCarrier.model extension atoms) ↔ SourceConstraint model :=
 (projected_iff oldEntries old_coherent old_external atoms model).trans (inline_exact model)

theorem new_table_exact (model : Assignment) :
 PresenceNormalForm.All CommonNominalFullCarrier.model model
   (definitionBlock newEntries ++ inline oldEntries atoms) ↔
 Equivalent (model 3).1 (model 1).1 ∧ SourceConstraint model := by
 rw [PresenceNormalForm.all_append,inline_exact]
 apply and_congr_left
 intro _
 change PresenceNormalForm.All CommonNominalFullCarrier.model model
   (GeneralNominalAllocation.equations 3 (.var 1) ++ []) ↔ _
 simp only [List.append_nil]
 exact GeneralNominalCaptureMerges.equations_exact model 3 (.var 1)

theorem replace_projection (model : Assignment) :
 (∃ extension, Preserves oldEntries extension model ∧ Definitions newEntries extension ∧
   PresenceNormalForm.All CommonNominalFullCarrier.model extension (inline oldEntries atoms)) ↔
 SourceConstraint model :=
 (replacement_projection_iff oldEntries newEntries old_coherent old_external new_coherent
   new_external targets atoms model).symm.trans (old_projection model)

theorem self_dependency_excluded : ¬ External [(3,Core.PresenceGeneration.TyTerm.var 3)] := by
 intro external
 exact external (3,.var 3) (by simp) 3 (by simp [GeneralNominalState.typeSources])
   (3,.var 3) (by simp) rfl
end Yulang.GeneralDictionaryRebaseEscapedExample242
