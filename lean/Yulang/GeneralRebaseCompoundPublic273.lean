import Yulang.GeneralRebaseCompoundActual238273
import Yulang.GeneralNominalVersionedSourceCongruence238

set_option maxRecDepth 16000
set_option maxHeartbeats 2300000
namespace Yulang.GeneralRebaseCompoundPublic273
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralDictionaryCompoundFrame238 (before installed)
open GeneralDictionaryCompoundVersionedModel238 (extended)
open GeneralDictionaryJournalRefinement228Source (snapshot context root foo root_fixed alias_zero width_two top_three lower_width)
open GeneralDictionaryOptionalOutput229 (value below_width)
open GeneralRebaseCompoundActual238273 (exact_output)
open GeneralNominalAssignmentCongruence238 (Same)

def view (id : Nat) : Ty :=
 if id = 0 ∨ id = 1 then foo
 else if id = 2 then .emptyRecord
 else if id = 3 then .top
 else value

def Fixed (boundary : Assignment) : Prop :=
 ∀ id ≤ 4, Equivalent (boundary id).1 (view id)

def AgreesTypes (internal boundary : Assignment) : Prop := ∀ id ≤ 4, (internal id).1 = (boundary id).1

theorem installed_before (m : Assignment) (valid : Models installed m) : Models before m :=
 GeneralNominalVersionedInstall232.step_models rfl valid

theorem initial_source (m : Assignment) (valid : Models before m) : GeneralNominalState.Models snapshot m :=
 ((GeneralNominalVersionedJournal232.initial_models context root m).mp valid).1

theorem fixed (m : Assignment) (valid : Models installed m) : Fixed m := by
 have source := initial_source m (installed_before m valid)
 intro id small
 have cases5 : id = 0 ∨ id = 1 ∨ id = 2 ∨ id = 3 ∨ id = 4 := by omega
 rcases cases5 with rfl | rfl | rfl | rfl | rfl
 · exact root_fixed m source
 · exact GeneralDictionaryDefaultExpression209.equivalent_trans
     ⟨(alias_zero m source).2,(alias_zero m source).1⟩ (root_fixed m source)
 · exact width_two m source
 · exact top_three m source
 · exact exact_output m valid

noncomputable def complete (boundary : Assignment) : Assignment :=
 fun id => (if id ≤ 4 then (boundary id).1 else (extended id).1,(extended id).2)

theorem complete_types (boundary : Assignment) : AgreesTypes (complete boundary) boundary := by
 intro id small
 simp [complete,small]

theorem same_model (boundary : Assignment) (good : Fixed boundary) : Same extended (complete boundary) := by
 intro id
 refine ⟨?_,rfl⟩
 by_cases small : id ≤ 4
 · rw [complete_types boundary id small]
   have source := fixed extended GeneralDictionaryCompoundStep238.installed_model id small
   have exactBoundary := good id small
   exact GeneralDictionaryDefaultExpression209.equivalent_trans source ⟨exactBoundary.2,exactBoundary.1⟩
 · simp only [complete,small,ite_false]
   exact ⟨subtype_refl _,subtype_refl _⟩

theorem complete_valid (boundary : Assignment) (good : Fixed boundary) : Models installed (complete boundary) :=
 (GeneralNominalVersionedSourceCongruence238.source_models_iff (same_model boundary good)
   GeneralDictionaryCompoundStep238.reachable).mp GeneralDictionaryCompoundStep238.installed_model

/-- One extension witnesses the entire original post-install journal and
fixes the five public type coordinates jointly, not equation by equation.
The internal row assignment is supplied by the known model; rows are not
part of this projection. -/
theorem public_exact (boundary : Assignment) :
 (∃ m, AgreesTypes m boundary ∧ Models installed m) ↔ Fixed boundary := by
 constructor
 · rintro ⟨m,agree,models⟩ id small
   rw [← agree id small]; exact fixed m models id small
 · intro checked
   exact ⟨complete boundary,complete_types boundary,complete_valid boundary checked⟩

theorem all_public_equivalent {first last : Assignment} (a : Fixed first) (b : Fixed last) :
 ∀ id ≤ 4, Equivalent (first id).1 (last id).1 := fun id small =>
 GeneralDictionaryDefaultExpression209.equivalent_trans (a id small) ⟨(b id small).2,(b id small).1⟩

end Yulang.GeneralRebaseCompoundPublic273
