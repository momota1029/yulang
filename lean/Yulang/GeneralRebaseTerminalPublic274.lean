import Yulang.GeneralRebaseCompoundRowsMeaning273
import Yulang.GeneralDictionaryVersionedSecondStep233
import Yulang.GeneralNominalVersionedSourceCongruence238

set_option maxRecDepth 18000
set_option maxHeartbeats 5300000
namespace Yulang.GeneralRebaseTerminalPublic274
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralDictionaryVersionedInitialFrame233 (before)
open GeneralDictionaryVersionedPointStage233 (point)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralDictionaryOptionalInstall229 (plan)
open GeneralRebaseCompoundPublic273 (Fixed AgreesTypes)
open GeneralRebaseCompoundSourceTypes273 (Body PublicSource)
open GeneralDictionaryVersionedBothModel233 (extended)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)

noncomputable abbrev first := GeneralDictionaryVersionedInitialFrame233.installed

theorem first_to_source (m : Assignment) (valid : Models first m) :
 GeneralNominalState.Models snapshot m :=
 (GeneralNominalVersionedJournal232.initial_models .. |>.mp
  (GeneralNominalVersionedInstall232.step_models rfl valid)).1

theorem first_output (m : Assignment) (valid : Models first m) : Body m := by
 have held := (valid.2.1 plan (List.mem_cons_self ..)).2.2
 unfold GeneralNominalVersionedPlans231.Outputs at held
 rw [GeneralDictionaryVersionedBothPacket233.emitted_schema] at held
 exact held _ (List.mem_singleton_self _)

theorem first_fixed (m : Assignment) (valid : Models first m) : Fixed m :=
 (GeneralRebaseCompoundSourceTypes273.restricted_exact m).mpr
  ⟨GeneralRebaseCompoundSourceTypes273.source_reads m (first_to_source m valid),first_output m valid⟩

theorem point_fixed (m : Assignment) (valid : Models point m) : Fixed m :=
 first_fixed m ((GeneralDictionaryVersionedPointStage233.models_iff m).mp valid)

theorem final_fixed (m : Assignment) (valid : Models installed m) : Fixed m :=
 point_fixed m (GeneralNominalVersionedInstall232.step_models rfl valid)

theorem final_to_first (m : Assignment) (valid : Models installed m) : Models first m :=
 (GeneralDictionaryVersionedPointStage233.models_iff m).mp
   (GeneralNominalVersionedInstall232.step_models rfl valid)

theorem final_legacy_empty : GeneralNominalVersionedMixedRegistry234.LegacyEmpty installed := ⟨rfl,rfl⟩

noncomputable def complete (boundary : Assignment) : Assignment :=
 fun id => (if id ≤ 4 then (boundary id).1 else (extended id).1,(extended id).2)

theorem complete_types (boundary : Assignment) : AgreesTypes (complete boundary) boundary := by
 intro id small
 simp [complete,small]

theorem completion_congruent (boundary : Assignment) (known : Fixed boundary) :
 GeneralNominalAssignmentCongruence238.Same extended (complete boundary) := by
 intro id
 refine ⟨?_,rfl⟩
 by_cases small : id ≤ 4
 · rw [complete_types boundary id small]
   have fixed := final_fixed extended GeneralDictionaryVersionedSecondInstall233.installed_model id small
   have actual := known id small
   exact equivalent_trans fixed ⟨actual.2,actual.1⟩
 · simp only [complete,small,ite_false]
   exact ⟨subtype_refl _,subtype_refl _⟩

theorem complete_terminal (boundary : Assignment) (known : Fixed boundary) : Models installed (complete boundary) :=
 (GeneralNominalVersionedSourceCongruence238.models_iff (completion_congruent boundary known)
   installed final_legacy_empty).mp GeneralDictionaryVersionedSecondInstall233.installed_model

def TypePublic (s : State roles) (boundary : Assignment) : Prop := ∃ m, AgreesTypes m boundary ∧ Models s m

theorem terminal_exact (boundary : Assignment) : TypePublic installed boundary ↔ Fixed boundary := by
 constructor
 · rintro ⟨m,agrees,held⟩ id small
   rw [← agrees id small]; exact final_fixed m held id small
 · intro known; exact ⟨complete boundary,complete_types boundary,complete_terminal boundary known⟩

theorem point_exact (boundary : Assignment) : TypePublic point boundary ↔ Fixed boundary := by
 constructor
 · rintro ⟨m,agrees,held⟩ id small
   rw [← agrees id small]; exact point_fixed m held id small
 · intro known
   obtain ⟨m,agrees,full⟩ := (terminal_exact boundary).mpr known
   exact ⟨m,agrees,GeneralNominalVersionedInstall232.step_models rfl full⟩

theorem first_exact (boundary : Assignment) : TypePublic first boundary ↔ Fixed boundary :=
 (exists_congr (fun m => and_congr Iff.rfl (GeneralDictionaryVersionedPointStage233.models_iff m).symm)).trans
  (point_exact boundary)

end Yulang.GeneralRebaseTerminalPublic274
