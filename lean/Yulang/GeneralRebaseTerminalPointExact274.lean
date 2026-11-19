import Yulang.GeneralRebaseTerminalDecode274

set_option maxRecDepth 23000
set_option maxHeartbeats 7900000
namespace Yulang.GeneralRebaseTerminalPointExact274
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedPlans231 (Holds)
open GeneralDictionaryVersionedPointStage233 (point allocated reserved ordinary)
open GeneralDictionaryVersionedSecondInstall233 (installed effect terminal)
open GeneralDictionaryVersionedSecondRaw233 (newLo newHi)
open GeneralDictionaryJournalRefinement228Source (root snapshot foo)
open GeneralDictionaryOptionalInstall229 (actual)
open GeneralDictionaryVersionedPoint233 (Values)
open GeneralRebaseTerminalRowFrame274 (oldPlan newPlan)
open GeneralRebaseTerminalPublic274 (first_fixed point_fixed first_to_source)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)
open GeneralNominalAssignmentCongruence238 (Same)

def NewFacts (m : Assignment) : Prop :=
 Equivalent (m newLo).1 (m 2).1 ∧ Equivalent (m newHi).1 (m 2).1

theorem point_source (m : Assignment) (valid : Models point m) :
 GeneralNominalState.Models snapshot m :=
 first_to_source m ((GeneralDictionaryVersionedPointStage233.models_iff m).mp valid)

theorem old_actual_width (m : Assignment) (valid : Models point m) :
 Equivalent (m actual).1 (m 2).1 := by
 have held := valid.2.1 oldPlan GeneralDictionaryVersionedPointStage233.original_plan_retained
 have shape : oldPlan.headSchema = GeneralDictionaryCompoundPacket238.plan.headSchema := by
   rw [GeneralDictionaryOptionalInstall229.head_schema,GeneralDictionaryCompoundPacket238.head_schema]
 have exact := GeneralRebaseCompoundOwnerCapture273.actual_is_width m oldPlan
   (point_source m valid) shape held.2.1.2.2.2.2.1
 rwa [GeneralNominalVersionedFrame231.binder_eq,GeneralDictionaryOptionalInstall229.binder_exact] at exact

def fields : List Nat := [2,actual,newLo,newHi]

def present (m : Assignment) : Assignment :=
 fun id => (if id = 0 then foo else if id = 4 then GeneralDictionaryOptionalOutput229.value
   else if id ∈ fields then .emptyRecord else (m id).1,(m id).2)

theorem point_legacy_empty : GeneralNominalVersionedMixedRegistry234.LegacyEmpty point := ⟨rfl,rfl⟩

theorem representative (m : Assignment) (valid : Models point m) (new : NewFacts m) :
 Same m (present m) := by
 intro id
 refine ⟨?_,rfl⟩
 have fixed := point_fixed m valid
 have width : Equivalent (m 2).1 .emptyRecord := fixed 2 (by decide)
 by_cases zero : id = 0
 · subst id; exact fixed 0 (by decide)
 · by_cases four : id = 4
   · subst id; exact fixed 4 (by decide)
   · by_cases supported : id ∈ fields
     · have target : (present m id).1 = .emptyRecord := by simp [present,zero,four,supported]; rfl
       rw [target]
       simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at supported
       rcases supported with rfl | rfl | rfl | rfl
       · exact width
       · exact equivalent_trans (old_actual_width m valid) width
       · exact equivalent_trans new.1 width
       · exact equivalent_trans new.2 width
     · simp only [present,zero,four,supported]
       exact ⟨subtype_refl _,subtype_refl _⟩

theorem issues (m : Assignment) : Values (present m) := by
 constructor <;> rfl

theorem packet_of_point (m : Assignment) (valid : Models point m) (new : NewFacts m) :
 Holds newPlan m := by
 have same := representative m valid new
 have normalized : Models point (present m) :=
   (GeneralNominalVersionedSourceCongruence238.models_iff same point point_legacy_empty).mp valid
 have proof := GeneralDictionaryVersionedPoint233.packet_holds allocated reserved ordinary (issues m) normalized.1.1
 exact (GeneralNominalVersionedPacketCongruence238.holds_iff same newPlan).mpr proof

theorem classes_of_point (m : Assignment) (valid : Models point m) (new : NewFacts m) :
 GeneralNominalVersionedEffects231.ClassEffects point.core root newPlan m := by
 have same := representative m valid new
 have canonical := GeneralDictionaryVersionedPointFrame233.class_effects allocated reserved ordinary
   (issues m).output GeneralDictionaryVersionedPointStage233.raw_sites
 exact (GeneralNominalVersionedEffectCongruence238.class_iff same point.core root newPlan).mpr canonical

theorem exact (m : Assignment) : Models installed m ↔ Models point m ∧ NewFacts m := by
 constructor
 · intro final
   exact ⟨GeneralNominalVersionedInstall232.step_models rfl final,GeneralDictionaryVersionedSecondRaw233.raw_new final.1.1⟩
 · rintro ⟨pointModel,known⟩
   have held := packet_of_point m pointModel known
   have classes := classes_of_point m pointModel known
   apply (GeneralNominalVersionedInstall232.install_models rfl).mpr
   refine ⟨pointModel,held,⟨GeneralNominalVersionedPlans231.head_models held,classes⟩,?_,?_,?_⟩
   · exact (GeneralNominalVersionedFrameTransport232.class_effects_iff
       (fun _ => GeneralNominalVersionedTerminal232.requests_iff terminal)).mpr classes
   · exact GeneralNominalVersionedTerminal232.legacy_live terminal pointModel.1
   · intro prior member
     exact (GeneralNominalVersionedFrameTransport232.class_effects_iff
       (fun _ => GeneralNominalVersionedTerminal232.requests_iff terminal)).mpr (pointModel.2.2 prior member).2

end Yulang.GeneralRebaseTerminalPointExact274
