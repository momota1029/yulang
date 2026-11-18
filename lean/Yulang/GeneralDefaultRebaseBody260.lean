import Yulang.GeneralOwnedOutputActual260
import Yulang.GeneralDictionaryVersionedGap206Install233
namespace Yulang.GeneralDefaultRebaseBody260
open GeneralDictionaryDefaultGap206Source
open GeneralDictionaryVersionedGap206233 (current)
open GeneralDictionaryAssociatedProvenance
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

abbrev body : Body := .default 0 0 (.var 0)
abbrev schema := GeneralNominalCenteredHeadMatEffects.bodySchema plan 0 body

theorem lookup_exact : lookup roles declaration 0 = some body := rfl

theorem schema_exact : schema = ⟨[⟨0,.actual,.variable 0⟩],false⟩ := rfl

theorem body_meaning (assignment : Assignment) :
 GeneralNominalVersionedEffects231.BodyHolds plan 0 assignment body ↔
 Equivalent (assignment 0).1 (assignment 1).1 :=
 (GeneralNominalVersionedEffects231.body_holds_iff ..).trans
   (GeneralNominalCenteredHeadMatEffects.positional_default plan assignment (0 : Fin 1))

theorem request_exact (output) (member : output ∈ GeneralNominalCenteredHeadOutputs.requests current.core root) :
 output = ⟨0,0⟩ := GeneralDictionaryDefaultGap206State.request_exact member

theorem request_present : (⟨0,0⟩ : GeneralSourceState.Output) ∈ GeneralNominalCenteredHeadOutputs.requests current.core root :=
 GeneralNominalCenteredHeadOutputs.mem_requests_iff.mpr
   ⟨GeneralNominalDemandMerging.pointSite root,List.mem_singleton_self _,.refl _,List.mem_singleton_self _⟩

theorem classes_exact (assignment : Assignment) :
 GeneralNominalVersionedEffects231.ClassEffects current.core root plan assignment ↔
 Equivalent (assignment 0).1 (assignment 1).1 := by
 constructor
 · intro valid
   exact (body_meaning assignment).mp (valid.1 ⟨0,0⟩ request_present body lookup_exact)
 · intro equal
   constructor
   · intro output member chosen found
     cases request_exact output member
     have same : chosen = body := Option.some.inj found.symm
     subst chosen
     exact (body_meaning assignment).mpr equal
   · intro first one last two _
     cases request_exact first one
     cases request_exact last two
     exact ⟨subtype_refl _,subtype_refl _⟩

theorem current_source (assignment : Assignment) :
 GeneralNominalVersionedJournal232.Models current assignment ↔ GeneralNominalState.Models snapshot assignment :=
 (GeneralNominalVersionedJournal232.lift_models start assignment).trans
   (GeneralNominalCenteredHeadMatStepJournal.point_initial_models (fun _ => rfl))
end Yulang.GeneralDefaultRebaseBody260
