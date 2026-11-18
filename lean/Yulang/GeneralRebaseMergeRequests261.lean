import Yulang.GeneralRebaseClassRun261
import Yulang.GeneralNominalCenteredHeadAllocV7MergeRegression
namespace Yulang.GeneralRebaseMergeRequests261
open GeneralSourceState (Output)
open GeneralNominalCenteredHeadAllocMergeSource
open GeneralNominalCenteredHeadAllocMergeInstall
open GeneralNominalCenteredHeadAllocMergeState
open GeneralNominalCenteredHeadAllocMergeConflict (focus chosen chosen_checked current)
open GeneralNominalCenters

/-- Both targets are actual requests of the same reached alias class. -/
def outputs : List Output := [⟨0,aTarget⟩,⟨0,bTarget⟩]

theorem first_present (atoms) : (⟨0,aTarget⟩ : Output) ∈
 GeneralNominalCenteredHeadOutputs.requests (stage atoms).core focus :=
 GeneralNominalCenteredHeadOutputs.request_retained aSite.observed
   (List.mem_cons_of_mem _ List.mem_cons_self) (.refl _) (a_outputs.symm ▸ List.mem_singleton_self _)

theorem last_present (atoms) : (⟨0,bTarget⟩ : Output) ∈
 GeneralNominalCenteredHeadOutputs.requests (stage atoms).core focus :=
 GeneralNominalCenteredHeadOutputs.request_retained bSite.observed
   (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
   (.edge (List.mem_singleton_self _)) (b_outputs.symm ▸ List.mem_singleton_self _)

theorem requests_exact (atoms) (output : Output) :
 output ∈ GeneralNominalCenteredHeadOutputs.requests (stage atoms).core focus ↔ output ∈ outputs := by
 constructor
 · intro member
   obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
   change site ∈ [GeneralNominalDemandMerging.pointSite root,aSite.observed,bSite.observed] at present
   rcases List.mem_cons.mp present with rfl | present
   · cases within
   · rcases List.mem_cons.mp present with rfl | present
     · change output ∈ aSite.occurrence.demand.outputs at within
       rw [a_outputs] at within
       cases List.mem_singleton.mp within
       exact List.mem_cons_self
     · cases List.mem_singleton.mp present
       change output ∈ bSite.occurrence.demand.outputs at within
       rw [b_outputs] at within
       cases List.mem_singleton.mp within
       exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
 · intro member
   rcases List.mem_cons.mp member with rfl | member
   · exact first_present atoms
   · cases List.mem_singleton.mp member
     exact last_present atoms

theorem requests_distinct : (⟨0,aTarget⟩ : Output) ≠ ⟨0,bTarget⟩ := by
 intro same
 exact targets_distinct (congrArg Output.target same)

abbrev packet (atoms : List (PresenceNormalForm.Atom Nat)) : GeneralNominalSaturationState.Packet roles :=
 ⟨registry,current atoms,aSite.observed,chosen,chosen_checked,[]⟩
abbrev candidate (atoms : List (PresenceNormalForm.Atom Nat)) : Plan roles := ⟨packet atoms,aSite,rfl⟩

abbrev body := GeneralDictionaryAssociatedProvenance.Body.explicit
 ⟨45,0,.app 2 []⟩

theorem lookup_exact (atoms) :
 GeneralDictionaryAssociatedProvenance.lookup roles (candidate atoms).packet.declaration 0 = some body := rfl

theorem schema_exact (atoms) (target : Nat) :
 GeneralRebaseBodyTable261.schema (candidate atoms) ⟨0,target⟩ =
 ⟨[⟨target,.actual,.primitive (.scalar .int) []⟩],false⟩ := rfl

theorem ready (atoms) : GeneralRebaseClassCheck261.Ready (candidate atoms) outputs := by
 intro output member
 rcases List.mem_cons.mp member with rfl | member
 · rfl
 · cases List.mem_singleton.mp member
   rfl

theorem effects_exact (atoms) (assignment : GeneralNominalCommonBridge.Assignment) :
 GeneralRebaseClassTable261.Effects (candidate atoms) outputs assignment ↔
 GeneralNominalVersionedEffects231.ClassEffects (stage atoms).core focus (candidate atoms) assignment := by
 unfold GeneralRebaseClassTable261.Effects GeneralNominalVersionedEffects231.ClassEffects
 unfold GeneralNominalCenteredHeadOutputs.EqualOutputs
 simp only [requests_exact]
end Yulang.GeneralRebaseMergeRequests261
