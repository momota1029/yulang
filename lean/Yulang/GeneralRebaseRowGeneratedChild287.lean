import Yulang.GeneralRebaseRowParentStep287

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28500
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseRowGeneratedChild287
open GeneralRebaseRowChildSource287
open GeneralRebaseRowParentPacket287
open GeneralRebaseRowParentFrame287
open GeneralNominalVersionedEvidence231 (Frame Evidence)
open GeneralNominalVersionedCandidates231 (Prepared Failed InspectionPending inputs)
open GeneralNominalRecursiveCandidates (arguments report)
open GeneralNominalCenters (Plan Site)
open GeneralNominalCommonBridge (Assignment)

noncomputable abbrev current (choice : Bool) := (after choice).core.erased.current.context

theorem emitted_center (choice : Bool) : GeneralNominalVersionedChildren232.emitted (plan choice) = [center choice] := by
  have length : (GeneralNominalVersionedChildren232.emitted (plan choice)).length = 1 :=
    GeneralNominalVersionedChildren232.emitted_length _
  have present : center choice ∈ GeneralNominalVersionedChildren232.emitted (plan choice) := by
    unfold GeneralNominalVersionedChildren232.emitted
    have belongs : requirement ∈ GeneralCanonicalChildOrder.canonicalRequirements (plan choice).packet.declaration.requirements :=
      (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mp (List.mem_singleton_self _)
    exact List.mem_map.mpr ⟨⟨_,belongs⟩,List.mem_attach _ _,child_site choice⟩
  obtain ⟨found,only⟩ := List.length_eq_one_iff.mp length
  rw [only] at present ⊢
  cases List.mem_singleton.mp present
  rfl

theorem raw_child (choice : Bool) :
    (center choice).observed ∈ (after choice).core.erased.current.sites := by
  change (center choice).observed ∈ before.core.erased.current.sites ++
    GeneralNominalVersionedChildren232.rawSites (plan choice)
  apply List.mem_append_right
  unfold GeneralNominalVersionedChildren232.rawSites
  rw [emitted_center]
  exact List.mem_singleton_self _

theorem center_child (choice : Bool) : center choice ∈ (after choice).core.sites := by
  change center choice ∈ before.core.sites ++ GeneralNominalVersionedChildren232.emitted (plan choice)
  rw [emitted_center]
  exact List.mem_append_right _ (List.mem_singleton_self _)

theorem current_args (choice : Bool) :
    arguments (current choice) (inputs (child choice)) = some [((0 : Fin 3),(0 : Fin 3))] := by
  cases choice <;> decide +kernel

theorem known (choice : Bool) :
    ¬ GeneralNominalState.RootPending (current choice).state (inputs (child choice)).demand := by
  rintro ⟨i,missing⟩
  exact missing ⟨(0 : Fin 3),rfl,Or.inr ⟨inner,rfl⟩⟩

theorem blocked : (report (current false) destructing [((0 : Fin 3),(0 : Fin 3))]).blocked = [((0 : Fin 3),(0 : Fin 3))] := by decide +kernel

theorem not_prepared : ¬ Prepared (registry false) (current false) (child false) destructing := by
  rintro ⟨_,_,coords,found,_,finished,_⟩
  cases Option.some.inj ((current_args false).symm.trans found)
  have no := finished.1
  rw [blocked] at no
  cases no

theorem not_failed : ¬ Failed (registry false) (current false) (child false) destructing := by
  rintro ⟨_,coords,found,_,clear,_,_⟩
  cases Option.some.inj ((current_args false).symm.trans found)
  rw [blocked] at clear
  cases clear

theorem pending_actual : InspectionPending (registry false) (current false) (child false) :=
  ⟨known false,destructing,List.mem_cons_of_mem _ List.mem_cons_self,rfl,not_failed,not_prepared⟩

theorem no_child_evidence (m : Assignment) (payload : GeneralDictionaryReadback.Payload) :
    ¬ Evidence (registry false) (after false).core m (child false) payload := by
  intro ev
  have erased := (GeneralDictionaryReadback.payload_iff_erased ..).mpr ev
  cases erased with
  | node localWitness childEvidence =>
    obtain ⟨p,f⟩ := localWitness
    have d := f.frame.visible
    simp only [List.mem_cons,List.not_mem_nil,or_false] at d
    rcases d with bad|good
    · have impossible := f.frame.role_eq
      rw [bad] at impossible
      cases impossible
    · have fit := f.frame.prepared
      rw [good] at fit
      exact not_prepared fit

end Yulang.GeneralRebaseRowGeneratedChild287
