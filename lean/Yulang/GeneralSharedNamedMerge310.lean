import Yulang.GeneralSharedNamedDependence310
import Yulang.GeneralVersionedOrdinaryFrame310

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25000
set_option maxHeartbeats 15000000
namespace Yulang.GeneralSharedNamedMerge310
open GeneralSharedNamedSource310 (root registry compiled)
open GeneralSharedNamedPlan310 (loSite hiSite z)
open GeneralSharedNamedInstall310 (after reachable actual_low)
open GeneralSharedNamedEvidence310 (alias_identity siblings_different)
open GeneralSharedNamedLeaf310 (named_requests)
open GeneralNominalVersionedJournal232 (Models State Effect)
open GeneralNominalVersionedAdministrative232 (merge merge_models)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalSaturationState (Alias)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent subtype_refl)
open GeneralDeclarationExamples (roles)
open GeneralNominalCenteredHeadOutputs (requests mem_requests_iff EqualOutputs)
open GeneralNominalCenters (Site SameInputs)
open GeneralDictionaryOrdinaryTransport (extend)

abbrev merged : State roles := merge after loSite hiSite

abbrev added := GeneralNominalDemandMerging.outputAtoms loSite.observed hiSite.observed

theorem after_context : merged.core.erased.current.context = extend after.core.erased.current.context [] added [] := by
  simp only [merge,GeneralNominalCenteredHeadMatStepJournal.merge,GeneralNominalCenteredHeadMatStepJournal.change,
    GeneralNominalCenteredSteps.administrative,GeneralNominalSaturationState.merge,extend,
    GeneralDictionaryOrdinaryTransport.extendState,GeneralNominalState.extend,List.append_nil]

theorem added_exact : added = GeneralNominalAllocation.equations z (.var z) := by
  change GeneralNominalDemandMerging.outputAtoms loSite.observed hiSite.observed = _
  unfold GeneralNominalDemandMerging.outputAtoms
  change loSite.occurrence.demand.outputs.flatMap _ = _
  rw [named_requests .low]
  change hiSite.occurrence.demand.outputs.flatMap _ = _
  rw [named_requests .high]
  rfl

theorem added_model (m : Assignment) :
    PresenceNormalForm.All CommonNominalFullCarrier.model m added := by
  apply (GeneralNominalDemandMerging.output_atoms_exact _ _ _).mpr
  intro a ha b hb _
  change a ∈ loSite.occurrence.demand.outputs at ha
  change b ∈ hiSite.occurrence.demand.outputs at hb
  cases List.mem_singleton.mp (named_requests .low ▸ ha)
  cases List.mem_singleton.mp (named_requests .high ▸ hb)
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem supported : GeneralVersionedOrdinaryFrame310.Supported after.core.erased.current.context.state added := by
  intro atom seen i hit
  rw [added_exact] at seen
  have eq : GeneralNominalAllocation.equations z (.var z) =
      [.tyLe (.var z) (.var z),.tyLe (.var z) (.var z)] := rfl
  rw [eq] at seen
  simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at seen
  subst atom
  have one : i = z := by
    change i ∈ [z,z] at hit
    simpa using hit
  subst i
  exact GeneralSharedNamedLeafFrame310.z_available

theorem same_inputs : SameInputs (Models after) loSite hiSite := by
  refine ⟨rfl,?_⟩
  change GeneralNominalDemandMerging.All₂ (GeneralNominalDemandMerging.Related (Models after))
    (List.ofFn fun i => some (.source (loSite.center i))) (List.ofFn fun i => some (.source (hiSite.center i)))
  simp only [List.ofFn_succ,List.ofFn_zero]
  rw [GeneralSharedNamedPlan310.center_low,GeneralSharedNamedPlan310.center_high]
  exact .cons ⟨_,_,rfl,rfl,GeneralNominalDemandMerging.source_same _ _⟩ .nil

theorem step : Step compiled root after merged :=
  ⟨loSite.occurrence,actual_low,.merge loSite hiSite
    (GeneralSharedNamedInstall310.centers ▸ List.mem_cons_of_mem _ List.mem_cons_self)
    (GeneralSharedNamedInstall310.centers ▸ List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    same_inputs (fun h => siblings_different (alias_identity h))⟩

theorem reached : B4TargetV8.Reachable (boundary roles) registry root merged := by
  obtain ⟨first,checked,path⟩ := reachable
  exact ⟨first,checked,.tail path step⟩

theorem aliases : merged.core.erased.current.aliases = [(loSite.occurrence.identity,hiSite.occurrence.identity)] := rfl

theorem root_not_alias_child {x : Nat} (h : Alias merged.core.erased.current root.identity x) :
    x = root.identity := by
  have closed : ∀ {a b}, Alias merged.core.erased.current a b → (a = root.identity ↔ b = root.identity) := by
    intro a b rel
    induction rel with
    | refl => rfl
    | edge found =>
      rw [aliases] at found
      have eq := List.mem_singleton.mp found
      cases eq
      exact Iff.intro (fun e => False.elim (GeneralSharedNamedLeafFrame310.invocations .low e))
        (fun e => False.elim (GeneralSharedNamedLeafFrame310.invocations .high e))
    | symm h ih => exact ih.symm
    | trans _ _ h k => exact h.trans k
  exact (closed h).mp rfl

theorem request_root (out : GeneralSourceState.Output) (seen : out ∈ requests merged.core root) :
    out = ⟨0,1⟩ := by
  obtain ⟨s,present,alias,member⟩ := mem_requests_iff.mp seen
  change s ∈ after.core.erased.current.sites at present
  rw [GeneralSharedNamedInstall310.raw_sites] at present
  have same := root_not_alias_child alias
  simp only [List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl|rfl|rfl
  · exact List.mem_singleton.mp member
  · exact False.elim (GeneralSharedNamedLeafFrame310.invocations .low same)
  · exact False.elim (GeneralSharedNamedLeafFrame310.invocations .high same)

theorem request_root_iff (out : GeneralSourceState.Output) :
    out ∈ requests merged.core root ↔ out ∈ requests after.core root := by
  constructor
  · intro found
    cases request_root out found
    exact GeneralNominalCenteredHeadOutputs.request_retained _ List.mem_cons_self (.refl _) (List.mem_singleton_self _)
  · intro found
    obtain ⟨s,present,alias,member⟩ := mem_requests_iff.mp found
    have eq := alias_identity alias
    exact mem_requests_iff.mpr ⟨s,present,eq ▸ .refl _,member⟩

theorem models (m : Assignment) : Models merged m ↔ Models after m := by
  refine ⟨GeneralNominalVersionedAdministrative232.merge_restrict,?_⟩
  intro valid
  apply merge_models.mpr
  refine ⟨valid,added_model m,?_,?_⟩
  · intro _ absent; cases absent
  · intro effect seen
    cases List.mem_singleton.mp seen
    have past := (valid.2.2 _ List.mem_cons_self).2
    exact (GeneralNominalVersionedFrameTransport232.class_effects_iff
      (fun out => (request_root_iff out).symm)).mp past

theorem inhabited : Models merged GeneralNominalExamples.model :=
  (models _).mpr GeneralSharedNamedInstall310.inhabited

end Yulang.GeneralSharedNamedMerge310
