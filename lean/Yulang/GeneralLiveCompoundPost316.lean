import Yulang.GeneralLiveCompoundLeafInstall316

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25000
set_option maxHeartbeats 30000000
namespace Yulang.GeneralLiveCompoundPost316
open GeneralDictionaryJournalRefinement228Source (roles root snapshot width_two lower_width)
open GeneralLiveCompoundUpperSnapshot316 (snap context)
open GeneralLiveCompoundUpperRefresh316 (upperState)
open GeneralLiveCompoundChildSite316
open GeneralLiveCompoundLeafHead316 (packet plan)
open GeneralLiveCompoundLeafEvidence316 (terminal)
open GeneralLiveCompoundLeafInstall316 (effect after)
open GeneralNominalVersionedChildren232
open GeneralNominalVersionedInstallation231 (reserved atoms allocated replayPlan)
open GeneralNominalRecursiveInspection (selfChecks)
open GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

noncomputable abbrev cur := after.core.erased.current.context
noncomputable abbrev raw := cur.state

theorem no_emitted : emitted plan = [] := by
  simpa only [List.map_eq_nil_iff,terminal] using emitted_occurrences plan

theorem raw_sites_after : after.core.erased.current.sites =
    [GeneralNominalDemandMerging.pointSite root,childSite.observed] := by
  change upperState.core.erased.current.sites ++ rawSites plan = _
  rw [raw_sites,rawSites,no_emitted]
  rfl

theorem centers_after : after.core.sites = [rootSite snapshot.seed root,childSite] := by
  change upperState.core.sites ++ emitted plan = _
  rw [centers,no_emitted,List.append_nil]

theorem aliases_after : after.core.erased.current.aliases = [] := rfl

theorem ordinary_exact : atoms packet =
    [ .tyLe (.var 4) (.var 2), .tyLe (.var GeneralDictionaryCompoundBase239.lo) (.var GeneralDictionaryCompoundBase239.hi),
      .tyLe (.var GeneralDictionaryCompoundBase239.lo) (.var GeneralDictionaryCompoundBase239.hi),
      .tyLe (.var 4) (.var 2)] := by
  unfold atoms
  rw [GeneralLiveCompoundLeafHead316.bindings]
  change _ ++ selfChecks snap (GeneralNominalRecursiveCandidates.report context GeneralLiveCompoundRegistry316.leaf [(5,6)]) = _
  rw [leaf_report]
  change _ ++ [] ++ _ = _
  rfl

theorem atoms_raw (m : Assignment) (valid : GeneralNominalState.Models snap m) :
    PresenceNormalForm.All CommonNominalFullCarrier.model m (atoms packet) := by
  rw [ordinary_exact]
  have sourceValid := GeneralMixedCompoundUpperEqClosed307.source_restrict valid
  have low := lower_width m sourceValid
  have lower : Equivalent (m GeneralDictionaryCompoundBase239.lo).1 (variant 0 (m 4).1) :=
    valid.1.2.1 (5 : Fin 8) _ rfl
  have upper : Equivalent (m GeneralDictionaryCompoundBase239.hi).1 (variant 0 (m 2).1) :=
    valid.1.2.1 (6 : Fin 8) _ rfl
  have range : Subtype (m GeneralDictionaryCompoundBase239.lo).1 (m GeneralDictionaryCompoundBase239.hi).1 :=
    subtype_trans lower.1 (subtype_trans ((common_variant_iff ..).mpr low) upper.2)
  intro a seen
  simp only [List.mem_cons,List.not_mem_nil,or_false] at seen
  rcases seen with rfl|rfl|rfl|rfl
  · exact low
  · exact range
  · exact range
  · exact low

theorem raw_models (m : Assignment) : GeneralNominalState.Models raw m ↔ GeneralNominalState.Models snap m := by
  change GeneralNominalState.Models
    (GeneralDictionaryOrdinaryTransport.extendState snap (reserved packet) (atoms packet) (allocated packet)) m ↔ _
  rw [GeneralDictionaryOrdinaryTransport.models_extended]
  exact ⟨And.left,fun h => ⟨h,atoms_raw m h⟩⟩

theorem known_iff (key : Nat) : GeneralNominalState.Known raw key ↔ GeneralNominalState.Known snap key := Iff.rfl

theorem point_closed : GeneralNominalReobservationSteps.PointClosed raw :=
  GeneralMixedCompoundUpperHalt307.point_closed

theorem generated_after : GeneralNominalSaturationState.Generated after.core.erased.current root child := by
  apply GeneralNominalSaturationState.Generated.child .root
  change (root,child) ∈ upperState.core.erased.current.edges ++ _
  apply List.mem_append_left
  exact GeneralNominalVersionedInstall232.installed_child (children ▸ List.mem_singleton_self _)

theorem leaf_replayed : GeneralNominalVersionedPlans231.Holds (replayPlan plan) GeneralLiveCompoundLeafProof316.w :=
  (GeneralNominalVersionedInstallation231.replay_holds_iff ..).mpr GeneralLiveCompoundLeafEvidence316.holds

end Yulang.GeneralLiveCompoundPost316
