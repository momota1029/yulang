import Yulang.GeneralNominalVersionedMixedTrace235
import Yulang.GeneralNominalVersionedMixedEqualityClosure235
import Yulang.GeneralNominalReobservationOrder
import Yulang.GeneralNominalFiniteProgress
set_option backward.isDefEq.respectTransparency false
/-! Actual mixed noninstallation updates. No global installation bound. -/
namespace Yulang.GeneralNominalVersionedMixedAdministrative236
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
open GeneralNominalVersionedAdministrative232
variable {roles : Roles.RoleDecls} {before after : State roles}
inductive Update (before : State roles) : State roles → Prop
 | refresh (context : GeneralNominalCandidates.Context) :
    GeneralNominalVersionedMixedObservations233.Refresh before context → (source : Nat) →
    source ∈ GeneralNominalState.sources before.core.erased.current.context.state →
    ¬ GeneralNominalState.Known before.core.erased.current.context.state source →
    GeneralNominalState.Known context.state source →
    Update before (GeneralNominalVersionedRefresh232.refresh before context)
 | equate (first last : Nat) :
    first ∈ GeneralNominalState.sources before.core.erased.current.context.state →
    last ∈ GeneralNominalState.sources before.core.erased.current.context.state →
    Equal before first last → ¬ GeneralNominalFeedbackSteps.RawEqual before.core.erased.current first last →
    Update before (equate before first last)
 | reobserve (revision : GeneralNominalReobservationSteps.Revision before.core.erased.current) :
    GeneralNominalVersionedMixedObservations233.Reobserve before revision →
    GeneralNominalReobservationSteps.Improves revision →
    Update before (GeneralNominalVersionedRefresh232.reobserve before revision)
 | merge (first last : Site roles) : first ∈ before.core.sites → last ∈ before.core.sites →
    SameInputs (Models before) first last →
    ¬ GeneralNominalSaturationState.Alias before.core.erased.current first.occurrence.identity last.occurrence.identity →
    Update before (merge before first last)
inductive Fact where
 | known (source : Nat)
 | point (source : Nat)
 | equal (first last : Nat)
 | alias (first last : Nat)
def Holds (state : State roles) : Fact → Prop
 | .known source => GeneralNominalState.Known state.core.erased.current.context.state source
 | .point source => GeneralNominalReobservationOrder.Point state.core.erased.current source
 | .equal first last => GeneralNominalFeedbackSteps.RawEqual state.core.erased.current first last
 | .alias first last => GeneralNominalSaturationState.Alias state.core.erased.current first last
def support (state : State roles) : List Nat :=
 GeneralNominalState.sources state.core.erased.current.context.state ++
 GeneralNominalAdministrativeProgress.outputs (state.core.sites.map Site.observed)
def facts (state : State roles) : List Fact :=
 (support state).map Fact.known ++ (support state).map Fact.point ++
 ((support state).flatMap fun first => (support state).map fun last => Fact.equal first last) ++
 (state.core.sites.flatMap fun first =>
   state.core.sites.map fun last => Fact.alias first.occurrence.identity last.occurrence.identity)
theorem sites (update : Update before after) : after.core.sites = before.core.sites := by
 cases update <;> rfl
theorem raw_models (update : Update before after)
 (valid : GeneralNominalState.Models after.core.erased.current.context.state model) :
 GeneralNominalState.Models before.core.erased.current.context.state model := by
 cases update with
 | refresh context certificate => exact GeneralNominalRefinements.models certificate.refines _ valid
 | reobserve revision certificate => exact certificate.raw _ valid
 | equate => exact ((GeneralNominalState.extend_models ..).mp valid).1
 | merge => exact ((GeneralNominalState.extend_models ..).mp valid).1
theorem monotone (update : Update before after) (fact : Fact) : Holds before fact → Holds after fact := by
 cases fact with
 | equal first last => exact fun old model valid => old model (raw_models update valid)
 | alias first last =>
   intro old
   have grow : before.core.erased.current.aliases ⊆ after.core.erased.current.aliases := by
     cases update with
     | merge => exact fun _ h => List.mem_cons_of_mem _ h
     | refresh => exact fun _ h => h
     | equate => exact fun _ h => h
     | reobserve => exact fun _ h => h
   induction old with
   | refl => exact .refl _
   | edge h => exact .edge (grow h)
   | symm _ ih => exact .symm ih
   | trans _ _ ih ih' => exact .trans ih ih'
 | known source =>
   cases update with
   | refresh context certificate => exact certificate.refines.known source
   | reobserve revision => exact (GeneralNominalReobservationSteps.revision_known revision source).mpr
   | equate => exact id
   | merge => exact id
 | point source =>
   cases update with
   | refresh context certificate => exact GeneralNominalReobservationOrder.point_refines certificate.refines
   | equate => exact id
   | merge => exact id
   | reobserve revision certificate improved =>
     rintro ⟨slot,same,point⟩
     exact ⟨slot,same,improved.1 slot point⟩

private theorem output_atoms_supported (sites : List (GeneralNominalDemandMerging.Site roles)) (first last : GeneralNominalDemandMerging.Site roles)
    (one : first ∈ sites) (two : last ∈ sites) (atom : PresenceNormalForm.Atom Nat)
    (member : atom ∈ GeneralNominalDemandMerging.outputAtoms first last) :
    ∀ source ∈ GeneralNominalState.atomSources atom, source ∈ GeneralNominalAdministrativeProgress.outputs sites := by
  obtain ⟨a,ha,rest⟩ := List.mem_flatMap.mp member
  obtain ⟨b,hb,member⟩ := List.mem_flatMap.mp rest
  split at member
  · simp only [GeneralNominalAllocation.equations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;>
      simp only [GeneralNominalState.atomSources,GeneralNominalState.typeSources,List.mem_append,
        List.mem_singleton] <;> intro source h
    · rcases h with rfl | rfl
      · exact List.mem_flatMap.mpr ⟨first,one,List.mem_map.mpr ⟨a,ha,rfl⟩⟩
      · exact List.mem_flatMap.mpr ⟨last,two,List.mem_map.mpr ⟨b,hb,rfl⟩⟩
    · rcases h with rfl | rfl
      · exact List.mem_flatMap.mpr ⟨last,two,List.mem_map.mpr ⟨b,hb,rfl⟩⟩
      · exact List.mem_flatMap.mpr ⟨first,one,List.mem_map.mpr ⟨a,ha,rfl⟩⟩
  · cases member

theorem sources_bounded (update : Update before after) :
 GeneralNominalState.sources after.core.erased.current.context.state ⊆ support before := by
 cases update with
 | refresh context certificate => exact fun _ h => List.mem_append_left _ (certificate.support _ h)
 | reobserve => exact fun _ h => List.mem_append_left _ h
 | equate first last one two =>
   intro source member
   exact List.mem_append_left _ (GeneralNominalCenteredHeadMatStepEnumeration.equate_sources one two member)
 | merge first last one two =>
   intro source member
   change source ∈ GeneralNominalState.sources (GeneralNominalState.extend before.core.erased.current.context.state [] _) at member
   simp only [GeneralNominalState.sources,GeneralNominalState.extend,List.append_nil,List.flatMap_append] at member
   have split : source ∈ GeneralNominalState.sources before.core.erased.current.context.state ∨
       source ∈ (GeneralNominalDemandMerging.outputAtoms first.observed last.observed).flatMap GeneralNominalState.atomSources := by
     simpa only [GeneralNominalState.sources,List.mem_append,or_assoc] using member
   rcases split with old | added
   · exact List.mem_append_left _ old
   · obtain ⟨atom,member,within⟩ := List.mem_flatMap.mp added
     exact List.mem_append_right _ (output_atoms_supported _ _ _
       (List.mem_map.mpr ⟨first,one,rfl⟩) (List.mem_map.mpr ⟨last,two,rfl⟩) atom member source within)
end Yulang.GeneralNominalVersionedMixedAdministrative236
