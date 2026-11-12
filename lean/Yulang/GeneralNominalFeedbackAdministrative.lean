import Yulang.GeneralNominalFeedbackProgress

/-! A derived finite support for merges, head refreshes and ordinary equality
feedback between candidate installations. No global installation bound is
assumed or obtained by this administrative accessibility theorem. -/
namespace Yulang.GeneralNominalFeedbackAdministrative

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalDemandMerging (Site)
open GeneralNominalFeedbackProgress (Fact Holds remaining)
open GeneralNominalAdministrativeProgress (outputs support)

variable {roles : Roles.RoleDecls} {registry : Registry}

inductive Update (registry : Registry) (before : State roles) : State roles → Prop
  | merge (first last : Site roles) : first ∈ before.sites → last ∈ before.sites →
      GeneralNominalFeedbackSites.SameInputs before first last → ¬ Alias before first.occurrence.identity last.occurrence.identity →
      Update registry before (merge before first last)
  | refresh (focus : Occurrence roles) (context : GeneralNominalCandidates.Context) :
      GeneralNominalCycleSteps.Refresh before context → (source : Nat) →
      source ∈ GeneralNominalState.sources before.context.state →
      ¬ GeneralNominalState.Known before.context.state source → GeneralNominalState.Known context.state source →
      Update registry before (regenerate before context)
  | equate (focus : Occurrence roles) (first last : Nat) :
      first ∈ GeneralNominalState.sources before.context.state → last ∈ GeneralNominalState.sources before.context.state →
      GeneralNominalFeedbackK2.Equal before first last → ¬ GeneralNominalFeedbackSteps.RawEqual before first last →
      Update registry before (GeneralNominalFeedbackSteps.equate before first last)

theorem as_update {before after : State roles} (update : Update registry before after) :
    ∃ focus, GeneralNominalFeedbackSteps.At registry before focus after := by
  cases update with
  | merge first last one two same novel => exact ⟨first.occurrence,.merge first last one two same novel⟩
  | refresh focus context certificate source member old known => exact ⟨focus,.refresh focus context certificate source member old known⟩
  | equate focus first last one two equal novel => exact ⟨focus,.equate focus first last one two equal novel⟩

theorem sites_unchanged {before after : State roles} (update : Update registry before after) : after.sites = before.sites := by
  cases update <;> rfl

private theorem output_atoms_supported (sites : List (Site roles)) (first last : Site roles)
    (one : first ∈ sites) (two : last ∈ sites) (atom : PresenceNormalForm.Atom Nat)
    (member : atom ∈ GeneralNominalDemandMerging.outputAtoms first last) :
    ∀ source ∈ GeneralNominalState.atomSources atom, source ∈ outputs sites := by
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

theorem sources_bounded {before after : State roles} (update : Update registry before after) :
    GeneralNominalState.sources after.context.state ⊆ support before := by
  cases update with
  | refresh _ _ certificate _ _ _ _ => exact fun _ member => List.mem_append_left _ (certificate.support _ member)
  | merge first last one two _ _ =>
    intro source member
    change source ∈ GeneralNominalState.sources (GeneralNominalState.extend before.context.state [] _) at member
    simp only [GeneralNominalState.sources,GeneralNominalState.extend,List.append_nil,List.flatMap_append] at member
    have : source ∈ GeneralNominalState.sources before.context.state ∨
        source ∈ (GeneralNominalDemandMerging.outputAtoms first last).flatMap GeneralNominalState.atomSources := by
      simpa only [GeneralNominalState.sources,List.mem_append,or_assoc] using member
    rcases this with old | added
    · exact List.mem_append_left _ old
    · obtain ⟨atom,member,within⟩ := List.mem_flatMap.mp added
      exact List.mem_append_right _ (output_atoms_supported before.sites first last one two atom member source within)
  | equate focus first last one two _ _ =>
    intro source member
    change source ∈ GeneralNominalState.sources (GeneralNominalState.extend before.context.state [] _) at member
    simp only [GeneralNominalState.sources,GeneralNominalState.extend,List.append_nil,List.flatMap_append] at member
    have : source ∈ GeneralNominalState.sources before.context.state ∨ source = first ∨ source = last := by
      simpa [GeneralNominalState.sources,List.mem_append,or_assoc,GeneralNominalAllocation.equations,
        GeneralNominalState.atomSources,GeneralNominalState.typeSources,or_comm,or_left_comm] using member
    rcases this with old | rfl | rfl
    · exact List.mem_append_left _ old
    · exact List.mem_append_left _ one
    · exact List.mem_append_left _ two

def facts (state : State roles) : List (Fact roles) :=
  (GeneralNominalAdministrativeProgress.facts state).map Sum.inl ++
    (support state).flatMap fun first => (support state).map fun last => Sum.inr (first,last)

theorem supported_update (start before after : State roles)
    (sites : before.sites = start.sites)
    (sources : GeneralNominalState.sources before.context.state ⊆ support start)
    (update : Update registry before after) :
    after.sites = start.sites ∧ GeneralNominalState.sources after.context.state ⊆ support start ∧
      ∃ fact ∈ facts start, ¬ Holds before fact ∧ Holds after fact := by
  refine ⟨(sites_unchanged update).trans sites,?_,?_⟩
  · intro source member
    rcases List.mem_append.mp (sources_bounded update member) with old | output
    · exact sources old
    · exact List.mem_append_right _ (by simpa only [sites] using output)
  · cases update with
    | merge first last one two _ novel =>
      refine ⟨.inl (.alias first.occurrence.identity last.occurrence.identity),?_,novel,?_⟩
      · apply List.mem_append_left
        apply List.mem_map.mpr
        refine ⟨.alias first.occurrence.identity last.occurrence.identity,?_,rfl⟩
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨first,sites ▸ one,
          List.mem_map.mpr ⟨last,sites ▸ two,rfl⟩⟩)
      · exact GeneralNominalCycleSteps.merged_inputs before first last
    | refresh _ _ _ source member old known =>
      refine ⟨.inl (.known source),?_,old,known⟩
      exact List.mem_append_left _ (List.mem_map.mpr ⟨.known source,
        List.mem_append_left _ (List.mem_map.mpr ⟨source,sources member,rfl⟩),rfl⟩)
    | equate _ first last one two _ novel =>
      exact ⟨.inr (first,last),List.mem_append_right _ (List.mem_flatMap.mpr
        ⟨first,sources one,List.mem_map.mpr ⟨last,sources two,rfl⟩⟩),novel,
          GeneralNominalFeedbackSteps.equate_feedback before first last⟩

theorem accessible (registry : Registry) (start : State roles) :
    Acc (fun next current => Update registry current next) start := by
  have all : ∀ current : State roles, current.sites = start.sites →
      GeneralNominalState.sources current.context.state ⊆ support start →
      Acc (fun next current => Update registry current next) current := by
    intro current
    induction current using (measure (remaining (facts start))).wf.induction with
    | h current ih =>
      intro sites sources
      refine Acc.intro current ?_
      intro next update
      obtain ⟨newSites,newSources,fact,member,old,now⟩ := supported_update start current next sites sources update
      obtain ⟨focus,action⟩ := as_update update
      have growth := GeneralNominalFeedbackProgress.at_extends action
      exact ih next (GeneralNominalFeedbackProgress.remaining_decreases (facts start) growth fact member old now)
        newSites newSources
  exact all start rfl (fun _ member => List.mem_append_left _ member)

end Yulang.GeneralNominalFeedbackAdministrative
