import Yulang.GeneralNominalVersionedMixedAdministrative236
set_option backward.isDefEq.respectTransparency false
/-! Unconditional accessibility of administrative updates between installations.
The finite basis is derived from the starting state, not supplied as a premise. -/
namespace Yulang.GeneralNominalVersionedMixedAdministrativeOrder236
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedAdministrative236
variable {roles : Roles.RoleDecls} {before after : State roles}

theorem supported_update (start before after : State roles)
    (sameSites : before.core.sites = start.core.sites)
    (sources : GeneralNominalState.sources before.core.erased.current.context.state ⊆ support start)
    (update : Update before after) :
    after.core.sites = start.core.sites ∧
    GeneralNominalState.sources after.core.erased.current.context.state ⊆ support start ∧
    ∃ fact ∈ facts start, ¬ Holds before fact ∧ Holds after fact := by
  refine ⟨(sites update).trans sameSites,?_,?_⟩
  · intro source member
    rcases List.mem_append.mp (sources_bounded update member) with old | output
    · exact sources old
    · exact List.mem_append_right _ (by simpa only [sameSites] using output)
  · cases update with
    | refresh context certificate source member old known =>
      refine ⟨.known source,?_,old,known⟩
      simp only [facts,List.mem_append,List.mem_map]
      exact Or.inl (Or.inl (Or.inl ⟨source,sources member,rfl⟩))
    | equate first last one two equal novel =>
      refine ⟨.equal first last,?_,novel,GeneralNominalFeedbackSteps.equate_feedback _ _ _⟩
      simp only [facts,List.mem_append]
      exact Or.inl (Or.inr (List.mem_flatMap.mpr ⟨first,sources one,
        List.mem_map.mpr ⟨last,sources two,rfl⟩⟩))
    | merge first last one two same novel =>
      refine ⟨.alias first.occurrence.identity last.occurrence.identity,?_,novel,
        GeneralNominalCycleSteps.merged_inputs _ first.observed last.observed⟩
      simp only [facts,List.mem_append]
      exact Or.inr (List.mem_flatMap.mpr ⟨first,sameSites ▸ one,
        List.mem_map.mpr ⟨last,sameSites ▸ two,rfl⟩⟩)
    | reobserve revision certificate improved =>
      obtain ⟨slot,old,now⟩ := improved.2
      refine ⟨.point (before.core.erased.current.context.state.base.source slot),?_,?_,slot,rfl,now⟩
      · simp only [facts,List.mem_append]
        exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨_,sources
          (List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_left _ (List.mem_ofFn.mpr ⟨slot,rfl⟩)))),rfl⟩)))
      · rintro ⟨other,same,point⟩
        have equal := before.core.erased.current.context.state.base.source_injective same
        exact old (equal ▸ point)

theorem accessible (start : State roles) : Acc (fun next current => Update current next) start := by
  have all : ∀ current : State roles, current.core.sites = start.core.sites →
      GeneralNominalState.sources current.core.erased.current.context.state ⊆ support start →
      Acc (fun next current => Update current next) current := by
    intro current
    induction current using (measure (GeneralNominalFiniteProgress.remaining Holds (facts start))).wf.induction with
    | h current ih =>
      intro sameSites sources
      refine Acc.intro current ?_
      intro next update
      obtain ⟨newSites,newSources,fact,member,old,now⟩ := supported_update start current next sameSites sources update
      exact ih next (GeneralNominalFiniteProgress.remaining_decreases Holds (facts start)
        (monotone update) member old now) newSites newSources
  exact all start rfl (fun _ member => List.mem_append_left _ member)

end Yulang.GeneralNominalVersionedMixedAdministrativeOrder236
