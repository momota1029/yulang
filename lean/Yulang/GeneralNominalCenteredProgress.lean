import Yulang.GeneralNominalCenteredSourceTrace
import Yulang.GeneralNominalWhereRequestMembership

/-! Finite administrative progress for the full centered transition relation.
The order uses persistent raw facts, without requiring guarded erasure. -/
namespace Yulang.GeneralNominalCenteredProgress
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalReobservationOrder (Fact Holds facts remaining Point)
open GeneralNominalAdministrativeProgress (support outputs)

variable {roles : Roles.RoleDecls} {root : Occurrence roles}

theorem at_extends (action : At registry before focus after) :
    GeneralNominalFeedbackProgress.Extends before.erased.current after.erased.current := by
  cases action with
  | administrative focus after action =>
    exact GeneralNominalReobservationSteps.at_extends (GeneralNominalSupportSteps.administrative_old action)
  | refresh focus context certificate source member unknown known =>
    exact ⟨⟨fun model valid => ⟨GeneralNominalRefinements.models certificate.refines model valid.1,valid.2⟩,
      fun _ member => member,fun _ member => member,fun _ member => member,certificate.refines.known⟩,
      GeneralNominalRefinements.models certificate.refines⟩
  | merge first last support one two same novel guard =>
    exact ⟨⟨fun model valid => ((GeneralNominalSaturationState.merge_models ..).mp valid).1,
      fun _ member => member,fun _ member => member,fun _ member => List.mem_cons_of_mem _ member,
      fun _ known => known⟩,fun model valid => ((GeneralNominalState.extend_models ..).mp valid).1⟩
  | install plan support enabled novel guard =>
    have refinement := GeneralNominalRefinements.installed plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.bounds
    refine ⟨⟨fun model valid => ((GeneralNominalSharedSteps.install_models (support := support) enabled.1.2.1 model).mp valid).1,
      fun _ member => List.mem_append_left _ member,fun _ member => List.mem_append_left _ member,
      fun _ member => member,?_,⟩,?_⟩
    · intro source known
      exact refinement.known source (enabled.1.2.1 ▸ known)
    · intro model valid
      rw [← enabled.1.2.1]
      exact GeneralNominalRefinements.models refinement model valid

theorem at_point (action : At registry before focus after) (known : Point before.erased.current source) :
    Point after.erased.current source := by
  cases action with
  | administrative focus after action =>
    exact GeneralNominalReobservationOrder.point_at (GeneralNominalSupportSteps.administrative_old action) known
  | refresh focus context certificate source member unknown known' =>
    exact GeneralNominalReobservationOrder.point_refines certificate.refines known
  | merge => exact known
  | install plan support enabled novel guard =>
    apply GeneralNominalReobservationOrder.point_refines (before := before.erased.current) _ known
    change GeneralNominalRefinements.Refines before.erased.current.context.state plan.packet.privateContext.state
    rw [← enabled.1.2.1]
    exact GeneralNominalRefinements.installed plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.bounds

theorem monotone (action : At registry before focus after) (fact : Fact roles) :
    Holds before.erased.current fact → Holds after.erased.current fact := by
  cases fact with
  | inl fact => exact GeneralNominalFeedbackProgress.monotone (at_extends action) fact
  | inr source => exact at_point action

theorem clause_child_member (plan : Plan roles) (clause : Clause)
    (member : clause ∈ plan.packet.declaration.requirements) (signature : clause.Signature roles) :
    (plan.childSite clause signature).occurrence ∈ plan.packet.children := by
  apply List.mem_map.mpr
  refine ⟨_,GeneralNominalWhereRequestMembership.canonical_emission_member
    plan.packet.site.occurrence.identity plan.packet.declaration plan.packet.checked _ _ clause member,rfl⟩

theorem sites_correspond (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ site ∈ state.sites, ∃ raw ∈ state.erased.current.sites, raw.occurrence = site.occurrence := by
  induction path with
  | refl =>
    intro site member
    cases List.mem_singleton.mp member
    exact ⟨_,List.mem_singleton_self _,rfl⟩
  | tail path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    have growth := (at_extends action).journal.sites
    cases action with
    | administrative =>
      intro site member
      obtain ⟨raw,present,same⟩ := ih site member
      exact ⟨raw,growth raw present,same⟩
    | refresh | merge => exact ih
    | install plan support enabled novel guard =>
      intro site member
      rcases List.mem_append.mp member with old | added
      · obtain ⟨raw,present,same⟩ := ih site old
        exact ⟨raw,List.mem_append_left _ present,same⟩
      · obtain ⟨clause,_,rfl⟩ := List.mem_map.mp added
        exact ⟨_,List.mem_append_right _ (List.mem_map.mpr
          ⟨_,clause_child_member plan clause.val clause.property _,rfl⟩),rfl⟩

theorem output_atoms_supported (sites : List (GeneralNominalDemandMerging.Site roles))
    (first last : GeneralNominalDemandMerging.Site roles)
    (one : ∃ raw ∈ sites, raw.occurrence = first.occurrence)
    (two : ∃ raw ∈ sites, raw.occurrence = last.occurrence)
    (atom : PresenceNormalForm.Atom Nat) (member : atom ∈ GeneralNominalDemandMerging.outputAtoms first last) :
    ∀ source ∈ GeneralNominalState.atomSources atom, source ∈ outputs sites := by
  obtain ⟨a,ha,rest⟩ := List.mem_flatMap.mp member
  obtain ⟨b,hb,member⟩ := List.mem_flatMap.mp rest
  obtain ⟨rawOne,presentOne,equalOne⟩ := one
  obtain ⟨rawTwo,presentTwo,equalTwo⟩ := two
  have left : a.target ∈ outputs sites := List.mem_flatMap.mpr
    ⟨rawOne,presentOne,List.mem_map.mpr ⟨a,equalOne.symm ▸ ha,rfl⟩⟩
  have right : b.target ∈ outputs sites := List.mem_flatMap.mpr
    ⟨rawTwo,presentTwo,List.mem_map.mpr ⟨b,equalTwo.symm ▸ hb,rfl⟩⟩
  split at member
  · simp only [GeneralNominalAllocation.equations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;>
      simp only [GeneralNominalState.atomSources,GeneralNominalState.typeSources,List.mem_append,
        List.mem_singleton] <;> intro source h
    · rcases h with rfl | rfl
      · exact left
      · exact right
    · rcases h with rfl | rfl
      · exact right
      · exact left
  · cases member

theorem merge_sources_bounded (state : GeneralNominalSaturationState.State roles)
    (first last : GeneralNominalDemandMerging.Site roles)
    (one : ∃ raw ∈ state.sites, raw.occurrence = first.occurrence)
    (two : ∃ raw ∈ state.sites, raw.occurrence = last.occurrence) :
    GeneralNominalState.sources (GeneralNominalSaturationState.merge state first last).context.state ⊆ support state := by
  intro source member
  change source ∈ GeneralNominalState.sources (GeneralNominalState.extend state.context.state [] _) at member
  simp only [GeneralNominalState.sources,GeneralNominalState.extend,List.append_nil,List.flatMap_append] at member
  have either : source ∈ GeneralNominalState.sources state.context.state ∨
      source ∈ (GeneralNominalDemandMerging.outputAtoms first last).flatMap GeneralNominalState.atomSources := by
    simpa only [GeneralNominalState.sources,List.mem_append,or_assoc] using member
  rcases either with old | added
  · exact List.mem_append_left _ old
  · obtain ⟨atom,present,within⟩ := List.mem_flatMap.mp added
    exact List.mem_append_right _ (output_atoms_supported state.sites first last one two atom present source within)

structure Progress (before after : GeneralNominalSaturationState.State roles) : Prop where
  sites : after.sites = before.sites
  sources : GeneralNominalState.sources after.context.state ⊆ support before
  persistent : ∀ fact, Holds before fact → Holds after fact
  fresh : ∃ fact ∈ facts before, ¬ Holds before fact ∧ Holds after fact

theorem basis_subset (start current : GeneralNominalSaturationState.State roles)
    (sites : current.sites = start.sites)
    (sources : GeneralNominalState.sources current.context.state ⊆ support start) : facts current ⊆ facts start := by
  have bounded : support current ⊆ support start := by
    intro source member
    rcases List.mem_append.mp member with old | output
    · exact sources old
    · exact List.mem_append_right _ (sites ▸ output)
  intro fact member
  change fact ∈ (GeneralNominalFeedbackAdministrative.facts current).map Sum.inl ++ (support current).map Sum.inr at member
  change fact ∈ (GeneralNominalFeedbackAdministrative.facts start).map Sum.inl ++ (support start).map Sum.inr
  rcases List.mem_append.mp member with old | point
  · obtain ⟨fact,factMember,rfl⟩ := List.mem_map.mp old
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨fact,?_,rfl⟩
    change fact ∈ (GeneralNominalAdministrativeProgress.facts current).map Sum.inl ++
      (support current).flatMap (fun first => (support current).map (fun last => Sum.inr (first,last))) at factMember
    change fact ∈ (GeneralNominalAdministrativeProgress.facts start).map Sum.inl ++
      (support start).flatMap (fun first => (support start).map (fun last => Sum.inr (first,last)))
    rcases List.mem_append.mp factMember with basic | equal
    · obtain ⟨fact,basicMember,rfl⟩ := List.mem_map.mp basic
      apply List.mem_append_left
      apply List.mem_map.mpr
      refine ⟨fact,?_,rfl⟩
      change fact ∈ (support current).map GeneralNominalSaturationProgress.Fact.known ++
        current.sites.flatMap (fun first => current.sites.map
          (fun last => GeneralNominalSaturationProgress.Fact.alias first.occurrence.identity last.occurrence.identity)) at basicMember
      change fact ∈ (support start).map GeneralNominalSaturationProgress.Fact.known ++
        start.sites.flatMap (fun first => start.sites.map
          (fun last => GeneralNominalSaturationProgress.Fact.alias first.occurrence.identity last.occurrence.identity))
      rcases List.mem_append.mp basicMember with known | alias
      · obtain ⟨source,sourceMember,rfl⟩ := List.mem_map.mp known
        exact List.mem_append_left _ (List.mem_map.mpr ⟨source,bounded sourceMember,rfl⟩)
      · exact List.mem_append_right _ (sites ▸ alias)
    · obtain ⟨first,one,rest⟩ := List.mem_flatMap.mp equal
      obtain ⟨last,two,rfl⟩ := List.mem_map.mp rest
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨first,bounded one,
        List.mem_map.mpr ⟨last,bounded two,rfl⟩⟩)
  · obtain ⟨source,sourceMember,rfl⟩ := List.mem_map.mp point
    exact List.mem_append_right _ (List.mem_map.mpr ⟨source,bounded sourceMember,rfl⟩)

theorem remaining_monotone (basis : List (Fact roles))
    (persistent : ∀ fact, Holds before fact → Holds after fact) : remaining basis after ≤ remaining basis before := by
  classical
  induction basis with
  | nil => exact Nat.le_refl _
  | cons fact rest ih =>
    change (if Holds after fact then remaining rest after else remaining rest after+1) ≤
      (if Holds before fact then remaining rest before else remaining rest before+1)
    by_cases old : Holds before fact
    · simp only [old,persistent fact old,ite_true]; exact ih
    · by_cases now : Holds after fact <;> simp only [old,now,ite_true,ite_false] <;> omega

theorem remaining_decreases (basis : List (Fact roles))
    (persistent : ∀ fact, Holds before fact → Holds after fact)
    (member : fact ∈ basis) (old : ¬ Holds before fact) (now : Holds after fact) :
    remaining basis after < remaining basis before := by
  classical
  induction basis with
  | nil => cases member
  | cons head rest ih =>
    change (if Holds after head then remaining rest after else remaining rest after+1) <
      (if Holds before head then remaining rest before else remaining rest before+1)
    rcases List.mem_cons.mp member with rfl | member
    · have tail := remaining_monotone rest persistent
      simp only [old,now,ite_true,ite_false]; omega
    · have tail := ih member
      by_cases was : Holds before head
      · simp only [was,persistent head was,ite_true]; exact tail
      · by_cases current : Holds after head <;> simp only [was,current,ite_true,ite_false] <;> omega

theorem progress_accessible (start : GeneralNominalSaturationState.State roles) :
    Acc (fun next current => Progress current next) start := by
  have all : ∀ current : GeneralNominalSaturationState.State roles, current.sites = start.sites →
      GeneralNominalState.sources current.context.state ⊆ support start →
      Acc (fun next current => Progress current next) current := by
    intro current
    induction current using (measure (remaining (facts start))).wf.induction with
    | h current ih =>
      intro sites sources
      refine Acc.intro current ?_
      intro next update
      obtain ⟨fact,member,old,now⟩ := update.fresh
      apply ih next (remaining_decreases _ update.persistent (basis_subset start current sites sources member) old now)
        (update.sites.trans sites)
      intro source member
      rcases List.mem_append.mp (update.sources member) with old | output
      · exact sources old
      · exact List.mem_append_right _ (sites ▸ output)
  exact all start rfl (fun _ member => List.mem_append_left _ member)

def Passive (before after : State roles) : Prop := Progress before.erased.current after.erased.current

theorem passive_accessible (state : State roles) : Acc (fun next current => Passive current next) state := by
  have lift (raw : GeneralNominalSaturationState.State roles)
      (accessible : Acc (fun next current => Progress current next) raw) :
      ∀ state : State roles, state.erased.current = raw → Acc (fun next current => Passive current next) state := by
    induction accessible with
    | intro raw predecessors ih =>
      intro state same
      refine Acc.intro state ?_
      intro next progress
      exact ih next.erased.current (same ▸ progress) next rfl
  exact lift _ (progress_accessible state.erased.current) state rfl

theorem progress_of_update (update : GeneralNominalReobservationOrder.Update registry before after) :
    Progress before after := by
  obtain ⟨sites,sources,fresh⟩ := GeneralNominalReobservationOrder.supported_update before before after rfl
    (fun _ member => List.mem_append_left _ member) update
  obtain ⟨focus,action⟩ := GeneralNominalReobservationOrder.as_update update
  exact ⟨sites,sources,GeneralNominalReobservationOrder.monotone action,fresh⟩

theorem step_cases (path : B4Target.Steps (Step registry root) (initial context root) before)
    (step : Step registry root before after) :
    Passive before after ∨ ∃ plan : Plan roles, ∃ support,
      GeneralNominalSaturationState.Generated before.erased.current root plan.packet.site.occurrence ∧
      GeneralNominalFeedbackSteps.Installable registry before.erased.current plan.packet ∧
      ¬ GeneralNominalFeedbackSteps.Committed before.erased.current plan.packet ∧
      PacketGuard before plan support ∧ after = install before plan support := by
  obtain ⟨focus,generated,action⟩ := step
  have persistent := monotone action
  cases action with
  | administrative focus after action =>
    apply Or.inl
    cases action with
    | enqueue linked absent =>
      obtain ⟨site,member,same⟩ := GeneralNominalCenteredSourceTrace.generated_registered path generated
      exact False.elim (absent site member same)
    | refresh context certificate source member unknown known =>
      exact progress_of_update (registry := registry) (.ordinary (.refresh focus context certificate source member unknown known))
    | equate first last one two equal novel =>
      exact progress_of_update (registry := registry) (.ordinary (.equate focus first last one two equal novel))
    | reobserve revision certificate improved => exact progress_of_update (registry := registry) (.reobserve revision certificate improved)
  | install plan support enabled novel guard => exact Or.inr ⟨plan,support,generated,enabled,novel,guard,rfl⟩
  | refresh focus context certificate source member unknown known =>
    refine Or.inl ⟨rfl,fun _ member => List.mem_append_left _ (certificate.support _ member),persistent,
      .inl (.inl (.known source)),?_,unknown,known⟩
    exact List.mem_append_left _ (List.mem_map.mpr ⟨.inl (.known source),
      List.mem_append_left _ (List.mem_map.mpr ⟨.known source,
        List.mem_append_left _ (List.mem_map.mpr ⟨source,List.mem_append_left _ member,rfl⟩),rfl⟩),rfl⟩)
  | merge first last dependencies one two same novel guard =>
    obtain ⟨rawOne,memberOne,equalOne⟩ := sites_correspond path first one
    obtain ⟨rawTwo,memberTwo,equalTwo⟩ := sites_correspond path last two
    refine Or.inl ⟨rfl,merge_sources_bounded _ first.observed last.observed
      ⟨rawOne,memberOne,equalOne⟩ ⟨rawTwo,memberTwo,equalTwo⟩,persistent,
      .inl (.inl (.alias first.occurrence.identity last.occurrence.identity)),?_,novel,
      GeneralNominalCycleSteps.merged_inputs ..⟩
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨.inl (.alias first.occurrence.identity last.occurrence.identity),?_,rfl⟩
    apply List.mem_append_left
    apply List.mem_map.mpr
    refine ⟨.alias first.occurrence.identity last.occurrence.identity,?_,rfl⟩
    apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨rawOne,memberOne,List.mem_map.mpr ⟨rawTwo,memberTwo,by rw [equalOne,equalTwo]⟩⟩

theorem inconsistent_accessible (path : B4Target.Steps (Step registry root) (initial context root) state)
    (empty : ¬ ∃ model, Models state model) : Acc (fun next current => Step registry root current next) state := by
  have all (state : State roles) (accessible : Acc (fun next current => Passive current next) state) :
      B4Target.Steps (Step registry root) (initial context root) state →
      (¬ ∃ model, Models state model) → Acc (fun next current => Step registry root current next) state := by
    induction accessible with
    | intro before predecessors ih =>
      intro path empty
      refine Acc.intro before ?_
      intro after step
      rcases step_cases path step with passive | ⟨plan,support,generated,enabled,novel,guard,rfl⟩
      · exact ih after passive (.tail path step) (fun ⟨model,valid⟩ => empty ⟨model,step_models step model valid⟩)
      · obtain ⟨model,valid,branch⟩ := guard.2.2.2.2.2.2
        exact False.elim (empty ⟨model,valid⟩)
  exact all state (passive_accessible state) path empty

theorem signature_monotone (step : Step registry root before after)
    (known : GeneralNominalSharedBudget.Holds before.erased signature) :
    GeneralNominalSharedBudget.Holds after.erased signature := by
  have growth := (at_extends step.choose_spec.2).journal
  exact ⟨fun model valid => known.1 model (growth.models model valid),
    fun child member => growth.edges _ (known.2 child member)⟩

theorem signatures_remaining_monotone (basis : List (GeneralNominalSharedBudget.Signature roles))
    (step : Step registry root before after) :
    GeneralNominalSharedBudget.remaining basis after.erased ≤ GeneralNominalSharedBudget.remaining basis before.erased := by
  classical
  induction basis with
  | nil => exact Nat.le_refl _
  | cons signature rest ih =>
    change (if GeneralNominalSharedBudget.Holds after.erased signature then GeneralNominalSharedBudget.remaining rest after.erased
      else GeneralNominalSharedBudget.remaining rest after.erased+1) ≤
      (if GeneralNominalSharedBudget.Holds before.erased signature then GeneralNominalSharedBudget.remaining rest before.erased
      else GeneralNominalSharedBudget.remaining rest before.erased+1)
    by_cases old : GeneralNominalSharedBudget.Holds before.erased signature
    · simp only [old,signature_monotone step old,ite_true]; exact ih
    · by_cases now : GeneralNominalSharedBudget.Holds after.erased signature <;>
        simp only [old,now,ite_true,ite_false] <;> omega

theorem signatures_remaining_decreases (basis : List (GeneralNominalSharedBudget.Signature roles))
    (step : Step registry root before after) (member : signature ∈ basis)
    (old : ¬ GeneralNominalSharedBudget.Holds before.erased signature)
    (now : GeneralNominalSharedBudget.Holds after.erased signature) :
    GeneralNominalSharedBudget.remaining basis after.erased < GeneralNominalSharedBudget.remaining basis before.erased := by
  classical
  induction basis with
  | nil => cases member
  | cons head rest ih =>
    change (if GeneralNominalSharedBudget.Holds after.erased head then GeneralNominalSharedBudget.remaining rest after.erased
      else GeneralNominalSharedBudget.remaining rest after.erased+1) <
      (if GeneralNominalSharedBudget.Holds before.erased head then GeneralNominalSharedBudget.remaining rest before.erased
      else GeneralNominalSharedBudget.remaining rest before.erased+1)
    rcases List.mem_cons.mp member with rfl | member
    · have tail := signatures_remaining_monotone rest step
      simp only [old,now,ite_true,ite_false]; omega
    · have tail := ih member
      by_cases was : GeneralNominalSharedBudget.Holds before.erased head
      · simp only [was,signature_monotone step was,ite_true]; exact tail
      · by_cases current : GeneralNominalSharedBudget.Holds after.erased head <;>
          simp only [was,current,ite_true,ite_false] <;> omega

end Yulang.GeneralNominalCenteredProgress
