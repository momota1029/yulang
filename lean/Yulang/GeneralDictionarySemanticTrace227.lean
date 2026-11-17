import Yulang.GeneralDictionaryOriginJournal227

/-! A finite semantic footprint is reconstructed along the actual trace.
Refresh and administrative actions add no names; installation/merge add the
explicit227 deltas. This is event provenance, not an ownership/Overlap proof. -/
namespace Yulang.GeneralDictionarySemanticTrace227
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionarySemanticDelta223 (Depends)
open GeneralDictionaryOriginJournal227 (installDelta mergeDelta)
variable {roles : Roles.RoleDecls}

/-- Classify the actual operation, retaining its operational premises. -/
inductive Contribution (registry : Registry) (root : Occurrence roles) :
    State roles → State roles → List Nat → Prop
  | administrative {before after focus}
      (generated : GeneralNominalSaturationState.Generated before.core.erased.current root focus)
      (action : Administrative before focus after) : Contribution registry root before after []
  | refresh {before focus context source}
      (generated : GeneralNominalSaturationState.Generated before.core.erased.current root focus)
      (certificate : GeneralNominalCenteredHeadMatStepRefresh.Refresh before context)
      (member : source ∈ GeneralNominalState.sources before.core.erased.current.context.state)
      (unknown : ¬ GeneralNominalState.Known before.core.erased.current.context.state source)
      (known : GeneralNominalState.Known context.state source) :
      Contribution registry root before (refresh before context) []
  | install {before} (effect : Effect roles)
      (generated : GeneralNominalSaturationState.Generated before.core.erased.current root effect.plan.packet.site.occurrence)
      (enabled : Installable registry before effect) (novel : ¬ Committed before effect.plan) :
      Contribution registry root before (install before effect) (installDelta before effect)
  | merge {before} (first last : Site roles)
      (generated : GeneralNominalSaturationState.Generated before.core.erased.current root first.occurrence)
      (one : first ∈ before.core.sites) (two : last ∈ before.core.sites)
      (same : SameInputs (Models before) first last)
      (novel : ¬ GeneralNominalSaturationState.Alias before.core.erased.current first.occurrence.identity last.occurrence.identity) :
      Contribution registry root before (merge before first last) (mergeDelta before first last)

theorem Contribution.step (event : Contribution registry root before after delta) :
    Step registry root before after := by
  cases event with
  | administrative generated action => exact ⟨_,generated,.administrative action⟩
  | refresh generated certificate member unknown known => exact ⟨_,generated,.refresh _ _ certificate _ member unknown known⟩
  | install effect generated enabled novel => exact ⟨_,generated,.install effect enabled novel⟩
  | merge first last generated one two same novel => exact ⟨_,generated,.merge first last one two same novel⟩

theorem classify (step : Step registry root before after) :
    ∃ delta, Contribution registry root before after delta := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | administrative action => exact ⟨[],.administrative generated action⟩
  | refresh focus context certificate source member unknown known => exact ⟨[],.refresh generated certificate member unknown known⟩
  | install effect enabled novel => exact ⟨_,.install effect generated enabled novel⟩
  | merge first last one two same novel => exact ⟨_,.merge first last generated one two same novel⟩

theorem Contribution.depends (event : Contribution registry root before after delta)
    (path : B4Target.Steps (Step registry root) (GeneralNominalCenteredHeadMatStepJournal.initial context root) before)
    (old : Depends before pool) : Depends after (pool ++ delta) := by
  cases event with
  | administrative generated action =>
      simpa only [List.append_nil,Depends] using
        GeneralDictionaryAdministrativeSemanticSupport222.reachable_administrative_depends path generated action old
  | refresh generated certificate member unknown known =>
      simp only [List.append_nil]
      intro a b same
      exact (GeneralNominalCenteredHeadMatStepRefresh.refresh_models certificate).trans
        ((old a b same).trans (GeneralNominalCenteredHeadMatStepRefresh.refresh_models certificate).symm)
  | install effect generated enabled novel => exact GeneralDictionaryOriginJournal227.install_depends path enabled old
  | merge first last generated one two same novel => exact GeneralDictionaryOriginJournal227.merge_depends path old

def initialSources (context : GeneralNominalCandidates.Context) (root : Occurrence roles) : List Nat :=
  GeneralDictionaryDefaultRawSupport213.sources context.state ++
    GeneralNominalCenteredFrame179.siteSources (rootSite context.state.seed root)

inductive Footprint (registry : Registry) (context : GeneralNominalCandidates.Context)
    (root : Occurrence roles) : State roles → List Nat → Prop
  | initial : Footprint registry context root (GeneralNominalCenteredHeadMatStepJournal.initial context root)
      (initialSources context root)
  | tail {before after pool delta} : Footprint registry context root before pool →
      Contribution registry root before after delta → Footprint registry context root after (pool ++ delta)

theorem Footprint.path (trace : Footprint registry context root state pool) :
    B4Target.Steps (Step registry root) (GeneralNominalCenteredHeadMatStepJournal.initial context root) state := by
  induction trace with
  | initial => exact .refl
  | tail trace event ih => exact .tail ih event.step

theorem Footprint.depends (trace : Footprint registry context root state pool) :
    Depends state pool := by
  induction trace with
  | initial =>
      intro a b same
      rw [initial_models,initial_models]
      exact and_congr
        (GeneralDictionaryDefaultRawSupport213.models_iff _ (fun n h => same n (List.mem_append_left _ h)))
        (GeneralNominalCenteredFrame179.site_iff _ (fun n h => same n (List.mem_append_right _ h)))
  | tail trace event ih => exact event.depends trace.path ih

theorem from_path (path : B4Target.Steps (Step registry root) (GeneralNominalCenteredHeadMatStepJournal.initial context root) state) :
    ∃ pool, Footprint registry context root state pool := by
  induction path with
  | refl => exact ⟨_,.initial⟩
  | tail path step ih =>
      obtain ⟨pool,trace⟩ := ih
      obtain ⟨delta,event⟩ := classify step
      exact ⟨pool ++ delta,.tail trace event⟩

/-- A protected name absent initially has an actual contributing step on the
trace. Merely reserving it or refreshing a cache is not such a contribution. -/
theorem Footprint.introduced (trace : Footprint registry context root state pool)
    (absent : name ∉ initialSources context root)
    (present : name ∈ pool) :
    ∃ before after delta,
      B4Target.Steps (Step registry root) (GeneralNominalCenteredHeadMatStepJournal.initial context root) before ∧
      Contribution registry root before after delta ∧ name ∈ delta ∧
      B4Target.Steps (Step registry root) after state := by
  induction trace with
  | initial => exact False.elim (absent present)
  | @tail before after pool delta trace event ih =>
      rcases List.mem_append.mp present with old | new
      · obtain ⟨start,finish,added,path,contribution,member,suffix⟩ := ih old
        exact ⟨start,finish,added,path,contribution,member,.tail suffix event.step⟩
      · exact ⟨before,after,delta,trace.path,event,new,.refl⟩

/-- The provenance split is exact; no new source comes from an administrative
or cache-only step. It does not say installation deltas contain only owned names. -/
theorem Contribution.nonempty_kind (event : Contribution registry root before after delta)
    (member : name ∈ delta) :
    (∃ effect : Effect roles, after = GeneralNominalCenteredHeadMatStepJournal.install before effect ∧ name ∈ installDelta before effect) ∨
    (∃ first last : Site roles, after = GeneralNominalCenteredHeadMatStepJournal.merge before first last ∧ name ∈ mergeDelta before first last) := by
  cases event with
  | administrative | refresh => cases member
  | install effect generated enabled novel => exact Or.inl ⟨effect,rfl,member⟩
  | merge first last generated one two same novel => exact Or.inr ⟨first,last,rfl,member⟩
/-- The earliest contributing event has no protected occurrence beforehand. -/
theorem Footprint.first_introduced (trace : Footprint registry context root state pool)
    (absent : name ∉ initialSources context root)
    (present : name ∈ pool) :
    ∃ before after prior delta,
      Footprint registry context root before prior ∧ name ∉ prior ∧
      Contribution registry root before after delta ∧ name ∈ delta ∧
      B4Target.Steps (Step registry root) after state := by
  classical
  induction trace with
  | initial => exact False.elim (absent present)
  | @tail before after pool delta trace event ih =>
      by_cases old : name ∈ pool
      · obtain ⟨start,finish,prior,added,history,missing,contribution,member,suffix⟩ := ih old
        exact ⟨start,finish,prior,added,history,missing,contribution,member,.tail suffix event.step⟩
      · exact ⟨before,after,pool,delta,trace,old,event,(List.mem_append.mp present).resolve_left old,.refl⟩

theorem initial_fresh_absent
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (notRootCenter : purpose ≠ 7) :
    fresh context.state.seed invocation declaration purpose owner position ∉ initialSources context root := by
  intro member
  have above := GeneralNominalIdentities.source_above_seed context.state.seed
    (invocation,declaration,purpose,owner,position)
  change context.state.seed < fresh context.state.seed invocation declaration purpose owner position at above
  rcases List.mem_append.mp member with raw | site
  · have below := source.below_seed _ (GeneralDictionaryDefaultRawSupport213.subset context.state raw)
    omega
  · obtain ⟨xs,present,within⟩ := List.mem_flatten.mp site
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp present
    simp only [List.mem_cons,List.not_mem_nil,or_false] at within
    have low := source.below_seed _ (source.linked.1 index).1
    have high := source.below_seed _ (source.linked.1 index).2
    rcases within with lower | upper | center
    · change _ = (root.demand.arguments index).1 at lower
      omega
    · change _ = (root.demand.arguments index).2 at upper
      omega
    · by_cases point : (root.demand.arguments index).1 = (root.demand.arguments index).2
      · rw [point_center _ _ _ point] at center
        omega
      · simp only [rootSite,point,ite_false] at center
        exact GeneralNominalCenteredAllocation.fresh_namespaces notRootCenter center

/-- Allocated identities outside root-center purpose7, including p0/p1, first enter a
semantic footprint at an actual install or merge, never at a cache refresh. -/
theorem Footprint.fresh_first (trace : Footprint registry context root state pool)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (notRootCenter : purpose ≠ 7)
    (present : fresh context.state.seed invocation declaration purpose owner position ∈ pool) :
    ∃ before after prior delta,
      Footprint registry context root before prior ∧
      fresh context.state.seed invocation declaration purpose owner position ∉ prior ∧
      Contribution registry root before after delta ∧
      fresh context.state.seed invocation declaration purpose owner position ∈ delta ∧
      B4Target.Steps (Step registry root) after state :=
  trace.first_introduced (initial_fresh_absent source notRootCenter) present
end Yulang.GeneralDictionarySemanticTrace227
