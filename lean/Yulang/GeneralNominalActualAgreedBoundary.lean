import Yulang.GeneralNominalActualAgreedLocal

/-! Structural V5 transfers for both provenance policies. Selection-to-action
agreement is conditional only where the explicit strict policy requires it. -/
namespace Yulang.GeneralNominalActualAgreedBoundary
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalActualInspectionSteps B4TargetV5
open GeneralNominalActualAgreedLocal
open CommonRoleOutermostResolver (Frontier Child Tree)

abbrev vocabulary := GeneralNominalActualAgreedLocal.vocabulary

variable {roles : Roles.RoleDecls} {defer : Bool} {gap : GapPredicate roles}

def boundary (defer : Bool) (gap : GapPredicate roles) : SourceBoundary (vocabulary roles) where
  toSourceBoundary := GeneralNominalLocalBoundary.complete (fields defer gap)
    (GeneralNominalActualBoundary.remaining roles)
  Initial := (GeneralNominalValueBoundary.boundary roles).Initial

abbrev pendingBoundary (roles : Roles.RoleDecls) := boundary true (ProvenanceGap (roles := roles))
abbrev completeBoundary (roles : Roles.RoleDecls) := boundary false (ProvenanceGap (roles := roles))

theorem local_correspondence (defer : Bool) (gap : GapPredicate roles)
    (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (frontier : Frontier (Occurrence roles)) :
    B4TargetV3.Local (boundary defer gap).toSourceBoundary registry state root frontier ↔
      Local defer gap registry state root frontier :=
  (GeneralNominalLocalBoundary.local_extension (GeneralNominalActualBoundary.remaining roles) frontier).symm

noncomputable def frontiers (defer : Bool) (gap : GapPredicate roles) : B4SkeletonV3.Frontiers (vocabulary roles) := by
  classical
  exact fun registry state =>
    { frontier := fun root => if checked : Checked registry then
        Classical.choose (GeneralNominalActualAgreedLocal.local_total defer gap registry checked state root) else .pending
      Local := B4TargetV3.Local (boundary defer gap).toSourceBoundary registry state }

theorem closure (registry : Registry) (_checked : (boundary defer gap).Checked registry)
    (state : Tracked roles) (root : Occurrence roles) (_reachable : Reachable (boundary defer gap) registry root state)
    (halted : ∀ after, ¬ (boundary defer gap).Step registry root state after) :
    (boundary defer gap).Stable registry state root ∧
      ∀ child, (boundary defer gap).Generated registry state root child → (boundary defer gap).Stable registry state child := by
  have stable : GeneralNominalActualBoundary.Stable registry state root := fun focus reached after action => halted after ⟨focus,reached,action⟩
  exact ⟨stable,fun child reached focus path => stable focus (generated_trans reached path)⟩

theorem stepModels (registry : Registry) (_checked : (boundary defer gap).Checked registry)
    (root : Occurrence roles) (before after : Tracked roles) (_reachable : Reachable (boundary defer gap) registry root before)
    (step : (boundary defer gap).Step registry root before after) :
    ∀ model, (boundary defer gap).Models after model → (boundary defer gap).Models before model :=
  GeneralNominalSharedSteps.step_models (step_shared step)

theorem localIdentity (registry : Registry) (state : Tracked roles) (root : Occurrence roles)
    (_reachable : Reachable (boundary defer gap) registry root state) :
    (frontiers defer gap registry state).Local = B4TargetV3.Local (boundary defer gap).toSourceBoundary registry state := rfl

theorem frontierLocal (registry : Registry) (checked : (boundary defer gap).Checked registry)
    (state : Tracked roles) (root : Occurrence roles) (_reachable : Reachable (boundary defer gap) registry root state)
    (demand : Occurrence roles) (frontier : Frontier (Occurrence roles)) :
    (frontiers defer gap registry state).frontier demand = frontier ↔
      B4TargetV3.Local (boundary defer gap).toSourceBoundary registry state demand frontier := by
  classical
  have valid := Classical.choose_spec (GeneralNominalActualAgreedLocal.local_total defer gap registry checked.2 state demand)
  change (if checked : Checked registry then Classical.choose (GeneralNominalActualAgreedLocal.local_total defer gap registry checked state demand) else .pending) = frontier ↔ _
  rw [dite_eq_left checked.2]
  constructor
  · intro same
    rw [same] at valid
    exact (local_correspondence defer gap registry state demand frontier).mpr valid
  · intro given
    exact GeneralNominalLocalBoundary.local_functional valid ((local_correspondence defer gap registry state demand frontier).mp given)

theorem dictionaryRefl (dictionary : CommonRoleOutermostResolver.Dictionary) :
    (boundary defer gap).DictionaryEquivalent dictionary dictionary := GeneralDictionaryPayloadOrder.equivalent_refl dictionary

theorem initialReorders (registry other : Registry) (_checked : (boundary defer gap).Checked registry)
    (_checkedOther : (boundary defer gap).Checked other) (order : (boundary defer gap).Reorders registry other)
    (state : Tracked roles) (root : Occurrence roles) (given : (boundary defer gap).Initial registry root state) :
    (boundary defer gap).Initial other root state := by
  obtain ⟨context,formed,same⟩ := given
  exact ⟨context,GeneralDictionaryInitialSource.source_reorders registry other order context root formed,same⟩

theorem reachable_iff_sourceFormed : Reachable (boundary defer gap) registry root state ↔ SourceFormed registry root state := by
  constructor
  · rintro ⟨start,⟨context,source,rfl⟩,path⟩
    induction path with
    | refl => exact .initial context source
    | tail path step ih => exact .update ih step
  · intro formed
    induction formed with
    | initial context source => exact ⟨_,⟨context,source,rfl⟩,.refl⟩
    | update formed step ih => exact reachable_step (boundary defer gap) ih step

def GapFree (gap : GapPredicate roles) : Prop :=
  ∀ registry, (boundary false gap).Checked registry → ∀ state root,
    Reachable (boundary false gap) registry root state → ∀ demand, ¬ gap registry state demand

theorem policies_agree_reachable (complete : GapFree gap)
    (checked : (boundary false gap).Checked registry)
    (reachable : Reachable (boundary false gap) registry root state) (demand : Occurrence roles) :
    B4TargetV3.Local (boundary true gap).toSourceBoundary registry state demand frontier ↔
      B4TargetV3.Local (boundary false gap).toSourceBoundary registry state demand frontier := by
  exact (local_correspondence true gap registry state demand frontier).trans
    ((policies_agree (complete registry checked state root reachable demand)).trans
      (local_correspondence false gap registry state demand frontier).symm)

theorem selected_committed
    (policy : defer = true ∨ ¬ gap registry state demand)
    (stable : (boundary defer gap).Stable registry state demand)
    (selected : B4TargetV3.Local (boundary defer gap).toSourceBoundary registry state demand (.selected key children)) :
    ∃ packet : Packet roles, packet.site.occurrence = demand ∧ packet.children = children ∧
      GeneralNominalFeedbackSteps.Committed state.current packet := by
  obtain ⟨packet,focus,_,cs,enabled | ⟨_,_,done⟩⟩ := selected_available policy
    ((local_correspondence defer gap registry state demand _).mp selected)
  · refine ⟨packet,focus,cs,?_⟩
    apply Classical.byContradiction
    intro novel
    obtain ⟨base,support,guard⟩ := enabled
    have action := GeneralNominalActualInspectionSteps.At.install packet support base novel guard
    rw [focus] at action
    exact stable demand (.root) _ action
  · exact ⟨packet,focus,cs,done⟩

theorem generatedChildren_of_policy
    (policy : ∀ registry, (boundary defer gap).Checked registry → ∀ state root,
      Reachable (boundary defer gap) registry root state → ∀ demand,
      defer = true ∨ ¬ gap registry state demand) :
    B4SkeletonV5.GeneratedChildren (boundary defer gap) := by
  intro registry checked state root demand key children reachable reached stable safe unique child member
  obtain ⟨packet,focus,cs,done⟩ := selected_committed
    (policy registry checked state root reachable demand) stable (.selected safe unique)
  have parent : Generated state.current root demand := reached.elim (fun same => same ▸ .root) id
  have edge : (demand,child) ∈ state.current.edges := by
    rw [← focus]
    exact done.2 child (cs ▸ member)
  exact .child parent edge

theorem generatedChildren_pending : B4SkeletonV5.GeneratedChildren (boundary true gap) :=
  generatedChildren_of_policy (fun _ _ _ _ _ _ => Or.inl rfl)

theorem generatedChildren_complete (complete : GapFree gap) :
    B4SkeletonV5.GeneratedChildren (boundary false gap) :=
  generatedChildren_of_policy (fun registry checked state root reachable demand =>
    Or.inr (complete registry checked state root reachable demand))

theorem whereAccessible_of_readback (registry : Registry) (checked : (boundary defer gap).Checked registry)
    (state : Tracked roles) (root : Occurrence roles)
    (readback : GeneralNominalCycleReadback.Readback roles registry state.current.context) :
    Acc (Child (B4TargetV3.Local (boundary defer gap).toSourceBoundary registry state)) root := by
  have accessible := GeneralNominalCycleReadback.whereAccessible checked.2 readback root
  induction accessible with
  | intro parent below ih =>
    constructor
    rintro child ⟨key,children,selected,member⟩
    exact ih child ⟨key,children,GeneralNominalFeedbackK2.selected_legacy
      (selected_old ((local_correspondence defer gap registry state parent _).mp selected)),member⟩

/-- A terminal state selector; diagnostics remain a separate supplied function. -/
noncomputable def terminalExecutor (diagnostics : Registry → Tracked roles → Occurrence roles → Tree) :
    B4TargetV3.Executor (vocabulary roles) := by
  classical
  exact ⟨fun registry state root =>
    let final := if terminal : ∃ final, B4Target.Steps (Step registry root) state final ∧
        ∀ next, ¬ Step registry root final next then Classical.choose terminal else state
    (final,diagnostics registry final root)⟩

theorem execution_of_accessible
    (accessible : Acc (fun next current => Step registry root current next) state) :
    B4Target.Steps ((boundary defer gap).Step registry root) state
      ((terminalExecutor diagnostics).run registry state root).1 := by
  classical
  have terminal := GeneralNominalActualBoundary.terminal_of_accessible accessible
  change B4Target.Steps (Step registry root) state (if h : ∃ final,
    B4Target.Steps (Step registry root) state final ∧ ∀ next, ¬ Step registry root final next
      then Classical.choose h else state)
  rw [dite_eq_left terminal]
  exact (Classical.choose_spec terminal).1

theorem halted_of_accessible
    (accessible : Acc (fun next current => Step registry root current next) state) :
    ∀ next, ¬ (boundary defer gap).Step registry root
      ((terminalExecutor diagnostics).run registry state root).1 next := by
  classical
  have terminal := GeneralNominalActualBoundary.terminal_of_accessible accessible
  change ∀ next, ¬ Step registry root (if h : ∃ final,
    B4Target.Steps (Step registry root) state final ∧ ∀ next, ¬ Step registry root final next
      then Classical.choose h else state) next
  rw [dite_eq_left terminal]
  exact (Classical.choose_spec terminal).2

theorem executor_exists
    (accessible : ∀ registry, (boundary defer gap).Checked registry → ∀ state root,
      Reachable (boundary defer gap) registry root state →
      Acc (fun next current => Step registry root current next) state)
    (diagnostics : Registry → Tracked roles → Occurrence roles → Tree) :
    ∃ executor : B4TargetV3.Executor (vocabulary roles),
      (∀ registry, (boundary defer gap).Checked registry → ∀ state root,
        Reachable (boundary defer gap) registry root state →
        B4Target.Steps ((boundary defer gap).Step registry root) state (executor.run registry state root).1) ∧
      (∀ registry, (boundary defer gap).Checked registry → ∀ state root,
        Reachable (boundary defer gap) registry root state →
        ∀ next, ¬ (boundary defer gap).Step registry root (executor.run registry state root).1 next) :=
  ⟨terminalExecutor diagnostics,
    fun registry checked state root reachable => execution_of_accessible (accessible registry checked state root reachable),
    fun registry checked state root reachable => halted_of_accessible (accessible registry checked state root reachable)⟩

end Yulang.GeneralNominalActualAgreedBoundary
