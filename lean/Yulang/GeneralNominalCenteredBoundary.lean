import Yulang.GeneralNominalCenteredSteps

/-! Local diagnostics with center-aware K2 and no provenance deferral.
Structural V5 fields hold for the centered kernel. Completion of local
selection into a guarded update remains a source-compilation obligation. -/
namespace Yulang.GeneralNominalCenteredBoundary
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenteredSteps
open GeneralNominalCenters
open B4TargetV5
open CommonRoleOutermostResolver (Frontier)

abbrev oldFields (roles : Roles.RoleDecls) := GeneralNominalFeedbackK2.fields roles

def vocabulary (roles : Roles.RoleDecls) : B4Target.Vocabulary where
  Registry := Registry
  State := State roles
  Demand := Occurrence roles
  Model := GeneralNominalCommonBridge.Assignment

def fields (roles : Roles.RoleDecls) : GeneralNominalLocalBoundary.Fields (vocabulary roles) where
  Checked := (oldFields roles).Checked
  Models := Models
  RootPending := fun registry state => (oldFields roles).RootPending registry state.erased.current
  RootK2 := fun registry state root => (oldFields roles).RootK2 registry state.erased.current root ∨ RootCycle state root
  CandidateK2 := fun registry state root => (oldFields roles).CandidateK2 registry state.erased.current root ∨ CandidateCycle registry state root
  InspectionPending := fun registry state root =>
    (oldFields roles).InspectionPending registry state.erased.current root ∨
      ¬ DecisionGuard registry state root
  Survivor := fun registry state => (oldFields roles).Survivor registry state.erased.current
  Reorders := (oldFields roles).Reorders
  DictionaryEquivalent := (oldFields roles).DictionaryEquivalent

def remaining (roles : Roles.RoleDecls) : GeneralNominalLocalBoundary.Remaining (vocabulary roles) where
  Step := Step
  Stable := Stable
  Generated := fun _ state => GeneralNominalSaturationState.Generated state.erased.current
  Evidence := fun registry state => GeneralDictionaryFeedbackEvidence.evidence roles registry state.erased.current

def boundary (roles : Roles.RoleDecls) : SourceBoundary (vocabulary roles) where
  toSourceBoundary := GeneralNominalLocalBoundary.complete (fields roles) (remaining roles)
  Initial := InitialSource

abbrev Local (registry : Registry) (state : State roles) := GeneralNominalLocalBoundary.Local (fields roles) registry state

theorem local_correspondence (registry : Registry) (state : State roles) (root : Occurrence roles)
    (frontier : Frontier (Occurrence roles)) :
    B4TargetV3.Local (boundary roles).toSourceBoundary registry state root frontier ↔ Local registry state root frontier :=
  (GeneralNominalLocalBoundary.local_extension (remaining roles) frontier).symm

variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles} {root : Occurrence roles}

theorem local_functional (one : Local registry state root first) (two : Local registry state root last) : first = last :=
  GeneralNominalLocalBoundary.local_functional one two

theorem local_total (registry : Registry) (checked : Checked registry) (state : State roles) (root : Occurrence roles) :
    ∃ frontier, Local registry state root frontier :=
  GeneralNominalLocalBoundary.local_total (fun key first last one two =>
    GeneralNominalRecursiveCandidates.survivor_children_functional registry checked state.erased.current.context root key first last one two)

theorem survivors_unchanged (registry : Registry) (state : State roles) (root : Occurrence roles) (key children) :
    (fields roles).Survivor registry state root key children ↔
      (GeneralNominalActualAgreedLocal.fields false (fun _ _ _ => False)).Survivor registry state.erased root key children := Iff.rfl

theorem root_cycle_rejected (known : ¬ (fields roles).RootPending registry state root)
    (cycle : RootCycle state root) : Local registry state root .rejected :=
  .rejected ⟨known,Or.inl (Or.inr cycle)⟩

theorem inspected_cycle_rejected (known : ¬ (fields roles).RootPending registry state root)
    (cycle : CandidateCycle registry state root) : Local registry state root .rejected :=
  .rejected ⟨known,Or.inr (Or.inl (Or.inr cycle))⟩

theorem pending_exact : Local registry state root .pending ↔
    (fields roles).RootPending registry state root ∨
      (¬ (fields roles).RootPending registry state root ∧
       ¬ (fields roles).RootK2 registry state root ∧ ¬ (fields roles).CandidateK2 registry state root ∧
       ((oldFields roles).InspectionPending registry state.erased.current root ∨
        ¬ DecisionGuard registry state root)) := by
  constructor
  · intro pending
    cases pending with
    | pending unknown => exact Or.inl unknown
    | inspectionPending known deferred root candidate => exact Or.inr ⟨known,root,candidate,deferred⟩
  · rintro (unknown | ⟨known,root,candidate,deferred⟩)
    · exact .pending unknown
    · exact .inspectionPending known deferred root candidate

theorem selected_of_old
    (old : GeneralNominalFeedbackK2.Local registry state.erased.current root (.selected key children))
    (acyclic : ∀ origin, ¬ Cyclic state origin)
    (justified : DecisionGuard registry state root) :
    Local registry state root (.selected key children) := by
  cases old with
  | selected safe unique =>
    refine .selected ⟨safe.1,?_,?_,?_⟩ unique
    · rintro (old | ⟨site,_,_,index,cycle⟩)
      · exact safe.2.1 old
      · exact acyclic _ cycle
    · rintro (old | ⟨plan,_,_,_,_,_,_,_,_,entry,_,cycle⟩)
      · exact safe.2.2.1 old
      · exact acyclic _ cycle
    · exact fun deferred => deferred.elim safe.2.2.2 (fun absent => absent justified)

def Installable (registry : Registry) (state : State roles) (plan : Plan roles) : Prop :=
  GeneralNominalFeedbackSteps.Installable registry state.erased.current plan.packet ∧
    ∃ support, PacketGuard state plan support

theorem installable_selected (enabled : Installable registry state plan) :
    Local registry state plan.packet.site.occurrence (.selected plan.packet.declaration.id plan.packet.children) := by
  obtain ⟨base,support,guard⟩ := enabled
  have justified : DecisionGuard registry state plan.packet.site.occurrence := by
    simpa only [DecisionGuard,base.1.1,base.1.2.1] using guard.2.2.1
  have cycles := guard.2.2.2.2.2.1
  have candidate : ¬ CandidateCycle registry state plan.packet.site.occurrence := by
    simpa only [base.1.1] using cycles.2
  cases base.2.1 with
  | selected safe unique =>
      refine .selected ⟨safe.1,?_,?_,?_⟩ unique
      · exact fun cycle => cycle.elim safe.2.1 cycles.1
      · exact fun cycle => cycle.elim safe.2.2.1 candidate
      · exact fun deferred => deferred.elim safe.2.2.2 (fun absent => absent justified)

/-- This exact comparison exposes the old adapter's residual gap. Emptying its
provenance parameter alone does not remove that residual pending branch. -/
theorem agrees_with_empty_gap {frontier : Frontier (Occurrence roles)}
    (rootCycles : ¬ RootCycle state root)
    (candidateCycles : CandidateCycle registry state root ↔
      GeneralNominalActualAgreedLocal.InspectedCycle registry state.erased root)
    (unblocked : ¬ GeneralNominalActualAgreedLocal.Blocked registry state.erased root)
    (decisions : DecisionGuard registry state root ↔ GeneralNominalSharedSupport.DecisionGuard registry state.erased root) :
    Local registry state root frontier ↔
      GeneralNominalActualAgreedLocal.Local false (fun _ _ _ => False) registry state.erased root frontier := by
  have rp : (fields roles).RootPending registry state root ↔
      (GeneralNominalActualAgreedLocal.fields false (fun _ _ _ => False)).RootPending registry state.erased root := Iff.rfl
  have rk : (fields roles).RootK2 registry state root ↔
      (GeneralNominalActualAgreedLocal.fields false (fun _ _ _ => False)).RootK2 registry state.erased root := by
    change (_ ∨ RootCycle state root) ↔ _
    simp only [rootCycles,or_false]
    rfl
  have ck : (fields roles).CandidateK2 registry state root ↔
      (GeneralNominalActualAgreedLocal.fields false (fun _ _ _ => False)).CandidateK2 registry state.erased root :=
    or_congr Iff.rfl candidateCycles
  have ip : (fields roles).InspectionPending registry state root ↔
      (GeneralNominalActualAgreedLocal.fields false (fun _ _ _ => False)).InspectionPending registry state.erased root := by
    change (_ ∨ _) ↔ (_ ∨ _ ∨ (_ ∧ ¬ False) ∨ (false = true ∧ _ ∧ False))
    simp only [unblocked,false_and,and_false,or_false]
    exact or_congr Iff.rfl (not_congr decisions)
  have safe : GeneralNominalLocalBoundary.SafeKnown (fields roles) registry state root ↔
      GeneralNominalLocalBoundary.SafeKnown (GeneralNominalActualAgreedLocal.fields false (fun _ _ _ => False)) registry state.erased root :=
    and_congr (not_congr rp) (and_congr (not_congr rk) (and_congr (not_congr ck) (not_congr ip)))
  have rejected : GeneralNominalLocalBoundary.RejectReason (fields roles) registry state root ↔
      GeneralNominalLocalBoundary.RejectReason (GeneralNominalActualAgreedLocal.fields false (fun _ _ _ => False)) registry state.erased root :=
    and_congr (not_congr rp) (or_congr rk (or_congr ck (and_congr (not_congr ip) Iff.rfl)))
  constructor
  · intro given
    exact GeneralNominalLocalBoundary.Local.casesOn (b := fields roles) given
      (motive := fun f _ => GeneralNominalActualAgreedLocal.Local false (fun _ _ _ => False) registry state.erased root f)
      (fun h => .pending (rp.mp h))
      (fun a b c d => .inspectionPending ((not_congr rp).mp a) (ip.mp b) ((not_congr rk).mp c) ((not_congr ck).mp d))
      (fun h => .rejected (rejected.mp h))
      (fun {_ _ _ _} h a b c => .ambiguous (safe.mp h) a b c)
      (fun {_ _} h unique => .selected (safe.mp h) unique)
  · intro given
    exact GeneralNominalLocalBoundary.Local.casesOn (b := GeneralNominalActualAgreedLocal.fields false (fun _ _ _ => False)) given
      (motive := fun f _ => Local registry state root f)
      (fun h => .pending (rp.mpr h))
      (fun a b c d => .inspectionPending ((not_congr rp).mpr a) (ip.mpr b) ((not_congr rk).mpr c) ((not_congr ck).mpr d))
      (fun h => .rejected (rejected.mpr h))
      (fun {_ _ _ _} h a b c => .ambiguous (safe.mpr h) a b c)
      (fun {_ _} h unique => .selected (safe.mpr h) unique)

noncomputable def frontiers (roles : Roles.RoleDecls) : B4SkeletonV3.Frontiers (vocabulary roles) := by
  classical
  exact fun registry state =>
    { frontier := fun root => if checked : Checked registry then Classical.choose (local_total registry checked state root) else .pending
      Local := B4TargetV3.Local (boundary roles).toSourceBoundary registry state }

theorem closure (registry : Registry) (_checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles) (_reachable : Reachable (boundary roles) registry root state)
    (halted : ∀ after, ¬ (boundary roles).Step registry root state after) :
    (boundary roles).Stable registry state root ∧
      ∀ child, (boundary roles).Generated registry state root child → (boundary roles).Stable registry state child := by
  have stable : Stable registry state root := fun focus reached after action => halted after ⟨focus,reached,action⟩
  exact ⟨stable,fun child reached focus path => stable focus (GeneralNominalSaturationState.generated_trans reached path)⟩

theorem stepModels (registry : Registry) (_checked : (boundary roles).Checked registry)
    (root : Occurrence roles) (before after : State roles) (_reachable : Reachable (boundary roles) registry root before)
    (step : (boundary roles).Step registry root before after) :
    ∀ model, (boundary roles).Models after model → (boundary roles).Models before model := step_models step

theorem localIdentity (registry : Registry) (state : State roles) (root : Occurrence roles)
    (_reachable : Reachable (boundary roles) registry root state) :
    (frontiers roles registry state).Local = B4TargetV3.Local (boundary roles).toSourceBoundary registry state := rfl

theorem frontierLocal (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles) (_reachable : Reachable (boundary roles) registry root state)
    (demand : Occurrence roles) (frontier : Frontier (Occurrence roles)) :
    (frontiers roles registry state).frontier demand = frontier ↔
      B4TargetV3.Local (boundary roles).toSourceBoundary registry state demand frontier := by
  classical
  have valid := Classical.choose_spec (local_total registry checked.2 state demand)
  change (if checked : Checked registry then Classical.choose (local_total registry checked state demand) else .pending) = frontier ↔ _
  rw [dite_eq_left checked.2]
  constructor
  · intro same
    rw [same] at valid
    exact (local_correspondence registry state demand frontier).mpr valid
  · intro given
    exact local_functional valid ((local_correspondence registry state demand frontier).mp given)

theorem dictionaryRefl (dictionary : CommonRoleOutermostResolver.Dictionary) :
    (boundary roles).DictionaryEquivalent dictionary dictionary := GeneralDictionaryPayloadOrder.equivalent_refl dictionary

theorem initialReorders (registry other : Registry) (_checked : (boundary roles).Checked registry)
    (_checkedOther : (boundary roles).Checked other) (order : (boundary roles).Reorders registry other)
    (state : State roles) (root : Occurrence roles) (given : (boundary roles).Initial registry root state) :
    (boundary roles).Initial other root state := by
  obtain ⟨context,site,formed,rootSite,point,same⟩ := given
  exact ⟨context,site,GeneralDictionaryInitialSource.source_reorders registry other order context root formed,rootSite,point,same⟩

end Yulang.GeneralNominalCenteredBoundary
