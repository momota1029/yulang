import Yulang.GeneralNominalRefreshForkClassification
import Yulang.GeneralNominalRefreshForkCycles
import Yulang.GeneralDictionaryReachableEvidenceInitial

/-! An inhabited one-step fork with two halted, observably different outcomes.
Both outcomes preserve exactly the initial models. The difference is caused by
which certified interval descriptor refresh records, not by a language choice. -/
namespace Yulang.GeneralNominalRefreshDivergence

open GeneralNominalRefreshFork GeneralNominalRefreshForkClassification GeneralNominalRefreshForkCycles
open GeneralDeclarations GeneralNominalRecursiveCandidates GeneralSourceDictionaries
open GeneralNominalSaturationState CommonRoleOutermostResolver
open GeneralDeclarationExamples (roles)

theorem point_selected : GeneralNominalFeedbackK2.Local registry (after false) root (.selected 90 []) := by
  refine .selected ⟨point_survivor.1,not_rootK2 false root,not_candidateK2 false registry root,?_⟩
    ⟨point_survivor,?_⟩
  · rintro (⟨_,d,visible,checked,_,_,unprepared⟩ | ⟨_,legacy⟩)
    · have same := List.mem_singleton.mp visible
      subst d
      exact unprepared point_prepared
    · rcases legacy with ⟨rootK2,_⟩ | ⟨candidateK2,_⟩
      · obtain ⟨_,_,_,slot,_,recurs⟩ := rootK2
        exact legacy_not_recursive false slot recurs
      · obtain ⟨_,_,_,_,_,_,_,_,visited,_,recurs⟩ := candidateK2
        exact legacy_not_recursive false visited.1 recurs
  · intro key children given
    have original := given
    obtain ⟨_,d,visible,_,identity,_⟩ := given
    have same := List.mem_singleton.mp visible
    subst d
    have same : key = 90 := identity.symm
    subst key
    exact ⟨rfl,survivor_children_functional registry registry_checked _ root 90 children [] original point_survivor⟩

theorem wide_pending : GeneralNominalFeedbackK2.Local registry (after true) root .pending :=
  .inspectionPending wide_inspection_pending.1 (Or.inl wide_inspection_pending)
    (not_rootK2 true root) (not_candidateK2 true registry root)

theorem generated_only_root (wide : Bool) (focus : Occurrence roles)
    (generated : Generated (after wide) root focus) : focus = root := by
  induction generated with
  | root => rfl
  | child _ member _ => cases member
  | alias _ _ member _ _ =>
    exact congrArg GeneralNominalDemandMerging.Site.occurrence (List.mem_singleton.mp member)

theorem installs_committed (wide : Bool) (packet : Packet roles)
    (same : packet.site.occurrence = root)
    (enabled : GeneralNominalFeedbackSteps.Installable registry (after wide) packet) :
    GeneralNominalFeedbackSteps.Committed (after wide) packet := by
  rcases packet with ⟨reg,ctx,site,d,checked,bounds⟩
  have regEq := enabled.1.1
  have ctxEq := enabled.1.2.1
  have visible := enabled.1.2.2.2.1
  have found := enabled.1.2.2.2.2.2.1
  have prepared := enabled.1.2.2.2.2.2.2.1
  dsimp only at regEq ctxEq visible found prepared same
  subst reg
  change ctx = context (some wide) at ctxEq
  subst ctx
  have declEq := List.mem_singleton.mp visible
  subst d
  rw [same] at found prepared
  have boundsEq := Option.some.inj ((located _).symm.trans found)
  subst bounds
  cases wide with
  | true => exact False.elim (wide_not_prepared checked prepared)
  | false =>
    constructor
    · intro m valid
      change BranchModels registry (context (some false)) site.occurrence declaration checked [(0,0)] m
      rw [same]
      exact point_branch checked m valid.1
    · intro child member
      change child ∈ GeneralNominalAllocation.children _ _ site.occurrence declaration checked _ at member
      rw [same,children_empty] at member
      cases member

theorem stable (wide : Bool) : GeneralNominalFeedbackSteps.Stable registry (after wide) root := by
  intro focus generated next action
  have same := generated_only_root wide focus generated
  cases action with
  | enqueue focus _ absent => exact absent _ (List.mem_singleton_self _) same.symm
  | install packet enabled novel => exact novel (installs_committed wide packet same enabled)
  | merge first last one two _ novel =>
    have a := List.mem_singleton.mp one
    have b := List.mem_singleton.mp two
    subst first; subst last
    exact novel (.refl _)
  | refresh _ next certificate source member unknown known =>
    exact no_refresh wide next certificate source member unknown known
  | equate _ first last _ _ equal novel =>
    exact novel (GeneralDictionaryReachableEvidenceInitial.initial_equal_is_raw (context (some wide)) root first last equal)

theorem halted (wide : Bool) : ∀ next, ¬ GeneralNominalFeedbackSteps.Step registry root (after wide) next :=
  GeneralNominalFeedbackSteps.stable_halted (stable wide)

theorem point_local : B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles)
    registry (after false) root (.selected 90 []) :=
  (GeneralNominalFeedbackBoundary.local_correspondence roles (GeneralDictionaryFeedbackEvidence.evidence roles)
    registry (after false) root _).mpr point_selected

theorem wide_local : B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles)
    registry (after true) root .pending :=
  (GeneralNominalFeedbackBoundary.local_correspondence roles (GeneralDictionaryFeedbackEvidence.evidence roles)
    registry (after true) root _).mpr wide_pending

theorem point_tree : Resolves (B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles)
    registry (after false)) root (.selected 90 []) := .selected point_local .nil

theorem wide_tree : Resolves (B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles)
    registry (after true)) root .pending := .pending wide_local

theorem different_local : ¬ (∀ d f,
    B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles) registry (after false) d f ↔
      B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles) registry (after true) d f) := by
  intro agreement
  have impossible := B4TargetV3.local_functional ((agreement root _).mp point_local) wide_local
  cases impossible

theorem different_diagnostic : ¬ B4TargetV3.SameDiagnostic (GeneralDictionaryFeedbackEvidence.boundary roles)
    (.selected 90 []) .pending := by
  intro same
  cases same.1

theorem child_accessible (wide : Bool) :
    Acc (Child (B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles) registry (after wide))) root := by
  refine Acc.intro root ?_
  rintro child ⟨key,children,selected,member⟩
  cases wide with
  | false =>
    have same := B4TargetV3.local_functional selected point_local
    cases same
    cases member
  | true =>
    have impossible := B4TargetV3.local_functional selected wide_local
    cases impossible

theorem point_reader : GeneralDictionaryFeedbackExecutor.diagnostic roles registry (after false) root = .selected 90 [] := by
  have exact := GeneralNominalFeedbackBoundary.frontierLocal roles
    (GeneralDictionaryFeedbackEvidence.evidence roles) registry ⟨rfl,registry_checked⟩ (after false)
  rw [GeneralDictionaryFeedbackExecutor.diagnostic_eq_resolve roles registry (after false) root exact (child_accessible false)]
  exact (resolve_tree_exact_of_frontier_exact _ exact root (child_accessible false) _).mpr point_tree

theorem wide_reader : GeneralDictionaryFeedbackExecutor.diagnostic roles registry (after true) root = .pending := by
  have exact := GeneralNominalFeedbackBoundary.frontierLocal roles
    (GeneralDictionaryFeedbackEvidence.evidence roles) registry ⟨rfl,registry_checked⟩ (after true)
  rw [GeneralDictionaryFeedbackExecutor.diagnostic_eq_resolve roles registry (after true) root exact (child_accessible true)]
  exact (resolve_tree_exact_of_frontier_exact _ exact root (child_accessible true) _).mpr wide_tree

theorem different_reader : ¬ B4TargetV3.SameDiagnostic (GeneralDictionaryFeedbackEvidence.boundary roles)
    (GeneralDictionaryFeedbackExecutor.diagnostic roles registry (after false) root)
    (GeneralDictionaryFeedbackExecutor.diagnostic roles registry (after true) root) := by
  rw [point_reader,wide_reader]
  exact different_diagnostic

theorem halted_trace_eq {state final : State roles}
    (stopped : ∀ next, ¬ GeneralNominalFeedbackSteps.Step registry root state next)
    (path : B4Target.Steps (GeneralNominalFeedbackSteps.Step registry root) state final) : final = state := by
  induction path with
  | refl => rfl
  | tail _ step ih =>
    rw [ih] at step
    exact False.elim (stopped _ step)

theorem no_observational_join : ¬ ∃ left right,
    B4Target.Steps (GeneralNominalFeedbackSteps.Step registry root) (after false) left ∧
    B4Target.Steps (GeneralNominalFeedbackSteps.Step registry root) (after true) right ∧
    (∀ d f, B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles) registry left d f ↔
      B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles) registry right d f) := by
  rintro ⟨left,right,leftPath,rightPath,agreement⟩
  have a := halted_trace_eq (halted false) leftPath
  have b := halted_trace_eq (halted true) rightPath
  subst left; subst right
  exact different_local agreement

/-- The fork is in the exact initial/reachable domain, uses a checked registry,
and differs already at the saturation root, which is always generated. -/
theorem reachable_halted_divergence :
    (GeneralDictionaryReachableBoundary.boundary roles).Checked registry ∧
    (GeneralDictionaryReachableBoundary.boundary roles).Initial registry root before ∧
    GeneralNominalFeedbackSteps.Step registry root before (after false) ∧
    GeneralNominalFeedbackSteps.Step registry root before (after true) ∧
    (∀ wide next, ¬ GeneralNominalFeedbackSteps.Step registry root (after wide) next) ∧
    (∀ wide m, Models (after wide) m ↔ Models before m) ∧
    Models before model ∧
    Resolves (B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles) registry (after false)) root (.selected 90 []) ∧
    Resolves (B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles) registry (after true)) root .pending ∧
    ¬ B4TargetV3.SameDiagnostic (GeneralDictionaryFeedbackEvidence.boundary roles) (.selected 90 []) .pending :=
  ⟨⟨rfl,registry_checked⟩,⟨context none,initial_source,rfl⟩,refresh_step false,refresh_step true,halted,
    same_models,initial_models,point_tree,wide_tree,different_diagnostic⟩

end Yulang.GeneralNominalRefreshDivergence
