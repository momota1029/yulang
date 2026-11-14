import Yulang.GeneralNominalCenteredHeadWFJoinLocal

set_option backward.isDefEq.respectTransparency false

/-! A stable selected ground source has no installation: materialization
cannot translate a multi-tag variant row despite constructor coverage.
The example has an inhabited journal and feasible chosen class effects. -/
namespace Yulang.GeneralNominalCenteredHeadWFJoinCounterexample
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadWFJoinSource
open GeneralNominalCenteredHeadWFJoinLocal

abbrev child : Occurrence roles := GeneralNominalFeedbackSites.clauseChild packet childClause
  (declaration_checked.signature.2.2.2 childClause (List.mem_singleton_self _))

theorem children_exact : children = [child] := by
  change packet.children = [child]
  unfold GeneralNominalSaturationState.Packet.children GeneralNominalAllocation.children
    GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
    GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,GeneralDictionaryEmissionPlans.occurrence,
    GeneralDeclarationDemands.childDemand,child,GeneralNominalFeedbackSites.clauseChild]
  apply (List.map_inj_right (f := Subtype.val) (fun _ _ same => Subtype.ext same)).mp
  simp only [List.attach_map_subtype_val,List.map_cons,List.map_nil,List.mergeSort_singleton]

theorem child_role : child.demand.role = 1 := rfl

theorem child_ne_root : child ≠ root := by
  intro equal
  have impossible := congrArg (fun demand : Occurrence roles => demand.demand.role) equal
  contradiction

theorem frame_unknown (candidate : Plan roles) (framed : Frame registry start.core root key candidate) :
    (GeneralNominalRecursiveCandidates.generated candidate.packet.registry candidate.packet.context
      candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.checked candidate.packet.bounds).unknown = true := by
  rcases candidate with ⟨⟨reg,ctx,site,decl,check,bounds⟩,input,inputEq⟩
  have regEq : reg = registry := framed.registry_eq
  have ctxEq : ctx = context := framed.context_eq
  have declEq : decl = declaration := List.mem_singleton.mp framed.visible
  have rootEq : site.occurrence = root := framed.occurrence_eq
  subst reg; subst ctx; subst decl
  have boundsEq : [(1,1)] = bounds := Option.some.inj framed.located
  subst bounds
  simpa only [rootEq] using generated_unknown

theorem no_extension (candidate : Plan roles) (framed : Frame registry start.core root key candidate) :
    ¬ GeneralNominalCenteredHeadStepAvailability.Extension registry start candidate := by
  rintro ⟨materialized,_⟩
  rw [frame_unknown candidate framed] at materialized
  contradiction

theorem no_install (candidate : Plan roles) (focus : candidate.packet.site.occurrence = root) (support) :
    ¬ Installable registry start candidate support := by
  intro enabled
  have unknown := frame_unknown candidate (focus ▸ enabled.frame)
  rw [enabled.materialized] at unknown
  contradiction

theorem generated_only_root (focus : Occurrence roles)
    (generated : GeneralNominalSaturationState.Generated start.core.erased.current root focus) : focus = root := by
  induction generated with
  | root => rfl
  | child prior member ih => cases member
  | alias prior one two same ih =>
    exact congrArg GeneralNominalDemandMerging.Site.occurrence (List.mem_singleton.mp two)

theorem stable : Stable registry start root := by
  intro focus generated after action
  have same := generated_only_root focus generated
  cases action with
  | administrative focus after action =>
    cases action with
    | enqueue linked absent => exact absent _ (List.mem_singleton_self _) same.symm
    | refresh context certificate source member unknown known =>
        exact unknown (GeneralNominalCenteredTerminalForkSource.all_known _ source member)
    | equate first last one two equal novel =>
        exact novel (GeneralDictionaryReachableEvidenceInitial.initial_equal_is_raw context root first last equal)
    | reobserve revision certificate improved =>
        exact GeneralNominalReobservationSteps.pointClosed_no_revision
          (GeneralNominalCenteredTerminalForkSource.point_closed false) revision improved
  | refresh focus context certificate source member unknown known =>
      exact unknown (GeneralNominalCenteredTerminalForkSource.all_known _ source member)
  | install candidate support enabled novel => exact no_install candidate same support enabled
  | merge first last support one two inputs novel guard =>
    have a := List.mem_singleton.mp one
    have b := List.mem_singleton.mp two
    subst first; subst last
    exact novel (.refl _)

theorem halted : ∀ after, ¬ Step registry root start after := by
  rintro after ⟨focus,generated,action⟩
  exact stable focus generated after action

theorem child_not_generated : ¬ GeneralNominalSaturationState.Generated start.core.erased.current root child :=
  fun generated => child_ne_root (generated_only_root child generated)

theorem not_committed : ¬ GeneralNominalFeedbackSteps.Committed start.core.erased.current packet := by
  intro committed
  have absent := committed.2 child (by rw [show packet.children = children from rfl,children_exact]; simp)
  cases absent

theorem selected_stable_unavailable :
    (GeneralNominalCenteredHeadWFBoundary.boundary roles).Checked registry ∧
    B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry root start ∧
    Stable registry start root ∧
    GeneralNominalCenteredHeadWFBoundary.Local registry start root (.selected 37 children) ∧
    (∃ assignment, GeneralNominalCenteredHeadStepEffects.Models start assignment ∧
      ChosenHead registry start.core root 37 assignment) ∧
    ¬ GeneralNominalCenteredHeadStepBoundary.OutputConflict registry start root 37 ∧
    ¬ GeneralNominalFeedbackSteps.Committed start.core.erased.current packet ∧
    (∀ candidate : Plan roles, candidate.packet.site.occurrence = root →
      ∀ support, ¬ Installable registry start candidate support) ∧
    (∀ after, ¬ Step registry root start after) :=
  ⟨⟨rfl,checked⟩,reachable,stable,selected,positive_baseline,no_output_conflict,not_committed,no_install,halted⟩

theorem not_generatedChildren : ¬ B4SkeletonV5.GeneratedChildren
    (B4TargetV6.prior (GeneralNominalCenteredHeadWFBoundary.boundary roles)) := by
  intro production
  exact child_not_generated (production registry ⟨rfl,checked⟩ start root root 37 children reachable
    (Or.inl rfl) stable safe unique child (by rw [children_exact]; simp))

/-- The same obstruction includes the V6 no-conflict selection premise. -/
theorem not_v6_selected_production : ¬ (∀ (r : Registry),
    (GeneralNominalCenteredHeadWFBoundary.boundary roles).Checked r →
    ∀ state root focus key children,
    B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) r root state →
    (focus = root ∨ GeneralNominalSaturationState.Generated state.core.erased.current root focus) →
    Stable r state focus → GeneralNominalCenteredHeadWFBoundary.Local r state focus (.selected key children) →
    ∀ child ∈ children, GeneralNominalSaturationState.Generated state.core.erased.current root child) := by
  intro production
  exact child_not_generated (production registry ⟨rfl,checked⟩ start root root 37 children reachable
    (Or.inl rfl) stable selected child (by rw [children_exact]; simp))

end Yulang.GeneralNominalCenteredHeadWFJoinCounterexample
