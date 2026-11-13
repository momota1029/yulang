import Yulang.GeneralDictionaryReservedRefreshedClassification

/-! Exhaustive actual transition checks for the reserved fixture after nominal
refresh. This is a finite operational regression, not a general termination theorem. -/
namespace Yulang.GeneralDictionaryReservedRefreshedStability
set_option backward.isDefEq.respectTransparency false
open GeneralDictionaryFiniteObservedExampleReserved
open GeneralDictionaryFiniteObservedExampleReservedPositive
open GeneralDictionaryFiniteObservedExample (registry declaration checked)
open GeneralDictionaryReservedRefreshedEvidence GeneralDictionaryReservedNominalRefresh
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalSaturationState GeneralNominalSupport
open GeneralDeclarationExamples (roles)
open CommonNominalFullCarrier

private theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by have := i.isLt; omega
  rcases h with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

theorem sources_exact (id : Nat) : id ∈ GeneralNominalState.sources snapshot ↔ id = 0 ∨ id = 1 ∨ id = 2 := by
  constructor
  · intro member
    have bounded : (GeneralNominalState.sources snapshot).all (fun n => n < 3) = true := by decide +kernel
    have small := List.all_eq_true.mp bounded id member
    simp only [decide_eq_true_eq] at small
    omega
  · rintro (rfl | rfl | rfl) <;> decide +kernel

theorem all_known (id : Nat) (member : id ∈ GeneralNominalState.sources snapshot) :
    GeneralNominalState.Known snapshot id := by
  rcases (sources_exact id).mp member with rfl | rfl | rfl
  · exact ⟨(0 : Fin 3),rfl,Or.inr ⟨descriptor,rfl⟩⟩
  · exact ⟨(1 : Fin 3),rfl,Or.inl (by decide +kernel)⟩
  · exact output_known

theorem point_closed : GeneralNominalReobservationSteps.PointClosed snapshot := by
  intro slot desc recorded
  change (if slot = (1 : Fin 3) then none else some descriptor) = some desc at recorded
  split at recorded
  · cases recorded
  · cases Option.some.inj recorded
    intro parameter member
    change parameter ∈ [.type (1,1),.type (1,1),.type (1,1)] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at member
    subst parameter; rfl

theorem no_reobservation (revision : GeneralNominalReobservationSteps.Revision refreshed.current) :
    ¬ GeneralNominalReobservationSteps.Improves revision :=
  GeneralNominalReobservationSteps.pointClosed_no_revision point_closed revision

theorem sites_exact : refreshed.current.sites = [GeneralNominalDemandMerging.pointSite root] := by
  change start.current.sites ++ packet.children.map (GeneralNominalFeedbackSites.childSite packet) = _
  rw [GeneralDictionaryFiniteObservedExampleReservedPositive.packet_children]
  rfl

theorem edges_empty : refreshed.current.edges = [] := by
  change start.current.edges ++ packet.children.map _ = []
  rw [GeneralDictionaryFiniteObservedExampleReservedPositive.packet_children]
  rfl

theorem generated_only (focus : GeneralSourceDictionaries.Occurrence roles)
    (generated : Generated refreshed.current root focus) : focus = root := by
  induction generated with
  | root => rfl
  | child _ member ih => rw [edges_empty] at member; cases member
  | alias _ one two _ ih =>
    rw [sites_exact] at two
    have same := List.mem_singleton.mp two
    rw [same]; rfl

theorem raw_equal : GeneralNominalFeedbackSteps.RawEqual refreshed.current 2 0 := by
  intro model valid
  exact GeneralDictionaryReservedSuccessorBoundary.raw_equal model
    (GeneralNominalRefinements.models refines model valid)

private theorem int_not_nominal (name : Nat) (args : List Argument) :
    ¬ Subtype (.base .int) (nominal name args) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead name args.length) ⟨rfl,by simp⟩

private theorem not_equal01 : ¬ GeneralNominalFeedbackK2.Equal refreshed.current 0 1 := by
  intro equal
  have impossible := (equal positive refreshed_inhabited).2
  exact int_not_nominal _ _ impossible
private theorem not_equal12 : ¬ GeneralNominalFeedbackK2.Equal refreshed.current 1 2 := by
  intro equal
  have impossible := (equal positive refreshed_inhabited).1
  exact int_not_nominal _ _ impossible

theorem equality_closed (first last : Nat)
    (one : first ∈ GeneralNominalState.sources snapshot)
    (two : last ∈ GeneralNominalState.sources snapshot)
    (equal : GeneralNominalFeedbackK2.Equal refreshed.current first last) :
    GeneralNominalFeedbackSteps.RawEqual refreshed.current first last := by
  rcases (sources_exact first).mp one with rfl | rfl | rfl <;>
    rcases (sources_exact last).mp two with rfl | rfl | rfl
  · exact fun _ _ => ⟨subtype_refl _,subtype_refl _⟩
  · exact False.elim (not_equal01 equal)
  · exact fun m valid => (raw_equal m valid).symm
  · exact False.elim (not_equal01 (fun m valid => (equal m valid).symm))
  · exact fun _ _ => ⟨subtype_refl _,subtype_refl _⟩
  · exact False.elim (not_equal12 equal)
  · exact raw_equal
  · exact False.elim (not_equal12 (fun m valid => (equal m valid).symm))
  · exact fun _ _ => ⟨subtype_refl _,subtype_refl _⟩


theorem installable_committed (next : Packet roles)
    (enabled : GeneralNominalFeedbackSteps.Installable registry refreshed.current next) :
    GeneralNominalFeedbackSteps.Committed refreshed.current next := by
  obtain ⟨⟨sameRegistry,sameContext,present,visible,role,located,ready,selected,choices,merges,joint,compatible⟩,_,_⟩ := enabled
  have sameSite : next.site = GeneralNominalDemandMerging.pointSite root := by
    rw [sites_exact] at present
    exact List.mem_singleton.mp present
  have sameDeclaration : next.declaration = declaration := List.mem_singleton.mp visible
  rcases next with ⟨reg,ctx,site,decl,check,bounds⟩
  dsimp only at sameRegistry sameContext sameSite sameDeclaration
  subst reg; subst ctx; subst site; subst decl
  have sameBounds : bounds = [((1 : Fin 3),(1 : Fin 3))] :=
    Option.some.inj (located.symm.trans shape.located)
  subst bounds
  constructor
  · intro model valid
    exact GeneralDictionaryProvenanceScalarBranch.branch_models registry root root refreshed
      refreshed_reachable declaration check shape supported model valid
  · intro child member
    have empty : (Packet.children
        ⟨registry,refreshed.current.context,GeneralNominalDemandMerging.pointSite root,
          declaration,check,[((1 : Fin 3),(1 : Fin 3))]⟩) = [] :=
      GeneralDictionaryLinearLeaf.children_empty _ _ _ _ _ rfl _
    rw [empty] at member
    cases member

theorem stable : GeneralNominalValueSteps.Stable registry refreshed root := by
  intro focus generated after action
  have focusRoot := generated_only focus generated
  cases action with
  | administrative _ _ action =>
    cases action with
    | enqueue linked absent =>
      exact absent (GeneralNominalDemandMerging.pointSite root)
        (by rw [sites_exact]; exact List.mem_singleton_self _) focusRoot.symm
    | refresh context certificate id member unknown known => exact unknown (all_known id member)
    | equate first last one two equal novel => exact novel (equality_closed first last one two equal)
    | reobserve revision certificate improved => exact no_reobservation revision improved
  | install packet support enabled novel guard => exact novel (installable_committed packet enabled)
  | merge first last support one two same novel guard =>
    rw [sites_exact] at one two
    have firstRoot := List.mem_singleton.mp one
    have lastRoot := List.mem_singleton.mp two
    subst first; subst last
    exact novel (.refl _)

/-- The actual three-step history ends in a stable, classified, inhabited state.
The finite fixture is the scope; no general evidenceNode or executor is assumed. -/
theorem completed_reserved_run :
    B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root refreshed ∧
    GeneralNominalValueSteps.Stable registry refreshed root ∧
    B4TargetV3.Classify (GeneralNominalValueBoundary.boundary roles).toSourceBoundary
      registry refreshed root (.selected (.node declaration.id [])) ∧
    Models refreshed.current positive ∧ GeneralNominalState.Known snapshot 2 ∧
    ∀ model, Models refreshed.current model →
      GeneralDictionaryRecursiveEvidence.Evidence registry refreshed.current.context model root
        (.node declaration.id []) :=
  ⟨refreshed_reachable,stable,GeneralDictionaryReservedRefreshedClassification.classified,
    refreshed_inhabited,output_known,current_evidence⟩

end Yulang.GeneralDictionaryReservedRefreshedStability
