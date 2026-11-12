import Yulang.GeneralDictionaryJournalTree
import Yulang.GeneralDictionaryReachableBoundary
import Yulang.GeneralDictionaryReachableEvidenceInitial
import Yulang.GeneralDictionaryModeledJointGap

/-! Actual initial reachability does not force a stable terminal selection to
have a recorded packet: Committed is semantic, not journal membership. This is
not an evidence counterexample; the initial evidence theorem applies. -/
namespace Yulang.GeneralDictionaryReachableEvidenceUnrecorded
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates
open GeneralNominalRecursiveExamples (len lenRegistry len_checked)
open GeneralDictionaryModeledJointGap (context root)
open GeneralDeclarationExamples (roles)

abbrev state : State roles := initial context root

private theorem edge_to_raw_gap (first last : Nat)
    (edge : GeneralNominalFeedbackK2.Edge state first last) :
    GeneralNominalFeedbackK2.Edge GeneralDictionaryModeledJointGap.journal first last := by
  refine ⟨edge.1,edge.2.1,?_⟩
  rcases edge.2.2 with ⟨parent,child,structural,left,right⟩ | ⟨name,index,arguments⟩
  · exact Or.inl ⟨parent,child,structural,
      fun model valid => left model ((initial_models context root model).mpr valid.1),
      fun model valid => right model ((initial_models context root model).mpr valid.1)⟩
  · exact Or.inr ⟨name,index,fun model valid =>
      arguments model ((initial_models context root model).mpr valid.1)⟩

private theorem path_to_raw_gap (first last : Nat)
    (path : GeneralNominalFeedbackK2.Path state first last) :
    GeneralNominalFeedbackK2.Path GeneralDictionaryModeledJointGap.journal first last := by
  induction path with
  | nil => exact .nil _
  | cons edge _ ih => exact .cons (edge_to_raw_gap _ _ edge) ih

private theorem acyclic (source : Nat) : ¬ GeneralNominalFeedbackK2.Cycle state source := by
  rintro ⟨next,edge,path⟩
  exact GeneralDictionaryModeledJointGap.acyclic source
    ⟨next,edge_to_raw_gap _ _ edge,path_to_raw_gap _ _ path⟩

theorem selected : GeneralNominalFeedbackK2.Local lenRegistry state root (.selected 30 []) := by
  cases GeneralDictionaryModeledJointGap.selected with
  | selected safe unique =>
    refine .selected ⟨safe.1,?_,?_,safe.2.2.2⟩ unique
    · rintro (old | ⟨_,_,_,cycle,_⟩)
      · exact safe.2.1 (Or.inl old)
      · exact acyclic _ cycle
    · rintro (old | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
      · exact safe.2.2.1 (Or.inl old)
      · exact acyclic _ cycle

private theorem generated_only_root (focus : Occurrence roles)
    (generated : Generated state root focus) : focus = root := by
  induction generated with
  | root => rfl
  | child _ member _ => cases member
  | alias _ _ member _ _ =>
    exact congrArg GeneralNominalDemandMerging.Site.occurrence (List.mem_singleton.mp member)

private theorem installs_committed (packet : Packet roles)
    (same : packet.site.occurrence = root)
    (enabled : GeneralNominalFeedbackSteps.Installable lenRegistry state packet) :
    GeneralNominalFeedbackSteps.Committed state packet := by
  rcases packet with ⟨registry,ctx,site,declaration,checked,bounds⟩
  have reg := enabled.1.1
  have ctxt := enabled.1.2.1
  have visible := enabled.1.2.2.2.1
  have found := enabled.1.2.2.2.2.2.1
  dsimp only at reg ctxt visible found same
  subst registry
  change ctx = context at ctxt
  subst ctx
  have decl := List.mem_singleton.mp visible
  subst declaration
  rw [same] at found
  have located : arguments context root = some [(0,0)] := by decide +kernel
  have equal := Option.some.inj (located.symm.trans found)
  subst bounds
  constructor
  · intro model valid
    change BranchModels lenRegistry context site.occurrence len checked [(0,0)] model
    rw [same]
    exact GeneralDictionaryModeledJointGap.every_branch 30 checked model valid.1
  · intro child member
    change child ∈ GeneralNominalAllocation.children _ _ _ _ _ _ at member
    unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit at member
    simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
      len,GeneralDeclarationDemands.emitAll] at member
    obtain ⟨clause,present,_⟩ := member
    cases present

theorem stable : GeneralNominalFeedbackSteps.Stable lenRegistry state root := by
  intro focus generated after action
  have same := generated_only_root focus generated
  cases action with
  | enqueue focus _ absent => exact absent _ (List.mem_singleton_self _) same.symm
  | install packet enabled novel => exact novel (installs_committed packet same enabled)
  | merge first last one two _ novel =>
    have a := List.mem_singleton.mp one
    have b := List.mem_singleton.mp two
    subst first; subst last
    exact novel (.refl _)
  | refresh _ _ _ source member unknown _ =>
    exact unknown (GeneralDictionaryModeledJointGap.known source member)
  | equate _ first last _ _ equal novel =>
    exact novel (GeneralDictionaryReachableEvidenceInitial.initial_equal_is_raw context root first last equal)

theorem initial_source : GeneralNominalSourceFormation.InitialSource lenRegistry context root := by
  refine ⟨rfl,GeneralDictionaryModeledJointGap.prepared.1,GeneralDictionaryModeledJointGap.linked,?_,?_,rfl⟩
  · intro model valid index
    exact CommonNominalFullCarrier.subtype_refl _
  · intro source member
    simp [GeneralNominalState.sources,List.ofFn_succ] at member
    rcases member with h | h | h | h <;> simp [h]

/-- All premises of the tempting recorded-coverage claim hold, yet there are
no recorded packets whatsoever. Terminal evidence is already semantically true. -/
theorem stable_selected_without_record :
    GeneralNominalFeedbackSteps.SourceFormed lenRegistry root state ∧
    GeneralNominalFeedbackSteps.Stable lenRegistry state root ∧
    GeneralNominalFeedbackK2.Local lenRegistry state root (.selected 30 []) ∧
    Models state GeneralNominalExamples.model ∧ state.packets = [] :=
  ⟨.initial context initial_source,stable,selected,
    (initial_models context root _).mpr (GeneralNominalExamples.state_models true),rfl⟩

theorem no_recorded_focus : ¬ ∃ packet ∈ state.packets, packet.site.occurrence = root := by
  rintro ⟨packet,member,_⟩
  cases member

/-- The missing packet is harmless for evidence: every actual journal model
already validates the selected source-backed terminal dictionary. -/
theorem terminal_evidence (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models state model) :
    GeneralDictionaryRecursiveEvidence.Evidence lenRegistry state.context model root
      (.node 30 []) := by
  exact (GeneralDictionaryReachableEvidenceInitial.stable_initial_terminal_evidence
    lenRegistry context root 30 [] stable selected).2 model valid

/-- The example is reachable in the concrete V5 boundary, not only raw data. -/
theorem reachable : B4TargetV5.Reachable
    (GeneralDictionaryReachableBoundary.boundary roles) lenRegistry root state :=
  (GeneralDictionaryReachableBoundary.reachable_iff_sourceFormed lenRegistry root state).mpr
    stable_selected_without_record.1

/-- The actual finite-journal tree reader's coverage premise fails here. -/
theorem not_journal_covered : ¬ GeneralDictionaryJournalTree.Covered state root :=
  fun covered => no_recorded_focus (covered root .root)

/-- No universal stability-to-recorded-coverage bridge can hold, even with
actual initial reachability, a selected terminal and an inhabited journal. -/
theorem no_stable_selected_coverage : ¬ (∀ (s : State roles) (d : Occurrence roles),
    GeneralNominalFeedbackSteps.SourceFormed lenRegistry d s →
    GeneralNominalFeedbackSteps.Stable lenRegistry s d →
    GeneralNominalFeedbackK2.Local lenRegistry s d (.selected 30 []) →
    (∃ model, Models s model) → GeneralDictionaryJournalTree.Covered s d) := by
  intro coverage
  exact not_journal_covered (coverage state root stable_selected_without_record.1 stable selected
    ⟨_,stable_selected_without_record.2.2.2.1⟩)

end Yulang.GeneralDictionaryReachableEvidenceUnrecorded
