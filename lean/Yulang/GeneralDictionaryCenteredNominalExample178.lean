import Yulang.GeneralDictionaryNominalPairExample178
import Yulang.GeneralDictionaryCenteredNominal178

/-! A modeled centered Candidate with both a good and a bad fixed assignment.
The nonpoint root is not a ground-boundary initial state. Stability is not
claimed, so this does not refute the exact G EvidenceNode obligation. -/
namespace Yulang.GeneralDictionaryCenteredNominalExample178
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralDictionaryNominalPair178
open GeneralDictionaryNominalPairExample178 (context state declaration registry shape assignment)

abbrev root : Occurrence roles := ⟨GeneralDictionaryNominalPairExample178.root.identity,⟨0,fun _ => (0,1),[],by simp⟩⟩
abbrev site : Site roles := ⟨root,fun _ => 0⟩
abbrev start := initialAt context site
abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite root,declaration,GeneralDictionaryNominalPairExample178.declaration_checked,[(0,1)]⟩
abbrev plan : Plan roles := ⟨packet,site,rfl⟩

theorem inhabited (good : Bool) : Models start (assignment good) := by
  apply (initialAt_models context site _).mpr
  exact ⟨GeneralDictionaryNominalPairExample178.source_models good,fun _ => ⟨CommonNominalFullCarrier.subtype_refl _,GeneralDictionaryNominalPairExample178.endpoint_order good⟩⟩

theorem located : arguments context root = some [(shape.lower,shape.upper)] := by decide +kernel

theorem branch_good : packet.Holds (assignment true) := by
  apply (branch_models_iff_merges context registry root declaration GeneralDictionaryNominalPairExample178.declaration_checked shape rfl rfl
    _ (GeneralDictionaryNominalPairExample178.source_models true) (GeneralDictionaryNominalPairExample178.endpoint_order true)).mpr
  change PresenceNormalForm.All CommonNominalFullCarrier.model _
    (GeneralNominalAllocation.merges state registry GeneralDictionaryNominalPairExample178.root.identity declaration
      (bindings state (report context declaration [(0,1)])))
  rw [GeneralDictionaryNominalPairExample178.report_captures]
  exact GeneralDictionaryNominalPairExample178.merge_good

theorem branch_bad : ¬ packet.Holds (assignment false) := by
  intro branch
  have merged := (branch_models_iff_merges context registry root declaration GeneralDictionaryNominalPairExample178.declaration_checked shape rfl rfl
    _ (GeneralDictionaryNominalPairExample178.source_models false) (GeneralDictionaryNominalPairExample178.endpoint_order false)).mp branch
  change PresenceNormalForm.All CommonNominalFullCarrier.model _
    (GeneralNominalAllocation.merges state registry GeneralDictionaryNominalPairExample178.root.identity declaration
      (bindings state (report context declaration [(0,1)]))) at merged
  rw [GeneralDictionaryNominalPairExample178.report_captures] at merged
  exact GeneralDictionaryNominalPairExample178.merge_bad merged

theorem metadata : Metadata registry context := by
  refine ⟨rfl,?_⟩
  intro name primitive recorded
  by_cases two : name = 2
  · subst name
    have same : GeneralCandidateInspection.Primitive.scalar .int = primitive := Option.some.inj recorded
    subst primitive
    exact ⟨⟨[],2⟩,rfl,rfl⟩
  · simp [GeneralNominalExamples.interpretation,two] at recorded

theorem prepared : Prepared registry context root declaration packet.checked := by
  refine ⟨metadata,?_,?_,[(0,1)],located,?_,?_,assignment true,branch_good⟩
  · constructor
    · intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
    · intro output member; cases member
  · intro key _ present
    have below : GeneralNominalAllocation.source state registry root.identity key ≤ state.seed := by
      simp [GeneralNominalState.sources,List.ofFn_succ] at present
      rcases present with h | h | h | h | h | h | h | h <;> rw [h] <;> decide +kernel
    exact False.elim (GeneralNominalAllocation.source_initial_fresh state registry root.identity key _ below rfl)
  · change Finished (report context declaration [(shape.lower,shape.upper)])
    rw [report_exact context declaration shape.lower shape.upper shape.different shape.left shape.right
      shape.recorded shape.recordedRight shape.same shape.names shape.low shape.high shape.parameters shape.parametersRight shape.query]
    exact ⟨rfl,rfl,rfl⟩
  · constructor
    · intro output member; cases member
    · rw [GeneralDictionaryLinearLeaf.generated_empty _ _ _ _ _ rfl rfl]

theorem candidate : GeneralDictionaryCenteredCandidate176.Candidate registry start root declaration.id [] plan := by
  refine ⟨rfl,rfl,rfl,rfl,?_,by simp [start,initialAt,GeneralNominalSupport.initial,
    GeneralNominalSaturationState.initial],by simp [start,initialAt],by simp,rfl,
    located,prepared,assignment true,branch_good⟩
  exact GeneralDictionaryLinearLeaf.children_empty context registry root declaration packet.checked rfl _

theorem evidence_good : GeneralDictionaryRecursiveEvidence.Evidence registry context (assignment true) root (.node declaration.id []) := by
  have extrema := (GeneralDictionaryCenteredNominal178.candidate_holds_iff_extrema candidate shape located rfl rfl
    (assignment true) (inhabited true)).mp branch_good
  exact GeneralDictionaryCenteredNominal178.candidate_evidence candidate shape located rfl rfl
    (assignment true) (inhabited true) extrema

theorem fixed_model_gap : Models start (assignment false) ∧
    GeneralDictionaryCenteredCandidate176.Candidate registry start root declaration.id [] plan ∧
    ¬ packet.Holds (assignment false) := ⟨inhabited false,candidate,branch_bad⟩

/-- A different visible declaration cannot rescue the bad assignment: this
registry contains exactly the selected source declaration. -/
theorem evidence_bad : ¬ GeneralDictionaryRecursiveEvidence.Evidence registry context (assignment false) root (.node declaration.id []) := by
  intro evidence
  have inst := (GeneralDictionaryRecursiveEvidence.evidence_leaf_iff registry context
    (assignment false) root declaration.id).mp evidence
  obtain ⟨chosen,visible,checked,_,_,bounds,found,_,_,_,_,branch⟩ := inst
  have sameDeclaration : chosen = declaration := List.mem_singleton.mp visible
  subst chosen
  have sameBounds := Option.some.inj (found.symm.trans located)
  subst bounds
  exact branch_bad branch

theorem evidence_not_from_candidate_alone : Models start (assignment false) ∧
    GeneralDictionaryCenteredCandidate176.Candidate registry start root declaration.id [] plan ∧
    ¬ GeneralDictionaryRecursiveEvidence.Evidence registry context (assignment false) root (.node declaration.id []) :=
  ⟨inhabited false,candidate,evidence_bad⟩

end Yulang.GeneralDictionaryCenteredNominalExample178
