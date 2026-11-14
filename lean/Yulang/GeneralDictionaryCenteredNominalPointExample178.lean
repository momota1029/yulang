import Yulang.GeneralDictionaryCenteredNominalPoint178
import Yulang.GeneralDictionaryCenteredNominalExample178

/-! Point inspection reads one capture; two different outer slots read two.
Even when their nominal values coincide, the latter path has fresh extrema
obligations. This comparison does not assert stable selection or G reachability. -/
namespace Yulang.GeneralDictionaryCenteredNominalPointExample178
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralDeclarationExamples (roles)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionaryNominalPairExample178 (context state declaration registry shape assignment)

abbrev root : Occurrence roles := ⟨GeneralDictionaryNominalPairExample178.root.identity,⟨0,fun _ => (0,0),[],by simp⟩⟩
abbrev start := initial context root
abbrev leaf : GeneralDictionaryLinearLeaf.LinearLeafShape context root declaration where
  terminal := rfl
  outputs := rfl
  role := rfl
  slot := 0
  descriptor := GeneralDictionaryNominalPairExample178.descriptor
  recorded := rfl
  arity := 1
  names := fun _ => 0
  distinct := fun i j _ => Subsingleton.elim i j
  inputs := rfl
  bounds := fun _ => (2,3)
  parameters := rfl
  query := shape.query
  located := by decide +kernel
abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite root,declaration,
    GeneralDictionaryNominalPairExample178.declaration_checked,[(0,0)]⟩
abbrev plan : Plan roles := ⟨packet,rootSite state.seed root,rfl⟩

theorem inhabited (good : Bool) : Models start (assignment good) :=
  (point_initial_models context root (fun _ => rfl) _).mpr
    (GeneralDictionaryNominalPairExample178.source_models good)

theorem branch (good : Bool) : packet.Holds (assignment good) :=
  GeneralDictionaryLinearLeaf.branch_models context registry root declaration packet.checked leaf _
    (GeneralDictionaryNominalPairExample178.source_models good)

theorem prepared : Prepared registry context root declaration packet.checked := by
  refine ⟨GeneralDictionaryCenteredNominalExample178.metadata,?_,?_,[(0,0)],leaf.located,?_,?_,
    assignment false,branch false⟩
  · constructor
    · intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
    · intro output member; cases member
  · exact GeneralDictionaryCenteredNominalExample178.prepared.2.2.1
  · exact GeneralNominalLinearCaptureFacts.report_finished context declaration leaf.slot leaf.descriptor
      leaf.recorded leaf.names leaf.bounds leaf.parameters leaf.query
  · exact GeneralDictionaryLinearLeaf.ready context registry root declaration packet.checked leaf

theorem candidate : GeneralDictionaryCenteredCandidate176.Candidate registry start root declaration.id [] plan := by
  refine ⟨rfl,rfl,rfl,rfl,?_,by simp [start,initial,initialAt,GeneralNominalSupport.initial,
    GeneralNominalSaturationState.initial,rootSite],by simp [start,initial,initialAt],by simp,rfl,
    leaf.located,prepared,assignment false,branch false⟩
  exact GeneralDictionaryLinearLeaf.children_empty context registry root declaration packet.checked rfl _

theorem evidence (good : Bool) : GeneralDictionaryRecursiveEvidence.Evidence registry context (assignment good) root (.node declaration.id []) :=
  GeneralDictionaryCenteredNominalPoint178.point_evidence candidate 0 0 (fun _ : Fin 1 => 0)
    (fun i j _ => Subsingleton.elim i j) rfl shape.query leaf.located rfl rfl _ (inhabited good)

theorem same_nominal_endpoints : (assignment false 0).1 = (assignment false 1).1 := rfl

theorem point_succeeds_nonpoint_fails :
    Models start (assignment false) ∧
    GeneralDictionaryRecursiveEvidence.Evidence registry context (assignment false) root (.node declaration.id []) ∧
    ¬ GeneralDictionaryRecursiveEvidence.Evidence registry context (assignment false)
      GeneralDictionaryCenteredNominalExample178.root (.node declaration.id []) :=
  ⟨inhabited false,evidence false,GeneralDictionaryCenteredNominalExample178.evidence_bad⟩
end Yulang.GeneralDictionaryCenteredNominalPointExample178
