import Yulang.GeneralDictionaryCenteredRootScalar177
import Yulang.GeneralDictionaryFiniteObservedExample

/-! An inhabited empty-journal regression of the scalar root producer. -/
namespace Yulang.GeneralDictionaryCenteredRootExample177
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralDeclarationExamples (roles)
open GeneralDictionaryFiniteObservedExample (context state constructors interpretation model state_models)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCenters GeneralNominalCenteredSteps

abbrev declaration := GeneralNominalExamples.intDisplay
abbrev registry : Registry := ⟨constructors,roles,[declaration]⟩
abbrev root : Occurrence roles := ⟨177,⟨0,fun _ => (1,1),[],by simp⟩⟩
abbrev start := initial context root

theorem checked : DeclarationChecked constructors roles declaration := by
  constructor
  · simp [Declaration.Signature,roles,GeneralDeclarationExamples.bareRole]
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,
      normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  all_goals intro c member; cases member

theorem source : GeneralNominalSourceFormation.InitialSource registry context root where
  roles_agree := rfl
  metadata := GeneralDictionaryFiniteObservedExample.metadata
  linked := by
    constructor
    · intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
    · intro output member; cases member
  intervals := fun _ _ _ => CommonNominalFullCarrier.subtype_refl _
  below_seed := GeneralDictionaryFiniteObservedExample.initial_source.below_seed
  unallocated := rfl

abbrev shape : GeneralDictionaryScalarLeaf.ScalarLeafShape context root declaration where
  terminal := rfl
  outputs := rfl
  role := rfl
  slot := 1
  base := .int
  noNominal := rfl
  head := rfl
  inputs := rfl
  query := by simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,interpretation,GeneralNominalExamples.interpretation]
  located := by decide +kernel

abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite root,declaration,checked,[(1,1)]⟩
abbrev plan : Plan roles := ⟨packet,rootSite state.seed root,rfl⟩

theorem prepared : Prepared registry context root declaration checked := by
  refine ⟨source.metadata,source.linked,?_,[(1,1)],shape.located,?_,?_,model,?_⟩
  · intro key _ present
    exact False.elim (GeneralNominalAllocation.source_initial_fresh state registry root.identity key _
      (source.below_seed _ present) rfl)
  · rw [GeneralDictionaryScalarLeaf.report_exact context root declaration shape]
    exact ⟨rfl,rfl,rfl⟩
  · exact GeneralDictionaryScalarLeaf.ready context registry root declaration checked shape
  · exact GeneralDictionaryScalarLeaf.branch_models context registry root declaration checked shape model state_models

theorem candidate : GeneralDictionaryCenteredCandidate176.Candidate registry start root declaration.id [] plan := by
  refine ⟨rfl,rfl,rfl,rfl,?_,by simp [start,initial,initialAt,GeneralNominalSupport.initial,
    GeneralNominalSaturationState.initial,rootSite],by simp [start,initial,initialAt],by simp,rfl,
    shape.located,prepared,model,?_⟩
  · exact GeneralDictionaryLinearLeaf.children_empty context registry root declaration checked rfl _
  · exact GeneralDictionaryScalarLeaf.branch_models context registry root declaration checked shape model state_models

abbrev term : GeneralNominalOriginTerms.Expr Nat := .node (.scalar .int) Fin.elim0

theorem ground : GeneralNominalGroundAccessibility.GroundRoots context root [.app 2 []] := by
  refine ⟨rfl,?_⟩
  intro index
  have zero : index.val = 0 := by have h := index.isLt; change index.val < 1 at h; omega
  simp only [zero]
  refine ⟨term,⟨?_,rfl,⟨trivial,fun i => Fin.elim0 i⟩⟩,?_⟩
  · simp [normalize,normalizeArgs,GeneralNominalInspection.translate,interpretation,
      GeneralNominalExamples.interpretation,GeneralNominalCompoundReadback.quote,
      ]
  · intro assignment valid
    have head := valid.1.2.1 (1 : Fin 2) (.base .int) (by rfl)
    exact head

theorem reachable : B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles)
    registry root start := ⟨start,⟨context,[.app 2 []],source,fun _ => rfl,ground,rfl⟩,.refl⟩

theorem inhabited : Models start model :=
  (point_initial_models context root (fun _ => rfl) model).mpr state_models

theorem evidence : GeneralDictionaryRecursiveEvidence.Evidence registry context model root (.node declaration.id []) :=
  GeneralDictionaryCenteredRootScalar177.root_evidence reachable candidate .int rfl rfl rfl shape.query model inhabited

 theorem empty_journal : start.plans = [] ∧ start.erased.current.packets = [] ∧
    start.erased.current.edges = [] ∧ start.erased.current.aliases = [] := ⟨rfl,rfl,rfl,rfl⟩

/-- A concrete model and actual candidate witness the producer without
assuming a selected semantic instance or a recorded dictionary. -/
theorem regression :
    B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root start ∧
    GeneralDictionaryCenteredCandidate176.Candidate registry start root declaration.id [] plan ∧
    Models start model ∧ start.plans = [] ∧ start.erased.current.packets = [] ∧
    GeneralDictionaryRecursiveEvidence.Evidence registry context model root (.node declaration.id []) :=
  ⟨reachable,candidate,inhabited,rfl,rfl,evidence⟩

end Yulang.GeneralDictionaryCenteredRootExample177
