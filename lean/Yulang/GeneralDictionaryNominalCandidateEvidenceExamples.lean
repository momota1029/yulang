import Yulang.GeneralDictionaryNominalCandidateEvidence
import Yulang.GeneralNominalExamples

/-! A terminal supported-variable candidate with known input and no requested
outputs jointly satisfies the candidate/materialization/model premises. -/
namespace Yulang.GeneralDictionaryNominalCandidateEvidenceExamples
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalExamples (context state model state_models)
open GeneralDictionaryNominalCandidateEvidence (prepare)

abbrev terminal : Declaration := ⟨7,0,[.var 0],[],[],[]⟩
theorem terminal_checked : DeclarationChecked constructors roles terminal := by
  constructor
  · simp [Declaration.Signature, roles, GeneralDeclarationExamples.bareRole]
  · simp [Declaration.Identified, Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly, Declaration.outputNames]
  · simp [Declaration.Scoped, Declaration.inputNames, Declaration.outputNames, normalizeArgs, normalize,
      variablesArgs, Pattern.variables]
  · simp [Declaration.ConstructorScoped, ArgsWellScoped, WellScoped]
  · simp
  · simp
  · simp
  · simp
abbrev registry : Registry := ⟨constructors,roles,[terminal]⟩
theorem registry_checked : Checked registry := by
  refine ⟨by simp, ?_⟩
  intro declaration member
  have same := List.mem_singleton.mp member
  subst declaration
  exact terminal_checked
abbrev demand : GeneralSourceState.Demand roles := ⟨0,fun _ => (1,1),[],by intro _ member; cases member⟩
abbrev root : Occurrence roles := ⟨200,demand⟩
abbrev captured : GeneralNominalAllocation.Bindings := [(0,(1,1))]

theorem located : GeneralNominalCandidates.arguments (context true) root = some [(1,1)] := by decide +kernel

theorem report : GeneralNominalCandidates.report (context true) terminal [(1,1)] =
    { captures := [(0,(1,1))], inspected := [(1,1)] } := by
  simp [GeneralNominalCandidates.report, GeneralNominalInspection.queries, Declaration.normalHead,
    normalizeArgs, normalize, GeneralNominalInspection.translate, GeneralNominalInspection.inspectMany,
    GeneralNominalInspection.inspect, GeneralNominalInspection.Report.append]

theorem survivor : GeneralNominalCandidates.Survivor registry (context true) root 7 [] := by
  have metadata : GeneralNominalCandidates.Metadata registry (context true) := by
    refine ⟨rfl, ?_⟩
    intro name primitive recorded
    by_cases two : name = 2
    · subst name
      have same : GeneralCandidateInspection.Primitive.scalar .int = primitive := Option.some.inj recorded
      subst primitive
      exact ⟨⟨[],2⟩,rfl,rfl⟩
    · simp [two] at recorded
  have fresh : GeneralNominalAllocation.Fresh (state true) registry root.identity := by
    intro key _ collision
    have bound : (GeneralNominalState.sources (state true)).foldr max 0 = (state true).seed := rfl
    have below := GeneralNominalAllocation.member_le_max _ _ collision
    rw [bound] at below
    exact False.elim (GeneralNominalAllocation.source_initial_fresh (state true) registry root.identity key _ below rfl)
  have noChildren (capture : GeneralNominalAllocation.Bindings) :
      GeneralNominalAllocation.children (state true) registry root terminal terminal_checked capture = [] := by
    simp [GeneralNominalAllocation.children, GeneralDictionaryEmissionPlans.children,
      GeneralCanonicalChildOrder.canonicalEmit, GeneralCanonicalChildOrder.canonicalDeclaration,
      GeneralCanonicalChildOrder.canonicalRequirements, GeneralDeclarationDemands.emitAll, terminal]
  refine ⟨?_, terminal, by simp, terminal_checked, rfl, rfl, [(1,1)], located, ?_, ?_⟩
  · rintro ⟨index, unknown⟩
    exact unknown ⟨1,rfl,Or.inl (by decide +kernel)⟩
  · refine ⟨metadata, ?_, fresh, [(1,1)], located, ?_, ?_, ?_, ?_⟩
    · constructor
      · intro index
        constructor <;> simp [GeneralNominalState.sources, List.ofFn_succ]
      · intro output member; cases member
    · rw [report]; exact ⟨rfl,rfl,rfl⟩
    · rw [report]
      intro bounds member
      have same := List.mem_singleton.mp member
      subst bounds
      apply Or.inr
      intro slot path
      cases path with
      | nil => decide +kernel
      | cons child _ =>
        obtain ⟨kind, children, impossible, _⟩ := child
        cases impossible
    · refine ⟨model, ?_⟩
      unfold GeneralNominalCandidates.privateState
      rw [report]
      apply (GeneralNominalAllocation.propagate_models ..).mpr
      refine ⟨state_models true, ?_, ?_⟩
      · intro first one last two _
        have a := List.mem_singleton.mp one
        have b := List.mem_singleton.mp two
        subst first; subst last
        exact CommonNominalFullCarrier.subtype_refl _
      · simp [GeneralNominalAllocation.merges, GeneralNominalInspection.bindings,
          GeneralNominalAllocation.occurrences, Declaration.inputNames, normalizeArgs, normalize,
          variablesArgs, Pattern.variables]
    · refine ⟨rfl, ?_, ?_⟩
      · simp [GeneralCanonicalChildOrder.canonicalEmit, GeneralCanonicalChildOrder.canonicalDeclaration,
          GeneralCanonicalChildOrder.canonicalRequirements, GeneralDeclarationDemands.emitAll, terminal]
      · rw [noChildren]; simp
  · exact (noChildren _).symm

abbrev payload : GeneralDictionaryReadback.Payload := .node 7 []
theorem candidate_payload : GeneralDictionaryReadback.PayloadEvidence (GeneralNominalCandidates.Survivor registry (context true)) root payload :=
  .node survivor .nil

theorem preparation_exists : (prepare registry registry_checked (context true) payload root).isSome = true := by
  decide +kernel

abbrev tree : GeneralDictionaryTransactions.Prepared roles (state true).base :=
  (prepare registry registry_checked (context true) payload root).get preparation_exists

theorem preparation_success : prepare registry registry_checked (context true) payload root = some tree :=
  (Option.some_get preparation_exists).symm

abbrev locatedTerms : GeneralDictionaryStateEquations.Located (state true).base demand where
  lower := fun _ => 1
  upper := fun _ => 1
  head := fun _ => .var 1
  target := fun index => Fin.elim0 index
  output := fun index => Fin.elim0 index
  arguments := fun _ => rfl
  targets := fun index => Fin.elim0 index

theorem tree_items : tree.items = [⟨demand, locatedTerms⟩] := by
  cbv
  congr 3
  all_goals funext index
  all_goals first
    | exact Fin.elim0 index
    | cases index with
      | mk value bound =>
        have zero : value = 0 := by change value < 1 at bound; omega
        subst value
        rfl

theorem recorded_model : GeneralNominalState.Models
    (GeneralDictionaryNominalRecording.record (state true) tree.items) model := by
  apply (GeneralDictionaryNominalRecording.record_models _ _ _).mpr
  refine ⟨state_models true, ?_⟩
  rw [tree_items]
  intro item member
  have same := List.mem_singleton.mp member
  subst item
  constructor
  · intro index
    exact ⟨CommonNominalFullCarrier.subtype_refl _, CommonNominalFullCarrier.subtype_refl _⟩
  · intro index
    exact Fin.elim0 index

theorem joint_nonvacuous :
    GeneralDictionaryReadback.PayloadEvidence (GeneralNominalCandidates.Survivor registry (context true)) root payload ∧
    prepare registry registry_checked (context true) payload root = some tree ∧
    GeneralNominalState.Models (GeneralDictionaryNominalRecording.record (state true) tree.items) model ∧
    ∃ witness, Readback root payload witness ∧
      Evidence (GeneralNominalCandidates.Survivor registry (context true)) witness ∧
      Evidence (GeneralDictionaryNominalSourceEvidence.Instance registry registry_checked
        (GeneralDictionaryNominalCandidateReadback.frames registry (context true)) model) witness := by
  obtain ⟨witness, readback, candidate, uniform⟩ :=
    GeneralDictionaryNominalCandidateEvidence.prepare_uniform_joint registry registry_checked (context true)
      payload root tree candidate_payload preparation_success
  exact ⟨candidate_payload, preparation_success, recorded_model, witness, readback, candidate,
    (uniform model recorded_model).2⟩

end Yulang.GeneralDictionaryNominalCandidateEvidenceExamples
