import Yulang.GeneralDictionaryJointMerge
import Yulang.GeneralNominalExamples

/-! Positive, nonempty associated-output merge. This is a transformer regression,
not a claim that the state is reachable by support transitions or has two
installed packets. Both root branches and their common model are constructed. -/
namespace Yulang.GeneralDictionaryJointMergeExample
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalSaturationState GeneralNominalJointCandidates
open GeneralNominalDemandMerging (pointSite)

abbrev outputEquation : Equation := ⟨0,0,.app 2 []⟩
abbrev terminal : Declaration := ⟨7,1,[.var 0],[],[outputEquation],[]⟩
theorem terminal_checked : DeclarationChecked constructors roles terminal := by
  constructor
  · refine ⟨rfl,?_,?_,?_⟩
    · intro equation member
      have eq := List.mem_singleton.mp member; subst equation
      exact ⟨none,rfl⟩
    · intro name body present
      by_cases zero : name = 0
      · subst name; exact Or.inl ⟨outputEquation,by simp,rfl⟩
      · simp [roles,GeneralDeclarationExamples.outputRole,zero] at present
    · intro clause member; cases member
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,
      variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · simp
  · simp
  · simp
  · simp
abbrev registry : Registry := ⟨constructors,roles,[terminal]⟩
abbrev source : GeneralNominalState.State := {GeneralNominalExamples.state true with reserved := [3],seed := 3}
abbrev context : GeneralNominalCandidates.Context := ⟨source,GeneralNominalExamples.interpretation⟩
abbrev demand (target : Nat) : GeneralSourceState.Demand roles :=
  ⟨1,fun _ => (1,1),[⟨0,target⟩],by
    intro output member
    have eq := List.mem_singleton.mp member; subst output
    exact ⟨none,rfl⟩⟩
abbrev root (identity target : Nat) : Occurrence roles := ⟨identity,demand target⟩
abbrev model := GeneralNominalExamples.model

theorem source_models : GeneralNominalState.Models source model := GeneralNominalExamples.state_models true

theorem report_exact : report context terminal [(1,1)] =
    { captures := [⟨0,(1,1),none⟩], checked := [(1,1),(1,1)] } := by
  simp [report,GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,inspectMany,inspect,Report.append]

theorem emissions_empty (identity : Nat) (capture : GeneralDeclarationDemands.Capture)
    (allocate : (clause : Clause) → GeneralDeclarationDemands.Allocation roles clause) :
    GeneralCanonicalChildOrder.canonicalEmit identity terminal terminal_checked capture allocate = [] := by
  apply List.eq_nil_of_length_eq_zero
  simp [GeneralCanonicalChildOrder.canonicalEmit,GeneralDeclarationDemands.emitAll,
    GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
    terminal]

theorem schema_exact (identity target : Nat) :
    generated registry context (root identity target) terminal terminal_checked [(1,1)] =
      { tests := [(.source target,.scalar .int)] } := by
  unfold generated GeneralNominalMaterialization.requests
  rw [emissions_empty]
  simp [GeneralNominalMaterialization.rootRequests,
    GeneralNominalMaterialization.generated,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,GeneralNominalInspection.translate,normalize,normalizeArgs,
    GeneralNominalExamples.interpretation]

theorem branch_models (identity target : Nat) (nonzero : target ≠ 0) :
    BranchModels registry context (root identity target) terminal terminal_checked [(1,1)] model := by
  refine ⟨?_,?_,?_⟩
  · unfold privateState
    rw [report_exact]
    apply (GeneralNominalState.extend_models ..).mpr
    constructor
    · apply (GeneralNominalAllocation.propagate_models ..).mpr
      refine ⟨source_models,?_,?_⟩
      · intro first one last two _
        have a := List.mem_singleton.mp one
        have b := List.mem_singleton.mp two
        subst first; subst last
        exact CommonNominalFullCarrier.subtype_refl _
      · simp [GeneralNominalAllocation.merges,bindings,GeneralNominalAllocation.occurrences,
          Declaration.inputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
    · simp [selfChecks,PresenceNormalForm.All,PresenceNormalForm.Atom.Holds,
        CommonNominalFullCarrier.model,CommonNominalFullCarrier.subtype_refl]
  · rw [report_exact]
    simp [ProjectionModels]
  · rw [schema_exact]
    refine ⟨?_,by simp,by simp,by simp⟩
    intro test member
    have eq := List.mem_singleton.mp member; subst test
    refine ⟨⟨_,.source target⟩,?_⟩
    intro actual observation
    cases observation
    change CommonNominalFullCarrier.Equivalent (model target).1 (.base .int)
    simp only [nonzero]
    exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem prepared (identity target : Nat) (supported : target = 1 ∨ target = 3) :
    Prepared registry context (root identity target) terminal terminal_checked := by
  have nonzero : target ≠ 0 := by rcases supported with rfl | rfl <;> decide
  refine ⟨?_,?_,?_,[(1,1)],?_,?_,?_,model,branch_models identity target nonzero⟩
  · refine ⟨rfl,?_⟩
    intro name primitive recorded
    by_cases two : name = 2
    · subst name
      have eq : GeneralCandidateInspection.Primitive.scalar .int = primitive := Option.some.inj recorded
      subst primitive
      exact ⟨⟨[],2⟩,rfl,rfl⟩
    · simp [two] at recorded
  · constructor
    · intro index
      constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
    · intro output member
      have eq := List.mem_singleton.mp member; subst output
      rcases supported with rfl | rfl <;> simp [GeneralNominalState.sources,List.ofFn_succ]
  · intro key member collision
    have bound : (GeneralNominalState.sources source).foldr max 0 = source.seed := rfl
    have below := GeneralNominalAllocation.member_le_max _ _ collision
    rw [bound] at below
    exact False.elim (GeneralNominalAllocation.source_initial_fresh source registry identity key _ below rfl)
  · change arguments context (root 0 0) = some [(1,1)]
    decide +kernel
  · rw [report_exact]; exact ⟨rfl,rfl,rfl⟩
  · constructor
    · intro output member
      have eq := List.mem_singleton.mp member; subst output
      exact ⟨outputEquation,by simp,rfl⟩
    · rw [schema_exact]

abbrev first := pointSite (root 200 1)
abbrev last := pointSite (root 201 3)
abbrev before : State roles := {context := context,sites := [first,last]}

theorem before_models : Models before model := by
  refine ⟨source_models,?_,?_⟩
  · intro packet member; cases member
  · intro site member
    rcases List.mem_cons.mp member with rfl | member
    · exact point_holds _ _
    · have eq := List.mem_singleton.mp member; subst site
      exact point_holds _ _

theorem branch_at (identity target : Nat) (supported : target = 1 ∨ target = 3) :
    BranchAt registry before (root identity target) 7 model := by
  refine ⟨terminal,by simp,terminal_checked,rfl,rfl,prepared identity target supported,[(1,1)],?_,?_⟩
  · change arguments context (root 0 0) = some [(1,1)]
    decide +kernel
  · exact branch_models identity target (by rcases supported with rfl | rfl <;> decide)

theorem same_inputs : GeneralNominalDemandMerging.SameInputs (Models before) first last := by
  refine ⟨rfl,?_⟩
  exact .cons ⟨_,_,rfl,rfl,GeneralNominalDemandMerging.source_same _ 1⟩ .nil

abbrev meaning : GeneralNominalDemandMerging.AssociatedMeaning where
  value := fun _ _ _ => .base .int
  congruent := by
    intro _ _ _ _ _
    exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem dictionary_outputs (identity target : Nat) (nonzero : target ≠ 0) :
    GeneralNominalDemandMerging.DictionaryOutputs meaning model (pointSite (root identity target)) := by
  refine ⟨[.base .int],?_,?_⟩
  · exact .cons ⟨_,rfl,.source 1⟩ .nil
  · intro output member
    have eq := List.mem_singleton.mp member; subst output
    change CommonNominalFullCarrier.Equivalent (model target).1 (.base .int)
    simp only [nonzero]
    exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem output_atoms_nonempty : GeneralNominalDemandMerging.outputAtoms first last =
    [.tyLe (.var 1) (.var 3),.tyLe (.var 3) (.var 1)] := rfl

theorem output_atoms_hold :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalDemandMerging.outputAtoms first last) :=
  GeneralNominalDemandMerging.dictionary_outputs_preserved _ first last same_inputs meaning model before_models
    (dictionary_outputs 200 1 (by decide)) (dictionary_outputs 201 3 (by decide))

theorem merged_joint : Joint registry (merge before first last) first.occurrence 7 := by
  apply GeneralDictionaryJointMerge.joint_merge_registered registry before first last (by simp) 7
    (by intro packet member; cases member) model before_models output_atoms_hold (branch_at 200 1 (Or.inl rfl))
  intro site member _
  rcases List.mem_cons.mp member with rfl | member
  · exact branch_at 200 1 (Or.inl rfl)
  · have eq := List.mem_singleton.mp member; subst site
    exact branch_at 201 3 (Or.inr rfl)

theorem source_evidence (identity target : Nat) (supported : target = 1 ∨ target = 3) :
    GeneralDictionaryRecursiveEvidence.Evidence registry context model (root identity target)
      (.node 7 []) := by
  apply (GeneralDictionaryRecursiveEvidence.evidence_iff_payload ..).mpr
  apply GeneralDictionaryReadback.PayloadEvidence.node _ .nil
  obtain ⟨metadata,linked,fresh,bounds,located,finished,ready,consistent⟩ := prepared identity target supported
  have same : bounds = [(1,1)] := Option.some.inj located.symm
  subst bounds
  refine ⟨terminal,by simp,terminal_checked,rfl,rfl,[(1,1)],located,finished,ready,?_,metadata,?_⟩
  · unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children
    rw [emissions_empty]
    rfl
  · exact branch_models identity target (by rcases supported with rfl | rfl <;> decide)

theorem merged_evidence :
    GeneralDictionaryRecursiveEvidence.Evidence registry (merge before first last).context model
      first.occurrence (.node 7 []) ∧
    GeneralDictionaryRecursiveEvidence.Evidence registry (merge before first last).context model
      last.occurrence (.node 7 []) := by
  constructor
  · exact (GeneralDictionaryJointMerge.evidence_merge_iff ..).mpr
      ⟨source_evidence 200 1 (Or.inl rfl),output_atoms_hold⟩
  · exact (GeneralDictionaryJointMerge.evidence_merge_iff ..).mpr
      ⟨source_evidence 201 3 (Or.inr rfl),output_atoms_hold⟩

end Yulang.GeneralDictionaryJointMergeExample
