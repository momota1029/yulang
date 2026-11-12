import Yulang.GeneralDictionaryVariableJournalMerge
import Yulang.GeneralDictionaryOutputMergeSuccess
/-! Nonempty repeated-binder historical packet example. The exhibited assignment
uses int at both outputs; no source-formed reachability is claimed. -/
namespace Yulang.GeneralDictionaryVariableJournalExample
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalRecursiveCandidates
open GeneralNominalRecursiveInspection GeneralNominalUnaryCaptureFacts
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalExamples (context state model state_models listDescriptor displayRoot interpretation)
abbrev firstClause : Clause := ⟨10,1,[.var 0],[⟨30,0,.var 0⟩]⟩
abbrev secondClause : Clause := ⟨11,1,[.var 0],[⟨31,0,.var 0⟩]⟩
abbrev declaration : Declaration := { GeneralDeclarationExamples.display with
  requirements := [firstClause, secondClause] }
abbrev terminal := GeneralDictionaryJointMergeExample.terminal
abbrev terminal_checked := GeneralDictionaryJointMergeExample.terminal_checked
abbrev registry : Registry := ⟨constructors, roles, [declaration,terminal]⟩

theorem checked : DeclarationChecked constructors roles declaration := by
  constructor
  · refine ⟨rfl,by simp,?_,?_⟩
    · intro name body impossible; cases impossible
    · intro clause member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      all_goals
        refine ⟨rfl,?_⟩
        intro equation member
        have eq := List.mem_singleton.mp member; subst equation
        exact ⟨none,rfl⟩
  · simp [Declaration.Identified, Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly, Declaration.outputNames]
  · simp [Declaration.Scoped, Declaration.inputNames, Declaration.outputNames, normalizeArgs, normalize, variablesArgs, Pattern.variables]
  · simp [Declaration.ConstructorScoped, ArgsWellScoped, WellScoped, constructors]
  · intro clause member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact ⟨rfl,rfl⟩
  · intro clause member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro clause member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> (unfold ConservativeSmaller; decide +kernel)
  · intro clause member; simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact unary_descent 0 0

theorem query : GeneralNominalInspection.queries (state true) interpretation declaration = [.nominal 0 [.variables [0]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,interpretation]

abbrev outputTarget (n : Nat) : Nat :=
  GeneralNominalAllocation.source (state true) registry 100
    (GeneralNominalAllocation.origin 100 1 5 (n+20) 0)

theorem output_nonzero (n : Nat) : outputTarget n ≠ 0 := by
  have positive := GeneralNominalIdentities.source_above_seed (state true).seed
    (GeneralNominalAllocation.origin 100 1 5 (n+20) 0)
  unfold outputTarget GeneralNominalAllocation.source
  omega

theorem schema : generated registry (context true) displayRoot declaration checked [(0,0)] =
    {variables := [⟨0,.source (outputTarget 10),.actual⟩,⟨0,.source (outputTarget 11),.actual⟩]} := by
  unfold generated GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [show GeneralCanonicalChildOrder.canonicalDeclaration declaration = declaration from (by simp [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,declaration,List.mergeSort_pair])]
  simp [GeneralNominalMaterialization.rootRequests,GeneralDeclarationDemands.emitAll,
    GeneralDeclarationDemands.emit,GeneralNominalMaterialization.emissionRequests,
    GeneralNominalMaterialization.inputRequests,List.ofFn_succ,normalize,GeneralNominalMaterialization.generated,
    GeneralNominalMaterialization.schema,GeneralNominalMaterialization.Schema.append,
    GeneralNominalInspection.translate,interpretation,outputTarget,GeneralNominalAllocation.allocation,
    GeneralDeclarationDemands.outputTarget,Declaration.outputNames]


theorem calculated : report (context true) declaration [(0,0)] =
    captured (state true) 0 0 0 (1,1) :=
  report_exact (context true) declaration 0 listDescriptor rfl 0 (1,1) rfl query

theorem branch : BranchModels registry (context true) displayRoot declaration checked [(0,0)] model := by
  have privateModel := private_models (context true) registry displayRoot declaration 0 listDescriptor rfl 0 rfl
    (1,1) rfl query model (state_models true)
  refine ⟨privateModel.1,privateModel.2,?_⟩
  rw [schema,calculated]
  refine ⟨by simp,?_,?_,?_⟩
  · intro entry member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    all_goals
      refine ⟨⟨_,.source _⟩,?_⟩
      intro actual seen; cases seen
      simp only [GeneralNominalMaterialization.VariableHolds]
      simp [Declaration.outputNames,GeneralNominalCaptureMerges.Fits,GeneralNominalAllocation.capture,
        bindings,captured,GeneralNominalAllocation.occurrences,output_nonzero,CommonNominalFullCarrier.subtype_refl]
  · intro first one last two _ _ _ a b ha hb
    simp only [List.mem_cons,List.not_mem_nil,or_false] at one two
    rcases one with rfl | rfl <;> rcases two with rfl | rfl <;> cases ha <;> cases hb
    all_goals
      simp [output_nonzero,CommonNominalFullCarrier.Equivalent,
        CommonNominalFullCarrier.subtype_refl]
  · intro entry member cap present _ _
    have same := List.mem_singleton.mp present; subst cap
    intro origin identified a b observed seen
    have eq := Option.some.inj identified; subst origin
    have bounds := (nominal_argument_bounds (state true) model (state_models true) 0 listDescriptor rfl
      0 (1,1) rfl).2 b seen
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> cases observed
    all_goals
      simpa [GeneralNominalExamples.model,output_nonzero,GeneralNominalCaptureMerges.Fits,
        CommonNominalFullCarrier.Equivalent] using bounds

abbrev child (clause : Nat) : Occurrence roles :=
  ⟨GeneralNominalAllocation.source (state true) registry 100
    (GeneralNominalAllocation.origin 100 1 6 clause 0),
    ⟨1,fun _ => (1,1),[⟨0,outputTarget clause⟩],by
      intro output member
      have eq := List.mem_singleton.mp member; subst output
      exact ⟨none,rfl⟩⟩⟩
abbrev site (n : Nat) := GeneralNominalDemandMerging.pointSite (child n)
abbrev packet : Packet roles :=
  ⟨registry,context true,GeneralNominalDemandMerging.pointSite displayRoot,declaration,checked,[(0,0)]⟩
/-- A concrete journal with a valid historical parent packet and two sites.
No claim that an Initial/Step path constructs this journal is made here. -/
abbrev journal : State roles := ⟨context true,[packet],[site 10,site 11],[],[]⟩

theorem requests (n : Nat) (which : n = 10 ∨ n = 11) :
    GeneralDictionaryVariableJournalMerge.Requests packet (site n) (fun _ => 0) := by
  intro output present
  have eq := List.mem_singleton.mp present; subst output
  change (⟨0,.source (outputTarget n),.actual⟩ : GeneralNominalMaterialization.Use) ∈
    (generated registry (context true) displayRoot declaration checked [(0,0)]).variables
  rw [schema]
  rcases which with rfl | rfl <;> simp

theorem journal_model : Models journal model := by
  refine ⟨state_models true,?_,?_⟩
  · intro p member
    have eq := List.mem_singleton.mp member; subst p
    exact branch
  · intro s member
    rcases List.mem_cons.mp member with rfl | rest
    · exact point_holds _ _
    · have eq := List.mem_singleton.mp rest; subst s
      exact point_holds _ _

theorem distinct_outputs : outputTarget 10 ≠ outputTarget 11 := by
  intro equal
  have same := (GeneralNominalIdentities.source_identity _ _ _).mp equal
  simp [GeneralNominalAllocation.origin] at same

theorem merged_models (m : GeneralNominalCommonBridge.Assignment) :
    Models (merge journal (site 10) (site 11)) m ↔ Models journal m :=
  GeneralDictionaryVariableJournalMerge.models_merge_iff journal (site 10) (site 11) packet
    (by simp) (fun _ => 0) (requests 10 (Or.inl rfl)) (requests 11 (Or.inr rfl)) m

/-- Explicit nonvacuity with two nonempty same-name requests, distinct allocated
output targets, and a real assignment before and after the merge. The witness
is int-valued at both outputs, not a non-scalar-valued regression. -/
theorem nonvacuous :
    Models journal model ∧ Models (merge journal (site 10) (site 11)) model ∧
      outputTarget 10 ≠ outputTarget 11 ∧
      (site 10).occurrence.demand.outputs ≠ [] ∧ (site 11).occurrence.demand.outputs ≠ [] :=
  ⟨journal_model,(merged_models model).mpr journal_model,distinct_outputs,by simp [site,child,GeneralNominalDemandMerging.pointSite],by simp [site,child,GeneralNominalDemandMerging.pointSite]⟩

end Yulang.GeneralDictionaryVariableJournalExample
