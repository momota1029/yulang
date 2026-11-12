import Yulang.GeneralNominalRecursiveExamples
import Yulang.GeneralNominalRecursiveBoundary

/-!
# Original-state models need not satisfy a surviving terminal branch

This regression uses the recursive candidate relation unchanged. A checked
terminal declaration accepts `List a` and defines its requested output as int.
The original source permits `List string` with that output target equal to
string. An int-valued branch witness proves applicability, but does not prove
the source output equation in every original-state model. Selection therefore
needs its branch facts installed before an all-model evidence rule can use them.
-/
namespace Yulang.GeneralDictionaryRecursiveObstruction

open GeneralDeclarations GeneralDeclarationPatterns
open GeneralDeclarationExamples (constructors roles outputRole)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalUnaryCaptureFacts
open CommonNominalFullCarrier

abbrev equation : Equation := ⟨41,1,.app 2 []⟩
abbrev declaration : Declaration := ⟨40,2,[.app 0 [.var 0]],[],[equation],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[declaration]⟩
abbrev context : Context := GeneralNominalExamples.context false
abbrev root : GeneralSourceDictionaries.Occurrence roles :=
  ⟨300,⟨2,fun _ => (0,0),[⟨1,1⟩],by
    intro output member
    have same := List.mem_singleton.mp member
    subst output
    exact ⟨none,rfl⟩⟩⟩

theorem declaration_checked : DeclarationChecked constructors roles declaration := by
  constructor
  · refine ⟨rfl,?_,?_,?_⟩
    · intro entry member
      have same := List.mem_singleton.mp member
      subst entry
      exact ⟨none,rfl⟩
    · intro name body present
      by_cases one : name = 1
      · subst name
        exact Or.inl ⟨equation,by simp,rfl⟩
      · simp [roles,outputRole,one] at present
    · intro clause member; cases member
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,
      normalizeArgs,normalize,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro clause member; cases member
  · intro clause member; cases member
  · intro clause member; cases member
  · intro clause member; cases member

theorem registry_checked : Checked registry := by
  refine ⟨by simp,?_⟩
  intro candidate member
  have same := List.mem_singleton.mp member
  subst candidate
  exact declaration_checked

theorem query_exact : GeneralNominalInspection.queries context.state context.interpretation declaration =
    [.nominal 0 [.variables [0]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation]

theorem report_calculated : report context declaration [(0,0)] =
    captured context.state 0 0 0 (1,1) :=
  report_exact context declaration 0 GeneralNominalExamples.listDescriptor rfl 0 (1,1) rfl query_exact

theorem schema_calculated : generated registry context root declaration declaration_checked [(0,0)] =
    { tests := [(.source 1,.scalar .int)] } := by
  unfold generated GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
    List.mergeSort_nil]
  simp [GeneralNominalMaterialization.rootRequests,GeneralDeclarationDemands.emitAll,
    GeneralNominalMaterialization.generated,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,normalize,normalizeArgs,GeneralNominalInspection.translate,
    GeneralNominalExamples.interpretation]

theorem good_branch : BranchModels registry context root declaration declaration_checked [(0,0)]
    GeneralNominalExamples.model := by
  have privateModel := private_models context registry root declaration 0
    GeneralNominalExamples.listDescriptor rfl 0 rfl (1,1) rfl query_exact
    GeneralNominalExamples.model (GeneralNominalExamples.state_models false)
  refine ⟨privateModel.1,privateModel.2,?_⟩
  rw [schema_calculated]
  refine ⟨?_,?_,?_,?_⟩
  · intro test member
    have same := List.mem_singleton.mp member
    subst test
    refine ⟨⟨_,.source 1⟩,?_⟩
    intro actual observed
    cases observed
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro entry member; cases member
  · intro first member; cases member
  · intro entry member; cases member

theorem metadata : Metadata registry context := by
  refine ⟨rfl,?_⟩
  intro name primitive recorded
  by_cases two : name = 2
  · subst name
    have same : GeneralCandidateInspection.Primitive.scalar .int = primitive := Option.some.inj recorded
    subst primitive
    exact ⟨⟨[],2⟩,rfl,rfl⟩
  · simp [two] at recorded

theorem linked : GeneralNominalState.Linked context.state root.demand := by
  constructor
  · intro index
    constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
  · intro output member
    have same := List.mem_singleton.mp member
    subst output
    simp [GeneralNominalState.sources,List.ofFn_succ]

theorem not_pending : ¬ GeneralNominalState.RootPending context.state root.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨0,rfl,Or.inr ⟨GeneralNominalExamples.listDescriptor,rfl⟩⟩

theorem prepared : Prepared registry context root declaration declaration_checked := by
  refine ⟨metadata,linked,initial_fresh _ _ _ (by decide +kernel),[(0,0)],
    (by decide +kernel),?_,?_,GeneralNominalExamples.model,good_branch⟩
  · rw [report_calculated]
    exact ⟨rfl,rfl,rfl⟩
  · constructor
    · intro output member
      have same := List.mem_singleton.mp member
      subst output
      exact ⟨equation,by simp,rfl⟩
    · rw [schema_calculated]

theorem survivor : Survivor registry context root 40 [] := by
  refine ⟨not_pending,declaration,by simp,declaration_checked,rfl,rfl,[(0,0)],
    (by decide +kernel),prepared,?_⟩
  unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
    List.mergeSort_nil]
  rfl

theorem not_rootK2 : ¬ GeneralNominalMixedRecurrence.RootK2 context.state root.demand := by
  rintro ⟨_,_,index,slot,equal,recursive⟩
  have same : slot = 0 := Fin.ext equal
  subst slot
  exact GeneralNominalMixedRecurrence.nominal_not_recursive context.state 0
    GeneralNominalExamples.listDescriptor rfl recursive

theorem not_candidateK2 : ¬ CandidateK2 registry context root := by
  rintro ⟨_,candidate,visible,_,_,_,bounds,located,visited,member,recursive⟩
  have same := List.mem_singleton.mp visible
  subst candidate
  have found : arguments context root = some [(0,0)] := by decide +kernel
  have same := Option.some.inj (found.symm.trans located)
  subst bounds
  rw [report_calculated] at member
  have same := List.mem_singleton.mp member
  subst visited
  exact GeneralNominalMixedRecurrence.nominal_not_recursive context.state 0
    GeneralNominalExamples.listDescriptor rfl recursive

theorem not_inspection_pending : ¬ InspectionPending registry context root := by
  rintro ⟨_,candidate,visible,checked,_,_,unprepared⟩
  have same := List.mem_singleton.mp visible
  subst candidate
  exact unprepared prepared

theorem safe : GeneralNominalLocalBoundary.SafeKnown
    (GeneralNominalLocalBoundary.recursiveFields roles) registry context root :=
  ⟨not_pending,not_rootK2,not_candidateK2,not_inspection_pending⟩

theorem unique : GeneralNominalLocalBoundary.Unique
    (GeneralNominalLocalBoundary.recursiveFields roles) registry context root 40 [] := by
  refine ⟨survivor,?_⟩
  intro key children candidate
  have original := candidate
  obtain ⟨_,decl,visible,_,identity,_⟩ := candidate
  have same := List.mem_singleton.mp visible
  subst decl
  have same : key = 40 := identity.symm
  subst key
  exact ⟨rfl,survivor_children_functional registry registry_checked context root 40 children [] original survivor⟩

theorem selected : GeneralNominalLocalBoundary.Local
    (GeneralNominalLocalBoundary.recursiveFields roles) registry context root (.selected 40 []) :=
  .selected safe unique

abbrev badModel : GeneralNominalCommonBridge.Assignment := fun source =>
  (if source = 0 then nominal 0 [.inl (.base .str)] else .base .str,Common.rowEmpty)

theorem bad_original_model : GeneralNominalState.Models context.state badModel := by
  refine ⟨⟨?_,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
  · exact PresenceNormalForm.all_nil _ _
  · intro slot term recorded
    simp [GeneralNominalExamples.heads,GeneralSourceState.Head.equation] at recorded
  · intro pair member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact subtype_refl _
  · intro slot descriptor recorded
    by_cases zero : slot = 0
    · subst slot
      have same : GeneralNominalExamples.listDescriptor = descriptor := Option.some.inj recorded
      subst descriptor
      exact ⟨[.inl (.base .str)],.cons ⟨subtype_refl _,subtype_refl _⟩ .nil,
        ⟨subtype_refl _,subtype_refl _⟩⟩
    · simp [GeneralNominalExamples.state,zero] at recorded

/-- Even the private head intervals and projection constraints hold in the bad
model. Only the requested associated-output materialization distinguishes it. -/
theorem bad_private_projection :
    GeneralNominalState.Models (privateState registry context root declaration [(0,0)]) badModel ∧
    ProjectionModels context.state (report context declaration [(0,0)]) badModel :=
  private_models context registry root declaration 0 GeneralNominalExamples.listDescriptor
    rfl 0 rfl (1,1) rfl query_exact badModel bad_original_model

theorem bad_output_equation : ¬ Equivalent (badModel 1).1 (.base .int) := by
  intro equal
  have old := (CommonNominalFullModelMap.subtype_exact (.base .str) (.base .int)).mp equal.1
  cases (CommonRigidHeadInspection.base_iff .str .int).mp old

theorem bad_not_branch : ¬ BranchModels registry context root declaration declaration_checked [(0,0)] badModel := by
  intro branch
  have materialized := branch.2.2
  rw [schema_calculated] at materialized
  have equal := (materialized.1 (.source 1,.scalar .int) (by simp)).2 _ (.source 1)
  exact bad_output_equation equal

/-- The countermodel satisfies the original state even though the checked,
safe, unique terminal candidate survives using a different branch witness. -/
theorem original_model_gap : Checked registry ∧
    GeneralNominalLocalBoundary.SafeKnown (GeneralNominalLocalBoundary.recursiveFields roles) registry context root ∧
    GeneralNominalLocalBoundary.Unique (GeneralNominalLocalBoundary.recursiveFields roles) registry context root 40 [] ∧
    GeneralNominalState.Models context.state badModel ∧
    ¬ BranchModels registry context root declaration declaration_checked [(0,0)] badModel :=
  ⟨registry_checked,safe,unique,bad_original_model,bad_not_branch⟩


/-- The obligation below comes from the source itself: output 1 is explicitly
int, and this demand retains source identity 1 as that named output's target. -/
theorem output_provenance : equation ∈ declaration.associated ∧ equation.name = 1 ∧
    normalize equation.rhs = .app 2 [] ∧
    context.interpretation.primitives 2 = some (.scalar .int) ∧
    root.demand.outputs = [⟨1,1⟩] :=
  ⟨by simp,rfl,rfl,rfl,rfl⟩

/-- Local classification does not require the state to have installed the
selected branch equations. It selects this leaf for every remaining package. -/
theorem classified_any (remaining : GeneralNominalLocalBoundary.Remaining
    (GeneralNominalCandidates.vocabulary roles)) :
    B4TargetV3.Classify
      (GeneralNominalLocalBoundary.complete (GeneralNominalLocalBoundary.recursiveFields roles) remaining)
      registry context root (.selected (.node 40 [])) :=
  .selected safe unique .nil

/-- Any proposed source Evidence must respect the explicit associated equality
(spec/06-roles.md, section 6.3). Even this one necessary terminal-output law
already contradicts an all-original-model EvidenceNode, independently of the
representation or implementation chosen for Evidence. The output law is an
explicit premise, not an assertion about arbitrary predicates. -/
theorem no_evidenceNode_of_output_sound
    (remaining : GeneralNominalLocalBoundary.Remaining (GeneralNominalCandidates.vocabulary roles))
    (outputSound : ∀ model, remaining.Evidence registry context model root (.node 40 []) →
      Equivalent (model 1).1 (.base .int)) :
    ¬ B4TargetV3.EvidenceNode
      (GeneralNominalLocalBoundary.complete (GeneralNominalLocalBoundary.recursiveFields roles) remaining) := by
  intro node
  exact bad_output_equation (outputSound badModel
    (node registry ⟨rfl,registry_checked⟩ context badModel bad_original_model
      root 40 [] [] safe unique .nil))

/-- The same obstruction refutes final dictionary soundness for an executor
only when that executor leaves this source context unchanged. Nothing here
refutes an executor which installs the branch equations in its final state. -/
theorem no_dictionarySound_of_unchanged
    (remaining : GeneralNominalLocalBoundary.Remaining (GeneralNominalCandidates.vocabulary roles))
    (outputSound : ∀ model, remaining.Evidence registry context model root (.node 40 []) →
      Equivalent (model 1).1 (.base .int))
    (executor : B4TargetV3.Executor (GeneralNominalCandidates.vocabulary roles))
    (unchanged : (executor.run registry context root).1 = context) :
    ¬ B4TargetV3.DictionarySound
      (GeneralNominalLocalBoundary.complete (GeneralNominalLocalBoundary.recursiveFields roles) remaining)
      executor := by
  intro sound
  have classified := classified_any remaining
  have models := bad_original_model
  rw [← unchanged] at classified models
  have evidence := sound registry ⟨rfl,registry_checked⟩ context root (.node 40 []) classified badModel models
  rw [unchanged] at evidence
  exact bad_output_equation (outputSound badModel evidence)

end Yulang.GeneralDictionaryRecursiveObstruction
