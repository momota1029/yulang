import Yulang.GeneralDictionaryDefaultFinite208
import Yulang.GeneralNominalCenteredHeadMatSemanticCodes

namespace Yulang.GeneralDictionaryDefaultCodes208
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralDictionaryAssociatedProvenance
open GeneralNominalCenteredHeadMatEffects
open GeneralNominalCenteredHeadMatSemanticCodes (Config encode)
open GeneralNominalCenteredHeadMatPlanData (Same)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {first last plan : Plan roles}

/-- The finite signature stores class output names and targets, not a source snapshot. -/
def ClassMeaning (outputs : List GeneralSourceState.Output) (plan : Plan roles) (model : Assignment) : Prop :=
  (∀ output ∈ outputs, ∀ body, lookup roles plan.packet.declaration output.name = some body →
    BodyHolds plan output.target model body) ∧
  ∀ first ∈ outputs, ∀ last ∈ outputs, first.name = last.name →
    CommonNominalFullCarrier.Equivalent (model first.target).1 (model last.target).1

theorem body_same (same : Same first last) (target model body) :
    BodyHolds first target model body ↔ BodyHolds last target model body := by
  have defaults : defaultVariables first model = defaultVariables last model := by
    funext mode index
    have centers := congrArg (fun site : Site roles => List.ofFn site.center) same.input
    simp only [defaultVariables,centers]
    rfl
  cases body <;> simp only [BodyHolds,bodySchema,compileBody,bodyVariables,
    same.registry,same.interpretation,GeneralNominalCenteredHeadMatPlanData.variables_eq same,
    defaults]

theorem class_same (same : Same first last) (outputs model) :
    ClassMeaning outputs first model ↔ ClassMeaning outputs last model := by
  simp only [ClassMeaning,same.declaration,body_same same]

theorem class_membership (same : ∀ output, output ∈ firstOutputs ↔ output ∈ lastOutputs) :
    ClassMeaning firstOutputs plan model ↔ ClassMeaning lastOutputs plan model := by
  simp only [ClassMeaning,same]

noncomputable def classCode (pool : List GeneralSourceState.Output)
    (state : GeneralNominalCenteredSteps.State roles) (root : Occurrence roles) : List GeneralSourceState.Output := by
  classical
  exact pool.filter fun output => output ∈ GeneralNominalCenteredHeadOutputs.requests state root

theorem classCode_mem
    (covered : GeneralNominalCenteredHeadOutputs.requests state root ⊆ pool) :
    output ∈ classCode pool state root ↔ output ∈ GeneralNominalCenteredHeadOutputs.requests state root := by
  classical
  simp only [classCode,List.mem_filter,decide_eq_true_eq]
  exact ⟨And.right,fun member => ⟨covered member,member⟩⟩

theorem classCode_meaning
    (covered : GeneralNominalCenteredHeadOutputs.requests state root ⊆ pool) :
    ClassMeaning (classCode pool state root) plan model ↔ ClassEffects state root plan model := by
  simp only [ClassMeaning,classCode_mem covered]
  rfl

theorem classCode_sublist : (classCode pool state root).Sublist pool := by
  classical
  exact List.filter_sublist

structure Code (roles : Roles.RoleDecls) where
  packet : GeneralNominalCenteredHeadMatSemanticCodes.Code roles
  outputs : List GeneralSourceState.Output

noncomputable def signature (context : GeneralNominalCandidates.Context) (code : Code roles) :
    GeneralNominalSharedBudget.Signature roles := by
  classical
  exact if available : ∃ plan, Config context plan ∧ encode plan = code.packet then
    let plan := Classical.choose available
    ⟨plan.input.occurrence,plan.packet.children,fun model =>
      (GeneralNominalCenteredHeadMatStepPackets.Inputs plan model ∧
       GeneralNominalCenteredHeadMatStepPackets.Outputs plan model) ∧ ClassMeaning code.outputs plan model⟩
  else ⟨code.packet.input.occurrence,[],fun _ => False⟩

theorem represents (configured : Config context plan)
    (covered : GeneralNominalCenteredHeadOutputs.requests state.core plan.packet.site.occurrence ⊆ pool) :
    GeneralDictionaryDefaultFinite208.Represents
      (signature context ⟨encode plan,classCode pool state.core plan.packet.site.occurrence⟩) state plan := by
  classical
  have available : ∃ other, Config context other ∧ encode other = encode plan := ⟨plan,configured,rfl⟩
  unfold signature
  rw [dite_eq_left available]
  let other := Classical.choose available
  have spec : Config context other ∧ encode other = encode plan := Classical.choose_spec available
  have related := GeneralNominalCenteredHeadMatSemanticCodes.same other plan spec.1 configured spec.2
  refine ⟨(congrArg Site.occurrence related.input).trans plan.input_exact,
    GeneralNominalCenteredHeadMatPlanData.children related,?_⟩
  intro model
  change ((_ ∧ _) ∧ _) ↔ _
  rw [GeneralNominalCenteredHeadMatPlanData.delta related,class_same related,classCode_meaning covered]
  change ((_ ∧ _) ∧ _) ↔ (_ ∧ GeneralDictionaryDefaultSchema208.SchemaHolds _ _ _ _)
  rw [GeneralDictionaryDefaultSchema208.schema_holds_iff]
  exact and_assoc

/-- Finite enumeration of all membership-selected class requests. -/
def selections : List α → List (List α)
  | [] => [[]]
  | first :: rest => selections rest ++ (selections rest).map (first :: ·)

theorem filter_selection (items : List α) (test : α → Bool) :
    items.filter test ∈ selections items := by
  induction items with
  | nil => exact List.mem_singleton_self _
  | cons first rest ih =>
    simp only [List.filter_cons,selections]
    split
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨_,ih,rfl⟩)
    · exact List.mem_append_left _ ih

theorem classCode_selected : classCode pool state root ∈ selections pool := by
  classical
  exact filter_selection _ _

end Yulang.GeneralDictionaryDefaultCodes208
