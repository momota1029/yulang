import Yulang.GeneralDictionaryOutputBinderExamples
import Yulang.GeneralDictionaryBinderLocations
import Yulang.GeneralDictionaryEmissionPlans
import Yulang.GeneralDictionaryVariableTransactions

/-!
# Checked two-level dictionary fixture with a terminal explicit input RHS

The root keeps two distinct output targets and emits its actual container child.
The leaf has a real declared associated output, no where children, and no output
binder. Heads are supplied as ordinary variable terms; this is not declaration
head elaboration or a candidate selection theorem.
-/
namespace Yulang.GeneralDictionaryTerminalFixture
open GeneralDeclarations GeneralDeclarationPatterns GeneralDeclarationDemands
open GeneralDeclarationExamples (constructors roles outputRole)
open GeneralDictionaryOutputBinderExamples (binderWrap binderWrap_checked)
open GeneralSourceState (State Demand Assignment Models)
open GeneralSourceDictionaries
open GeneralDictionaryStateEquations
open GeneralDictionaryBinderLocations (Inputs)
open GeneralDictionaryEmissionPlans
open GeneralDictionaryBatchRecording (Item record)

abbrev leafEquation : Equation := ⟨31, 1, .var 0⟩
abbrev leaf : Declaration := ⟨3, 2, [.var 0], [], [leafEquation], []⟩

theorem leaf_checked : DeclarationChecked constructors roles leaf := by
  constructor
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · intro equation member
      have same := List.mem_singleton.mp member
      subst equation
      exact ⟨none, rfl⟩
    · intro name body present
      by_cases one : name = 1
      · subst name
        exact Or.inl ⟨leafEquation, by simp, rfl⟩
      · simp [roles, outputRole, one] at present
    · intro clause member; cases member
  · simp [Declaration.Identified, Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly, Declaration.outputNames]
  · simp [Declaration.Scoped, Declaration.inputNames, Declaration.outputNames,
      normalizeArgs, normalize, variablesArgs, Pattern.variables]
  · simp [Declaration.ConstructorScoped, ArgsWellScoped, WellScoped]
  · intro clause member; cases member
  · intro clause member; cases member
  · intro clause member; cases member
  · intro clause member; cases member

abbrev registry : Registry := ⟨constructors, roles, [binderWrap, leaf]⟩

theorem registry_checked : Checked registry := by
  refine ⟨by simp, ?_⟩
  intro declaration member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact binderWrap_checked
  · exact leaf_checked

abbrev capture : Capture := ⟨fun _ => (0, 0), fun _ => 2⟩
abbrev frame : Frame roles where
  capture := fun _ => capture
  allocation := fun _ _ => ⟨fun _ => (30, 31), fun _ => 40⟩
  identity := fun _ _ clause => clause

abbrev state : State := GeneralDictionaryOutputBinderExamples.state
abbrev rootDemand : Demand roles where
  role := 1
  arguments := fun _ => (0, 0)
  outputs := [⟨0, 3⟩, ⟨0, 4⟩]
  declared := by
    intro output member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact ⟨none, rfl⟩
abbrev childDemand : Demand roles where
  role := 2
  arguments := fun _ => (0, 0)
  outputs := [⟨1, 2⟩]
  declared := by
    intro output member
    have same := List.mem_singleton.mp member
    subst output
    exact ⟨none, rfl⟩
abbrev root : Occurrence roles := ⟨9, rootDemand⟩
abbrev child : Occurrence roles := ⟨20, childDemand⟩

theorem root_actual_children : children frame root binderWrap binderWrap_checked = [child] := by
  have original : emitAll root.identity binderWrap binderWrap_checked.signature
      (frame.capture binderWrap.id) (frame.allocation binderWrap.id) =
      [emit 9 binderWrap GeneralDeclarationExamples.containerChild
        (binderWrap_checked.signature.2.2.2 _ (by simp)) capture
        (frame.allocation binderWrap.id GeneralDeclarationExamples.containerChild)] := rfl
  have permuted := GeneralCanonicalChildOrder.canonicalEmit_perm root.identity binderWrap
    binderWrap_checked (frame.capture binderWrap.id) (frame.allocation binderWrap.id)
  rw [original] at permuted
  have canonical := permuted.symm.eq_singleton
  unfold children
  rw [canonical]
  simp [occurrence, emit, GeneralDeclarationDemands.childDemand, inputInterval,
    outputTarget, normalize, Declaration.outputNames, child, childDemand,
    frame, capture, GeneralDeclarationExamples.containerChild,
    GeneralDeclarationExamples.itemEquation, binderWrap,
    GeneralDictionaryOutputBinderExamples.binderEquation,
    GeneralDeclarationExamples.wrap, GeneralDeclarationExamples.itemBinder]
theorem child_actual_children : children frame child leaf leaf_checked = [] := by
  have permuted := GeneralCanonicalChildOrder.canonicalEmit_perm child.identity leaf
    leaf_checked (frame.capture leaf.id) (frame.allocation leaf.id)
  have original : emitAll child.identity leaf leaf_checked.signature
      (frame.capture leaf.id) (frame.allocation leaf.id) = [] := rfl
  rw [original] at permuted
  have canonical := List.Perm.nil_eq permuted
  unfold children
  rw [← canonical]
  rfl

abbrev rootInputs : Inputs state rootDemand where
  lower := fun _ => 0
  upper := fun _ => 0
  head := fun _ => .var 0
  target := fun index => ⟨index.val + 3, by have bound := index.isLt; change index.val < 2 at bound; change index.val + 3 < 5; omega⟩
  arguments := fun _ => rfl
  targets := by
    intro index
    obtain ⟨index, bound⟩ := index
    change index < 2 at bound
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with rfl | rfl <;> rfl

abbrev childInputs : Inputs state childDemand where
  lower := fun _ => 0
  upper := fun _ => 0
  head := fun _ => .var 0
  target := fun _ => 2
  arguments := fun _ => rfl
  targets := by
    intro index
    have same : index = 0 := by
      apply Fin.ext
      have bound := index.isLt
      change index.val < 1 at bound
      change index.val = 0
      omega
    subst index
    rfl

abbrev rootLocated : Located state rootDemand where
  lower := rootInputs.lower
  upper := rootInputs.upper
  head := rootInputs.head
  target := rootInputs.target
  output := fun _ => .var 2
  arguments := rootInputs.arguments
  targets := rootInputs.targets
abbrev childLocated : Located state childDemand where
  lower := childInputs.lower
  upper := childInputs.upper
  head := childInputs.head
  target := childInputs.target
  output := fun _ => .var 0
  arguments := childInputs.arguments
  targets := childInputs.targets

abbrev rootItem : Item roles state := ⟨rootDemand, rootLocated⟩
abbrev childItem : Item roles state := ⟨childDemand, childLocated⟩
abbrev assignment : Assignment := fun _ => (.base .int, Common.rowEmpty)

theorem root_holds : rootLocated.equations.Holds assignment := by
  constructor
  · intro index; exact ⟨Common.subtype_refl _, Common.subtype_refl _⟩
  · intro index; exact Common.equivalent_refl _
theorem child_holds : childLocated.equations.Holds assignment := by
  constructor
  · intro index; exact ⟨Common.subtype_refl _, Common.subtype_refl _⟩
  · intro index; exact Common.equivalent_refl _

theorem joint_model : Models (record [rootItem, childItem]) assignment := by
  apply (GeneralDictionaryBatchRecording.batch_models _ _).mpr
  constructor
  · apply (GeneralSourceState.models_ordinary state assignment).mpr
    intro atom member; cases member
  · intro item member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact root_holds
    · exact child_holds

abbrev tree : GeneralDictionaryTransactions.Prepared roles state :=
  .node root 2 rootLocated [.node child 3 childLocated []]

theorem tree_items : tree.items = [rootItem, childItem] := rfl

theorem tree_joint_model : Models (record tree.items) assignment := joint_model

theorem retained_outputs : rootDemand.outputs = [⟨0, 3⟩, ⟨0, 4⟩] ∧
    childDemand.outputs = [⟨1, 2⟩] := ⟨rfl, rfl⟩


open GeneralDictionaryVariableTerms (compile build)
open GeneralDictionaryVariablePlans (Result lookup lookup_exact HeadInstances)

private theorem root_compile (index : Fin rootDemand.outputs.length) :
    compile state roles binderWrap capture (rootDemand.outputs[index]).name = some (.var 2) := by
  obtain ⟨index, bound⟩ := index
  change index < 2 at bound
  have cases : index = 0 ∨ index = 1 := by omega
  rcases cases with rfl | rfl <;> rfl

private theorem child_compile (index : Fin childDemand.outputs.length) :
    compile state roles leaf capture (childDemand.outputs[index]).name = some (.var 0) := by
  have same : index = 0 := by
    apply Fin.ext
    have bound := index.isLt
    change index.val < 1 at bound
    change index.val = 0
    omega
  subst index
  rfl

theorem root_build : build binderWrap capture rootInputs = some rootLocated := by
  have complete : ∀ index : Fin rootDemand.outputs.length,
      (compile state roles binderWrap capture (rootDemand.outputs[index]).name).isSome = true := by
    intro index; rw [root_compile index]; rfl
  unfold build
  rw [dite_eq_left complete]
  congr 1
  congr
  funext index
  simp only [root_compile index, Option.get_some]

theorem child_build : build leaf capture childInputs = some childLocated := by
  have complete : ∀ index : Fin childDemand.outputs.length,
      (compile state roles leaf capture (childDemand.outputs[index]).name).isSome = true := by
    intro index; rw [child_compile index]; rfl
  unfold build
  rw [dite_eq_left complete]
  congr 1
  congr
  funext index
  simp only [child_compile index, Option.get_some]

abbrev rootResult : Result state root := ⟨[child], rootLocated⟩
abbrev childResult : Result state child := ⟨[], childLocated⟩

theorem root_lookup : lookup registry registry_checked frame root 2 rootInputs = some rootResult := by
  apply (lookup_exact registry registry_checked frame root 2 rootInputs rootResult).mpr
  exact ⟨binderWrap, by simp, rfl, rfl, root_build, root_actual_children.symm⟩

theorem child_lookup : lookup registry registry_checked frame child 3 childInputs = some childResult := by
  apply (lookup_exact registry registry_checked frame child 3 childInputs childResult).mpr
  exact ⟨leaf, by simp, rfl, rfl, child_build, child_actual_children.symm⟩

/-- Head interpretation is explicitly assumed for both selected declarations.
In particular, rootInputs.head is not derived from binderWrap.head. -/
theorem tree_built (heads : HeadInstances roles state)
    (rootHead : heads root binderWrap capture rootInputs.head)
    (childHead : heads child leaf capture childInputs.head) :
    GeneralDictionaryVariableTransactions.Built registry registry_checked (fun _ => frame) heads tree := by
  refine GeneralDictionaryVariableTransactions.Built.node
    (registry := registry) (checked := registry_checked) (frames := fun _ => frame)
    (heads := heads) (root := root) (key := 2) rootInputs rootResult
    [.node child 3 childLocated []] root_lookup ?_ ?_ ?_
  · intro declaration present identity _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · exact rootHead
    · cases identity
  · rfl
  · intro subtree present
    have same := List.mem_singleton.mp present
    subst subtree
    refine GeneralDictionaryVariableTransactions.Built.node
      (registry := registry) (checked := registry_checked) (frames := fun _ => frame)
      (heads := heads) (root := child) (key := 3) childInputs childResult [] child_lookup ?_ ?_ ?_
    · intro declaration present identity _
      simp only [List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl
      · cases identity
      · exact childHead
    · rfl
    · intro subtree absent; cases absent

/-- One genuine finite tree with nonempty root and leaf output obligations,
conditional only on the explicit head interpretation boundary. -/
theorem uniform_completion (heads : HeadInstances roles state)
    (rootHead : heads root binderWrap capture rootInputs.head)
    (childHead : heads child leaf capture childInputs.head) :
    ∃ witness, Readback tree.root
        (erase tree.dictionary) witness ∧
      ∀ model, Models (record tree.items) model →
        Evidence (GeneralDictionaryVariableTransactions.SourceInstance registry registry_checked
          (fun _ => frame) heads model) witness :=
  GeneralDictionaryVariableTransactions.transaction_uniform registry registry_checked
    (fun _ => frame) heads tree (tree_built heads rootHead childHead)

/-- Joint recording propagates through the actual producer slot to the exact
captured input source, retaining each distinct occurrence of the root output. -/
theorem all_model_root_child_input (model : Assignment)
    (valid : Models (record tree.items) model) (index : Fin rootDemand.outputs.length) :
    Common.Equivalent (model (rootDemand.outputs[index]).target).1 (model 2).1 ∧
    Common.Equivalent (model 2).1 (model 0).1 ∧
    Common.Equivalent (model (rootDemand.outputs[index]).target).1 (model 0).1 := by
  have all := ((GeneralDictionaryBatchRecording.batch_models _ _).mp valid).2
  have rootHolds := all rootItem (by change rootItem ∈ [rootItem, childItem]; simp)
  have childHolds := all childItem (by change childItem ∈ [rootItem, childItem]; simp)
  have first : Common.Equivalent (model (rootDemand.outputs[index]).target).1 (model 2).1 :=
    rootHolds.2 index
  have second : Common.Equivalent (model 2).1 (model 0).1 := childHolds.2 ⟨0, by decide⟩
  exact ⟨first, second, Common.equivalent_trans first second⟩

end Yulang.GeneralDictionaryTerminalFixture
