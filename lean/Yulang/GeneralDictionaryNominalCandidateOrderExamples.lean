import Yulang.GeneralDictionaryNominalCandidateOrder
import Yulang.GeneralDictionaryNominalCandidateReadbackExamples

/-!
# Computed-frame order regressions

The existing nominal fixture supplies a nontrivial visible-list reversal with
successful readback and omitted-child failure. Its where lists are singleton or
empty; the separate where-swap theorem is proof-parametric in a checked
multi-clause declaration, not a claim about a concrete multi-clause fixture.
-/
namespace Yulang.GeneralDictionaryNominalCandidateOrderExamples
open GeneralDeclarations GeneralSourceDictionaries GeneralDictionaryReadback
open GeneralNominalExamples
open GeneralDeclarationExamples (constructors roles display wrap)
open GeneralDictionaryNominalCandidateReadbackExamples (payload sourceTree)
open GeneralDictionaryNominalCandidateReadback

abbrev reversed : Registry := ⟨constructors, roles, [wrap, display, intDisplay]⟩

theorem visible_reversed : GeneralRegistryReordering.Reorders registry reversed := by
  refine ⟨rfl, rfl, [wrap, display, intDisplay], ?_, ?_⟩
  · exact (List.reverse_perm [intDisplay, display, wrap]).symm
  · exact .cons (GeneralRegistryReordering.declarationReorders_refl _)
      (.cons (GeneralRegistryReordering.declarationReorders_refl _)
        (.cons (GeneralRegistryReordering.declarationReorders_refl _) .nil))

theorem reversed_checked : Checked reversed :=
  GeneralRegistryReordering.reorders_checked visible_reversed registry_checked

theorem visible_order_changes : registry.declarations ≠ reversed.declarations := by
  decide +kernel

theorem computed_frames_preserved : frames registry (context true) = frames reversed (context true) :=
  GeneralDictionaryNominalCandidateOrder.frames_reorders constructors roles _ _ reversed_checked
    visible_reversed (context true)

/-- The concrete reconstructed source identities and demands are unchanged. -/
theorem reversed_tree_reconstructed :
    reconstruct reversed reversed_checked (context true) payload displayRoot = some sourceTree := by
  rw [← GeneralDictionaryNominalCandidateOrder.reconstruct_reorders constructors roles _ _
    registry_checked reversed_checked visible_reversed (context true) payload displayRoot]
  exact GeneralDictionaryNominalCandidateReadbackExamples.tree_reconstructed

theorem reversed_omitted_child_defers :
    reconstruct reversed reversed_checked (context true) (.node 1 []) displayRoot = none := by
  rw [← GeneralDictionaryNominalCandidateOrder.reconstruct_reorders constructors roles _ _
    registry_checked reversed_checked visible_reversed (context true) (.node 1 []) displayRoot]
  exact GeneralDictionaryNominalCandidateReadbackExamples.omitted_child_defers

/-- Neither an unknown key nor reordering manufactures captured inputs. -/
theorem absent_key_preserved : declaration registry displayRoot 99 = none ∧
    declaration reversed displayRoot 99 = none := by
  have absent : declaration registry displayRoot 99 = none := by rfl
  exact ⟨absent, GeneralDictionaryNominalCandidateOrder.declaration_none_reorders
    constructors roles _ _ visible_reversed displayRoot 99 absent⟩

theorem absent_bindings_preserved : bindings registry (context true) displayRoot 99 = [] ∧
    bindings reversed (context true) displayRoot 99 = [] := by
  constructor
  · simp only [bindings, absent_key_preserved.1]
  · simp only [bindings, absent_key_preserved.2]

/-- Preparation remains partial; this asserts equality rather than success. -/
theorem preparation_preserved :
    GeneralDictionaryNominalCandidateEvidence.prepare registry registry_checked (context true) payload displayRoot =
      GeneralDictionaryNominalCandidateEvidence.prepare reversed reversed_checked (context true) payload displayRoot :=
  GeneralDictionaryNominalCandidateOrder.prepare_reorders constructors roles _ _ registry_checked
    reversed_checked visible_reversed (context true) payload displayRoot

/-- Structural reconstruction failure is retained by preparation. -/
theorem reversed_omitted_preparation_defers :
    GeneralDictionaryNominalCandidateEvidence.prepare reversed reversed_checked (context true)
      (.node 1 []) displayRoot = none := by
  unfold GeneralDictionaryNominalCandidateEvidence.prepare GeneralDictionaryPayloadPreparation.prepare
  change (GeneralDictionaryNominalCandidateReadback.reconstruct reversed reversed_checked (context true)
    (.node 1 []) displayRoot).bind _ = none
  rw [reversed_omitted_child_defers]
  rfl

/-- A genuine adjacent where swap, conditional on the original declaration's
checkedness. No concrete multi-clause nominal fixture is claimed here. -/
theorem where_swap_reorders (declaration : Declaration) (left right : Clause) (rest : List Clause)
    (clauses : declaration.requirements = left :: right :: rest) :
    GeneralRegistryReordering.Reorders (⟨constructors, roles, [declaration]⟩ : Registry)
      ⟨constructors, roles, [{ declaration with requirements := right :: left :: rest }]⟩ := by
  refine ⟨rfl, rfl, [declaration], .refl _, .cons ?_ .nil⟩
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl⟩
  rw [clauses]
  exact List.Perm.swap _ _ _

theorem where_swap_computed_frames (declaration : Declaration) (left right : Clause) (rest : List Clause)
    (clauses : declaration.requirements = left :: right :: rest)
    (checked : Checked ⟨constructors, roles, [declaration]⟩)
    (fixed : GeneralNominalCandidates.Context) :
    frames ⟨constructors, roles, [declaration]⟩ fixed =
      frames ⟨constructors, roles, [{ declaration with requirements := right :: left :: rest }]⟩ fixed := by
  have order := where_swap_reorders declaration left right rest clauses
  exact GeneralDictionaryNominalCandidateOrder.frames_reorders constructors roles _ _
    (GeneralRegistryReordering.reorders_checked order checked) order fixed

/-- Distinct clauses really change the declaration's stored enumeration. -/
theorem where_swap_changes (declaration : Declaration) (left right : Clause) (rest : List Clause)
    (clauses : declaration.requirements = left :: right :: rest) (distinct : left ≠ right) :
    declaration ≠ { declaration with requirements := right :: left :: rest } := by
  intro equal
  have lists := congrArg Declaration.requirements equal
  rw [clauses] at lists
  exact distinct (List.cons.inj lists).1

/-- Both no-caller-Frames optional executors retain their results for the same
proof-parametric adjacent where swap, including failure. -/
theorem where_swap_executors (declaration : Declaration) (left right : Clause) (rest : List Clause)
    (clauses : declaration.requirements = left :: right :: rest)
    (checked : Checked ⟨constructors, roles, [declaration]⟩)
    (fixed : GeneralNominalCandidates.Context) (raw : Payload) (root : Occurrence roles) :
    let moved : Registry := ⟨constructors, roles, [{ declaration with requirements := right :: left :: rest }]⟩
    let movedChecked := GeneralRegistryReordering.reorders_checked
      (where_swap_reorders declaration left right rest clauses) checked
    reconstruct ⟨constructors, roles, [declaration]⟩ checked fixed raw root =
      reconstruct moved movedChecked fixed raw root ∧
    GeneralDictionaryNominalCandidateEvidence.prepare ⟨constructors, roles, [declaration]⟩ checked fixed raw root =
      GeneralDictionaryNominalCandidateEvidence.prepare moved movedChecked fixed raw root := by
  have order := where_swap_reorders declaration left right rest clauses
  exact ⟨GeneralDictionaryNominalCandidateOrder.reconstruct_reorders constructors roles _ _
      checked (GeneralRegistryReordering.reorders_checked order checked) order fixed raw root,
    GeneralDictionaryNominalCandidateOrder.prepare_reorders constructors roles _ _
      checked (GeneralRegistryReordering.reorders_checked order checked) order fixed raw root⟩

end Yulang.GeneralDictionaryNominalCandidateOrderExamples
