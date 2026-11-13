import Yulang.GeneralDictionary169FiniteCoverage
import Yulang.GeneralDictionaryMixed168Display

/-! The existing actual Shared Display installation supplies local structural
coverage independently of its previously assembled MixedTree. Its chosen-child
graph is accessible: one recorded node followed by a source scalar leaf. -/
namespace Yulang.GeneralDictionary169FiniteDisplay
open GeneralNominalExamples GeneralDeclarations GeneralNominalSaturationState
open GeneralDeclarationExamples (roles)
open GeneralSourceDictionaries
open GeneralDictionarySharedDisplayInstallation (after)
open GeneralNominalSharedExamples (packet)
open GeneralDictionary169FiniteCoverage

abbrev Domain (occurrence : Occurrence roles) : Prop := occurrence = displayRoot ∨ occurrence = displayChild

private theorem distinct : displayChild ≠ displayRoot := by
  intro same
  have identities := congrArg (fun o : Occurrence roles => o.identity) same
  have different : displayChild.identity ≠ displayRoot.identity := by decide +kernel
  exact different identities

noncomputable def node (occurrence : Occurrence roles) (member : Domain occurrence) : Node registry after occurrence := by
  classical
  by_cases same : occurrence = displayRoot
  · subst occurrence
    exact .recorded (packet false) (List.mem_singleton_self _) GeneralDictionaryMixed168Display.parent_relocates
  · have child : occurrence = displayChild := member.resolve_left same
    subst occurrence
    exact .scalar displayChild intDisplay (by simp) int_display_checked GeneralDictionaryMixed168Display.leaf_shape

private theorem root_children (member : Domain displayRoot) :
    (node displayRoot member).children = [displayChild] := by
  classical
  simp [node,Node.children,GeneralDictionarySharedDisplayInstallation.children]

private theorem leaf_children (member : Domain displayChild) :
    (node displayChild member).children = [] := by
  classical
  simp only [node,dite_eq_right distinct,Node.children]

noncomputable def coverage : Coverage registry after Domain where
  node := node
  closed := by
    intro occurrence member child present
    rcases member with same | same
    · subst occurrence
      rw [root_children] at present
      exact Or.inr (List.mem_singleton.mp present)
    · subst occurrence
      rw [leaf_children] at present
      cases present

private theorem child_is_leaf (first last : Subtype Domain) (edge : Child coverage first last) :
    first.val = displayChild ∧ last.val = displayRoot := by
  rcases last with ⟨last,member⟩
  change first.val ∈ (node last member).children at edge
  rcases member with rfl | rfl
  · rw [root_children] at edge
    exact ⟨List.mem_singleton.mp edge,rfl⟩
  · rw [leaf_children] at edge
    cases edge

theorem accessible : Acc (Child coverage) (⟨displayRoot,Or.inl rfl⟩ : Subtype Domain) := by
  constructor
  intro child edge
  have leaf := (child_is_leaf child _ edge).1
  constructor
  intro next nextEdge
  have root := (child_is_leaf next child nextEdge).2
  exact False.elim (distinct (leaf.symm.trans root))

theorem uniform_dictionary :
    ∃ payload, GeneralDictionaryMixed168Tree.MixedTree registry after displayRoot payload ∧
      ∀ model, Models after.current model →
        GeneralDictionaryRecursiveEvidence.Evidence registry after.current.context model displayRoot payload :=
  GeneralDictionary169FiniteCoverage.uniform_dictionary coverage ⟨displayRoot,Or.inl rfl⟩ accessible
    GeneralDictionarySharedRecursiveExample.formed

/-- This interpretation is inhabited; no new dictionary semantics or actual
Stable result is claimed. -/
theorem nonvacuous :
    ∃ payload, GeneralDictionaryMixed168Tree.MixedTree registry after displayRoot payload ∧
      ∃ model, Models after.current model ∧
        GeneralDictionaryRecursiveEvidence.Evidence registry after.current.context model displayRoot payload := by
  obtain ⟨payload,tree,evidence⟩ := uniform_dictionary
  obtain ⟨model,valid⟩ := GeneralDictionarySharedDisplayInstallation.inhabited
  exact ⟨payload,tree,model,valid,evidence model valid⟩
end Yulang.GeneralDictionary169FiniteDisplay
