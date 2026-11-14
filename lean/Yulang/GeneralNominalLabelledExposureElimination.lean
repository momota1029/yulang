import Yulang.GeneralNominalSettledLabelledLedger

/-! Actual graph-backed exposure yields source-labelled global elimination.
The replacement code's budget is derived, and leaf/constructor capture
presentations become exactly equal after the same global replacement. -/
namespace Yulang.GeneralNominalLabelledExposureElimination
open GeneralDeclarationPatterns GeneralNominalOriginTerms GeneralNominalRecursiveInspection
open GeneralNominalIndexedHoleReadback GeneralNominalHoleElimination GeneralNominalOpenPatternLabels
open GeneralNominalSourceLabelVocabulary GeneralNominalLabelledOriginClosure GeneralNominalScopedRecipeLabels
open GeneralNominalCanonicalHoleJournal GeneralNominalBackedHoleElimination GeneralNominalFeedbackK2
open GeneralNominalReadbackFunctionality GeneralNominalSaturationState

variable {models : GeneralNominalCommonBridge.Assignment → Prop}
variable {origins : Nat → Origin} {remaining keys : List Nat} {tests : List Test}
variable {inventory : Inventory} {identities : Nat → Nat}

def Value.replace (value : Value models context origins remaining keys root)
    (replacement : Value models context origins (remaining.erase hole) keys (origins hole)) :
    Value models context origins (remaining.erase hole) keys root where
  pattern := normalize (value.pattern.subst (patternReplacement hole replacement.pattern))
  term := GeneralNominalHoleElimination.replace hole replacement.term value.term
  labelled := GeneralNominalUniformHoleLabels.replace_labelled value.labelled replacement.labelled
  allowed := by
    constructor
    · apply normalized_subst_scoped value.labelled.1.1 value.allowed.1
      · intro name
        by_cases equal : name = hole
        · simpa only [patternReplacement,equal,ite_true] using replacement.allowed.1
        · simp only [patternReplacement,equal,ite_false]; exact .var _
      · intro name
        exact (replacement_images replacement.labelled.1 name).1
    · apply GeneralPatternVariableProvenance.normalize_uses
      refine subst_uses value.pattern value.allowed.2
        (substitution := patternReplacement hole replacement.pattern)
        (surviving := fun name => name ∈ remaining.erase hole) ?_
      intro name member
      by_cases equal : name = hole
      · simpa only [patternReplacement,equal,ite_true] using replacement.allowed.2
      · simp only [patternReplacement,equal,ite_false]
        intro actual present
        cases List.mem_singleton.mp present
        exact (List.mem_erase_of_ne equal).mpr member

theorem replace_absent (absent : hole ∉ term.leaves) :
    replace hole value term = term := by
  induction term with
  | leaf name =>
    have different : name ≠ hole := by intro equal; exact absent (by simp [equal,Expr.leaves])
    simp only [replace,Expr.bind,substitute,different,ite_false]
  | node test children ih =>
    change Expr.node test _ = Expr.node test children
    congr 1
    funext position
    apply ih position
    intro member
    exact absent (List.mem_flatten.mpr ⟨_,List.mem_ofFn.mpr ⟨position,rfl⟩,member⟩)

theorem capture_pair_equal (absent : hole ∉ tree.leaves) :
    replace hole tree (.leaf hole) = replace hole tree tree := by
  rw [replace_absent absent]
  simp only [replace,Expr.bind,substitute,ite_true]

theorem capture_pair_below (absent : hole ∉ tree.leaves) :
    GeneralNominalSubtermOrder.Below (replace hole tree (.leaf hole)) (replace hole tree tree) :=
  (capture_pair_equal absent) ▸ GeneralNominalSubtermOrder.Below.refl

/-- The source label and the finite inventory-code depth are conclusions.
The remaining producer premises concern actual meaning, source templates,
and real K2 graph backing, rather than a future ancestry bound. -/
theorem discharge (state : State roles)
    (templates : NodeTemplates context keys tests)
    (old : Readback (Models state) (fun name => .source (identities name)) inventory.holes
      (.source actual) (.leaf hole))
    (expanded : Readback (Models state) (fun name => .source (identities name)) inventory.holes
      (.source actual) (.node test children))
    (canonical : Canonical (.node test children))
    (vocabulary : Vocabulary tests (.node test children))
    (backed : Backed state identities actual (.node test children))
    (inhabited : ∃ model, Models state model) (safe : ¬ RecursAt state actual) :
    ∃ replacement : Value (Models state) context (fun name => .source (identities name))
        (inventory.holes.erase hole) keys (.source (identities hole)),
      replacement.term = .node test children ∧
      (∃ extra, Trace (GeneralNominalSourceLabelVocabulary.tests keys) (fun _ => extra) inventory
        (eliminate inventory hole (GeneralNominalPatternInventory.encode replacement.pattern) extra) 1) ∧
      replace hole replacement.term (.leaf hole) = replace hole replacement.term (.node test children) := by
  have reduced := GeneralNominalReducedHoleSources.discharge old expanded backed inhabited safe
  have absent : hole ∉ (Expr.node test children).leaves := fun member =>
    safe (occurs_rejected backed (GeneralNominalReducedHoleSources.leaf_equal old) member inhabited)
  obtain ⟨pattern,label,scope⟩ := reify templates (.node test children) vocabulary canonical reduced.2.2
  exact ⟨⟨pattern,.node test children,⟨label,reduced.2⟩,scope⟩,rfl,
    GeneralNominalSourceLabelVocabulary.replacement_trace inventory reduced.1 scope,capture_pair_equal absent⟩

/-- A zero-length source alias is resolved by exactly the same global
operation; the replacement uses the surviving hole's existing identity. -/
theorem alias_discharge (member : other ∈ inventory.holes) (present : hole ∈ inventory.holes)
    (different : other ≠ hole)
    (same : ∀ model, models model → Same model (origins hole) (origins other)) :
    ∃ replacement : Value models context origins (inventory.holes.erase hole) keys (origins hole),
      replacement.term = .leaf other ∧
      Trace (GeneralNominalSourceLabelVocabulary.tests keys) (fun _ => 0) inventory
        (eliminate inventory hole (.leaf other) 0) 1 ∧
      replace hole replacement.term (.leaf hole) = replace hole replacement.term (.leaf other) := by
  have remains := (List.mem_erase_of_ne different).mpr member
  refine ⟨source_value remains same,rfl,.next hole (.leaf other) present ?_ (.leaf other 0 remains) (.refl _),?_⟩
  · intro name included
    cases List.mem_singleton.mp included
    exact remains
  · apply capture_pair_equal
    change hole ∉ (Expr.leaf other).leaves
    simpa only [Expr.leaves,List.mem_singleton] using Ne.symm different

end Yulang.GeneralNominalLabelledExposureElimination
