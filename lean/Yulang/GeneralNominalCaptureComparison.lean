import Yulang.GeneralNominalCommonTrustedLedger

/-! Repeated finite capture trees have a common substitution-stable lower
presentation, or expose a genuine hole replacement. Cyclic opaque leaves
can stay opaque; no pre-refinement mass choice is made. -/
set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCaptureComparison
open GeneralNominalOriginTerms GeneralNominalRecursiveInspection GeneralNominalFiniteMeaning
open GeneralNominalReadbackFunctionality GeneralNominalScopedRecipeLabels
open GeneralNominalHoleElimination GeneralNominalSubtermOrder CommonNominalFullCarrier

variable {M : α → Prop} {values : α → Nat → Ty} {remaining : List Nat} {tests : List Test}

def EqualTerms (M : α → Prop) (values : α → Nat → Ty) (first last : Expr Nat) : Prop :=
  ∀ model, M model → Equivalent (denote (values model) first) (denote (values model) last)

def Common (M : α → Prop) (values : α → Nat → Ty) (remaining : List Nat) (tests : List Test)
    (first last : Expr Nat) : Prop :=
  ∃ term, Canonical term ∧ Vocabulary tests term ∧ Closed remaining term ∧
    Below term first ∧ Below term last ∧ EqualTerms M values term first

def Elimination (M : α → Prop) (values : α → Nat → Ty) (remaining : List Nat) (tests : List Test) : Prop :=
  ∃ hole ∈ remaining, ∃ term, Canonical term ∧ Vocabulary tests term ∧ Closed (remaining.erase hole) term ∧
    EqualTerms M values (.leaf hole) term

theorem equal_symm (equal : EqualTerms M values first last) : EqualTerms M values last first :=
  fun model valid => ⟨(equal model valid).2,(equal model valid).1⟩

theorem equal_trans (one : EqualTerms M values first middle) (two : EqualTerms M values middle last) :
    EqualTerms M values first last := fun model valid =>
  ⟨subtype_trans (one model valid).1 (two model valid).1,
    subtype_trans (two model valid).2 (one model valid).2⟩

theorem common_symm (common : Common M values remaining tests first last)
    (equal : EqualTerms M values first last) : Common M values remaining tests last first := by
  obtain ⟨term,canonical,vocabulary,closed,one,two,meaning⟩ := common
  exact ⟨term,canonical,vocabulary,closed,two,one,equal_trans meaning equal⟩

theorem leaf_below (member : hole ∈ term.leaves) : Below (.leaf hole) term := by
  induction term with
  | leaf name => cases List.mem_singleton.mp member; exact .refl
  | node test children ih =>
    obtain ⟨leaves,present,member⟩ := List.mem_flatten.mp member
    obtain ⟨position,rfl⟩ := List.mem_ofFn.mp present
    exact .child test children position (ih position member)

theorem leaf_compare (present : hole ∈ remaining) (canonical : Canonical term)
    (vocabulary : Vocabulary tests term) (closed : Closed remaining term)
    (equal : EqualTerms M values (.leaf hole) term) :
    Common M values remaining tests (.leaf hole) term ∨ Elimination M values remaining tests := by
  classical
  by_cases occurs : hole ∈ term.leaves
  · exact Or.inl ⟨.leaf hole,trivial,trivial,by
      intro name member; cases List.mem_singleton.mp member; exact present,
      .refl,leaf_below occurs,fun _ _ => ⟨subtype_refl _,subtype_refl _⟩⟩
  · refine Or.inr ⟨hole,present,term,canonical,vocabulary,?_,equal⟩
    intro name member
    exact (List.mem_erase_of_ne (show name ≠ hole from fun same => occurs (same ▸ member))).mpr (closed name member)

theorem build_children_equal (test : Test) (canonical : TestCanonical test)
    (first last : Fin (arity test) → Ty)
    (equal : Equivalent (build test first) (build test last)) :
    ∀ position, Equivalent (first position) (last position) := by
  intro position
  cases test with
  | scalar => exact Fin.elim0 position
  | structural shape =>
    simp only [arity] at first last position
    exact GeneralNominalStructuralReadback.shape_payload (index := position.val) shape canonical _ _
      (List.length_ofFn ..) (List.length_ofFn ..)
      (by simp [position.isLt]) (by simp [position.isLt]) equal
  | nominal name count =>
    have same := ((nominal_regular_invariant_exact ..).mp equal.1).2.2 position.val
      (.inl (first position)) (.inl (last position))
      (by simp [position.isLt]) (by simp [position.isLt])
    exact same

theorem build_equal (test : Test) (first last : Fin (arity test) → Ty)
    (equal : ∀ position, Equivalent (first position) (last position)) :
    Equivalent (build test first) (build test last) := by
  cases test with
  | scalar => exact ⟨subtype_refl _,subtype_refl _⟩
  | structural shape =>
    simp only [arity] at first last equal
    change Equivalent (shapeValue shape (List.ofFn first)) (shapeValue shape (List.ofFn last))
    exact shape_congr shape (List.ofFn first) (List.ofFn last) (fun position => by
      simpa only [List.getElem?_ofFn,dite_eq_left position.isLt,Option.getD_some] using equal position)
  | nominal name count =>
    have forward (a b : Fin count → Ty) (same : ∀ i, Equivalent (a i) (b i)) :
        Subtype (nominal name (List.ofFn fun i => .inl (a i)))
          (nominal name (List.ofFn fun i => .inl (b i))) := by
      apply (nominal_regular_invariant_exact ..).mpr
      refine ⟨rfl,by simp,?_⟩
      intro index x y firstFound lastFound
      have bound : index < count := by
        have bound := (List.getElem?_eq_some_iff.mp firstFound).1
        simpa only [List.length_ofFn] using bound
      simp only [List.getElem?_ofFn,bound,dite_eq_left] at firstFound lastFound
      cases firstFound; cases lastFound
      exact same ⟨index,bound⟩
    exact ⟨forward first last equal,forward last first (fun i => ⟨(equal i).2,(equal i).1⟩)⟩

theorem compare (inhabited : ∃ model, M model)
    (first last : Expr Nat) (firstCanonical : Canonical first) (lastCanonical : Canonical last)
    (firstVocabulary : Vocabulary tests first) (lastVocabulary : Vocabulary tests last)
    (firstClosed : Closed remaining first) (lastClosed : Closed remaining last)
    (equal : EqualTerms M values first last) :
    Common M values remaining tests first last ∨ Elimination M values remaining tests := by
  classical
  induction first generalizing last with
  | leaf hole => exact leaf_compare (firstClosed hole (List.mem_singleton_self _)) lastCanonical lastVocabulary lastClosed equal
  | node test children ih =>
    cases last with
    | leaf hole =>
      rcases leaf_compare (lastClosed hole (List.mem_singleton_self _)) firstCanonical firstVocabulary firstClosed (equal_symm equal)
        with common | elimination
      · exact Or.inl (common_symm common (equal_symm equal))
      · exact Or.inr elimination
    | node other targets =>
      obtain ⟨model,valid⟩ := inhabited
      have same := GeneralNominalFiniteHeadInversion.test_equal test other _ _
        firstCanonical.1 lastCanonical.1 (equal model valid)
      cases same
      have compared (position : Fin (arity test)) :
          Common M values remaining tests (children position) (targets position) ∨ Elimination M values remaining tests :=
        ih position (targets position) (firstCanonical.2 position) (lastCanonical.2 position)
          (firstVocabulary.2 position) (lastVocabulary.2 position)
          (GeneralNominalOpenCaptureLabels.child_closed firstClosed position)
          (GeneralNominalOpenCaptureLabels.child_closed lastClosed position)
          (fun model valid => build_children_equal test firstCanonical.1 _ _ (equal model valid) position)
      by_cases elimination : Elimination M values remaining tests
      · exact Or.inr elimination
      · have common (position) := (compared position).resolve_right elimination
        let chosen : Fin (arity test) → Expr Nat := fun position => Classical.choose (common position)
        have chosenFacts (position) := Classical.choose_spec (common position)
        refine Or.inl ⟨.node test chosen,⟨firstCanonical.1,fun i => (chosenFacts i).1⟩,
          ⟨firstVocabulary.1,fun i => (chosenFacts i).2.1⟩,?_,
          .node test chosen children (fun i => (chosenFacts i).2.2.2.1),
          .node test chosen targets (fun i => (chosenFacts i).2.2.2.2.1),?_⟩
        · intro name member
          obtain ⟨leaves,present,member⟩ := List.mem_flatten.mp member
          obtain ⟨i,rfl⟩ := List.mem_ofFn.mp present
          exact (chosenFacts i).2.2.1 name member
        · intro model valid
          exact build_equal test _ _ (fun i => (chosenFacts i).2.2.2.2.2 model valid)

theorem common_survives (common : Common M values remaining tests first last)
    (replacement : Nat → Expr Nat) :
    ∃ term : Expr Nat, Below (term.bind replacement) (first.bind replacement) ∧
      Below (term.bind replacement) (last.bind replacement) := by
  obtain ⟨term,_,_,_,one,two,_⟩ := common
  exact ⟨term,below_bind one replacement,below_bind two replacement⟩

theorem compare_many (inhabited : ∃ model, M model)
    (anchor : Expr Nat) (terms : List (Expr Nat))
    (canonical : Canonical anchor) (vocabulary : Vocabulary tests anchor) (closed : Closed remaining anchor)
    (known : ∀ term ∈ terms, Canonical term ∧ Vocabulary tests term ∧ Closed remaining term ∧
      EqualTerms M values anchor term) :
    (∃ term, Canonical term ∧ Vocabulary tests term ∧ Closed remaining term ∧ Below term anchor ∧
      (∀ other ∈ terms, Below term other) ∧ EqualTerms M values term anchor) ∨
      Elimination M values remaining tests := by
  induction terms generalizing anchor with
  | nil =>
    exact Or.inl ⟨anchor,canonical,vocabulary,closed,.refl,by simp,
      fun _ _ => ⟨subtype_refl _,subtype_refl _⟩⟩
  | cons first rest ih =>
    have head := known first (List.mem_cons_self ..)
    rcases compare inhabited anchor first canonical head.1 vocabulary head.2.1 closed head.2.2.1 head.2.2.2
      with common | elimination
    · obtain ⟨middle,shape,vocab,scope,one,two,meaning⟩ := common
      have tail : ∀ term ∈ rest, Canonical term ∧ Vocabulary tests term ∧ Closed remaining term ∧
          EqualTerms M values middle term := by
        intro term member
        have old := known term (List.mem_cons_of_mem _ member)
        exact ⟨old.1,old.2.1,old.2.2.1,equal_trans meaning old.2.2.2⟩
      rcases ih middle shape vocab scope tail with result | elimination
      · obtain ⟨term,shape,vocab,scope,below,others,same⟩ := result
        refine Or.inl ⟨term,shape,vocab,scope,.trans below one,?_,equal_trans same meaning⟩
        intro other member
        rcases List.mem_cons.mp member with rfl | member
        · exact .trans below two
        · exact others other member
      · exact Or.inr elimination
    · exact Or.inr elimination

theorem elimination_value
    {models : GeneralNominalCommonBridge.Assignment → Prop} {identities : Nat → Nat}
    (templates : NodeTemplates context keys tests)
    (found : Elimination models (fun model name => (model (identities name)).1) inventory.holes tests) :
    ∃ hole ∈ inventory.holes,
      ∃ replacement : GeneralNominalLabelledOriginClosure.Value models context
        (fun name => .source (identities name)) (inventory.holes.erase hole) keys (.source (identities hole)),
        Vocabulary tests replacement.term ∧ ∃ extra,
          Trace (GeneralNominalSourceLabelVocabulary.tests keys) (fun _ => extra) inventory
            (eliminate inventory hole (GeneralNominalPatternInventory.encode replacement.pattern) extra) 1 := by
  obtain ⟨hole,present,term,canonical,vocabulary,closed,equal⟩ := found
  obtain ⟨pattern,label,allowed⟩ := reify templates term vocabulary canonical closed
  have readback : GeneralNominalIndexedHoleReadback.Readback models
      (fun name => .source (identities name)) (inventory.holes.erase hole) (.source (identities hole)) term := by
    refine ⟨?_,closed⟩
    intro model valid
    apply GeneralNominalUniformCaptureProduction.meaning_holds term canonical
      (valuation := fun name => (model (identities name)).1)
    · exact ⟨⟨_,.source _⟩,by intro actual seen; cases seen; exact equal model valid⟩
    · intro name member
      exact ⟨⟨_,.source _⟩,by intro actual seen; cases seen; exact ⟨subtype_refl _,subtype_refl _⟩⟩
  exact ⟨hole,present,⟨pattern,term,⟨label,readback⟩,allowed⟩,vocabulary,
    GeneralNominalSourceLabelVocabulary.replacement_trace inventory present allowed⟩

end Yulang.GeneralNominalCaptureComparison
