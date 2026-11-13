import Yulang.GeneralNominalReachableSchemas

/-! Finite capture reconciliation uses global source-labelled replacements.
Positive bookkeeping depth increments allow one Trace growth function to
encode a whole finite sequence, including aliases. -/
namespace Yulang.GeneralNominalCaptureRefinement
open GeneralDeclarationPatterns GeneralNominalOriginTerms GeneralNominalRecursiveInspection
open GeneralNominalCaptureComparison GeneralNominalHoleElimination
open GeneralNominalReadbackFunctionality GeneralNominalScopedRecipeLabels
open GeneralNominalLabelledOriginClosure GeneralNominalCanonicalHoleJournal
open GeneralNominalIndexedHoleReadback GeneralNominalSourceLabelVocabulary
open GeneralNominalFiniteMeaning CommonNominalFullCarrier GeneralNominalSubtermOrder

variable {models : GeneralNominalCommonBridge.Assignment → Prop}
variable {identities : Nat → Nat} {keys : List Nat} {tests : List Test}

structure Operation where
  hole : Nat
  pattern : Pattern
  tree : Expr Nat
  extra : Nat

def Operation.updated (op : Operation) (inventory : Inventory) : Inventory :=
  eliminate inventory op.hole (GeneralNominalPatternInventory.encode op.pattern) op.extra

def transform : List Operation → Expr Nat → Expr Nat
  | [], term => term
  | op :: rest, term => transform rest (replace op.hole op.tree term)

inductive Refinement (models : GeneralNominalCommonBridge.Assignment → Prop)
    (context : GeneralNominalCandidates.Context) (identities : Nat → Nat)
    (keys : List Nat) (tests : List Test) : Inventory → Inventory → List Operation → Prop
  | refl (inventory) : Refinement models context identities keys tests inventory inventory []
  | next (op : Operation)
      (present : op.hole ∈ before.holes)
      (label : GeneralNominalOpenPatternLabels.Label context op.pattern op.tree)
      (readback : Readback models (fun name => .source (identities name)) (before.holes.erase op.hole)
        (.source (identities op.hole)) op.tree)
      (allowed : Allowed keys (before.holes.erase op.hole) op.pattern)
      (vocabulary : Vocabulary tests op.tree)
      (bounded : GeneralNominalSharedEnumeration.Bounded (before.holes.erase op.hole)
        (GeneralNominalSourceLabelVocabulary.tests keys) op.extra (GeneralNominalPatternInventory.encode op.pattern))
      (positive : 0 < op.extra)
      (rest : Refinement models context identities keys tests (op.updated before) after operations) :
      Refinement models context identities keys tests before after (op :: operations)

theorem trace_growth (trace : Trace tests first before after count)
    (equal : ∀ depth, before.depth ≤ depth → first depth = last depth) :
    Trace tests last before after count := by
  induction trace with
  | refl => exact .refl _
  | @next before after count hole value present closed bounded tail ih =>
    have atStart := equal before.depth (Nat.le_refl _)
    have next : Trace tests last (eliminate before hole value (first before.depth)) after count :=
      ih (fun depth below => equal depth (Nat.le_trans (Nat.le_add_right ..) below))
    rw [atStart] at bounded next
    exact .next hole value present closed bounded next

theorem prepend_trace (present : hole ∈ before.holes)
    (bounded : GeneralNominalSharedEnumeration.Bounded (before.holes.erase hole) tests extra value)
    (positive : 0 < extra)
    (tail : Trace tests growth (eliminate before hole value extra) after count) :
    ∃ combined, Trace tests combined before after (count+1) := by
  let combined : Nat → Nat := fun depth => if depth = before.depth then extra else growth depth
  have atStart : combined before.depth = extra := by simp only [combined,ite_true]
  have later : Trace tests combined (eliminate before hole value extra) after count := by
    apply trace_growth tail
    intro depth bound
    have different : depth ≠ before.depth := by change before.depth + extra ≤ depth at bound; omega
    simp only [combined,different,ite_false]
  refine ⟨combined,?_⟩
  have closed := bounded_closed bounded
  rw [← atStart] at bounded later
  exact .next hole value present closed bounded later

theorem Refinement.trace (refinement : Refinement models context identities keys tests before after operations) :
    ∃ growth, Trace (GeneralNominalSourceLabelVocabulary.tests keys) growth before after operations.length := by
  induction refinement with
  | refl => exact ⟨fun _ => 0,.refl _⟩
  | next op present label readback allowed vocabulary bounded positive rest ih =>
    obtain ⟨growth,tail⟩ := ih
    exact prepend_trace present bounded positive tail

theorem Refinement.count (refinement : Refinement models context identities keys tests before after operations) :
    operations.length + after.holes.length = before.holes.length ∧ operations.length ≤ before.holes.length := by
  obtain ⟨growth,trace⟩ := refinement.trace
  have count := trace_count trace
  exact ⟨count,by omega⟩

theorem Refinement.journal (refinement : Refinement models context identities keys tests before after operations)
    (journal : Journal context root state before) : Nonempty (Journal context root state after) := by
  induction refinement with
  | refl => exact ⟨journal⟩
  | next op present label readback allowed vocabulary bounded positive rest ih =>
    exact ih (journal.replace label op.hole op.extra)

theorem Refinement.readback (refinement : Refinement models context identities keys tests before after operations)
    (known : Readback models (fun name => .source (identities name)) before.holes root term) :
    Readback models (fun name => .source (identities name)) after.holes root (transform operations term) := by
  induction refinement generalizing root term with
  | refl => exact known
  | next op present label readback allowed vocabulary bounded positive rest ih =>
    exact ih (eliminate_readback known readback)

theorem replacement_equal (equal : EqualTerms models values (.leaf hole) tree) (term : Expr Nat) :
    EqualTerms models values (replace hole tree term) term := by
  induction term with
  | leaf name =>
    by_cases same : name = hole
    · subst name
      simpa only [replace,Expr.bind,substitute,ite_true] using equal_symm equal
    · simp only [replace,Expr.bind,substitute,same,ite_false]
      exact fun _ _ => ⟨subtype_refl _,subtype_refl _⟩
  | node test children ih =>
    intro model valid
    exact build_equal test _ _ (fun position => ih position model valid)

theorem replacement_canonical (canonical : Canonical term) (known : Canonical tree) :
    Canonical (replace hole tree term) := by
  apply GeneralNominalSettledLabelledLedger.canonical_bind term canonical
  intro name member
  simp only [substitute]
  split
  · exact known
  · trivial

theorem replacement_vocabulary (vocabulary : Vocabulary tests term) (known : Vocabulary tests tree) :
    Vocabulary tests (replace hole tree term) := by
  apply vocabulary_bind vocabulary
  intro name member
  simp only [substitute]
  split
  · exact known
  · trivial

def CommonMany (models : GeneralNominalCommonBridge.Assignment → Prop) (identities : Nat → Nat)
    (remaining : List Nat) (tests : List Test) (anchor : Expr Nat) (terms : List (Expr Nat)) : Prop :=
  ∃ term, Canonical term ∧ Vocabulary tests term ∧ Closed remaining term ∧ Below term anchor ∧
    (∀ other ∈ terms, Below term other) ∧ EqualTerms models (fun model name => (model (identities name)).1) term anchor

theorem reconcile
    (templates : NodeTemplates context keys tests) (inhabited : ∃ model, models model)
    (inventory : Inventory) (anchor : Expr Nat) (terms : List (Expr Nat))
    (canonical : Canonical anchor) (vocabulary : Vocabulary tests anchor) (closed : Closed inventory.holes anchor)
    (known : ∀ term ∈ terms, Canonical term ∧ Vocabulary tests term ∧ Closed inventory.holes term ∧
      EqualTerms models (fun model name => (model (identities name)).1) anchor term) :
    ∃ after operations, Refinement models context identities keys tests inventory after operations ∧
      CommonMany models identities after.holes tests (transform operations anchor) (terms.map (transform operations)) := by
  classical
  have all : ∀ length, ∀ inventory : Inventory, inventory.holes.length = length →
      ∀ (anchor : Expr Nat) (terms : List (Expr Nat)), Canonical anchor → Vocabulary tests anchor → Closed inventory.holes anchor →
      (∀ term ∈ terms, Canonical term ∧ Vocabulary tests term ∧ Closed inventory.holes term ∧
        EqualTerms models (fun model name => (model (identities name)).1) anchor term) →
      ∃ after operations, Refinement models context identities keys tests inventory after operations ∧
        CommonMany models identities after.holes tests (transform operations anchor) (terms.map (transform operations)) := by
    intro length
    induction Nat.lt_wfRel.wf.apply length with
    | intro length predecessors ih =>
      intro inventory size anchor terms canonical vocabulary closed known
      rcases compare_many inhabited anchor terms canonical vocabulary closed known with common | elimination
      · exact ⟨inventory,[],.refl _,by simpa only [transform,CommonMany,List.map_id'] using common⟩
      · obtain ⟨hole,present,value,shape,vocab,scope,equal⟩ := elimination
        obtain ⟨pattern,label,allowed⟩ := reify templates value vocab shape scope
        have readback : Readback models (fun name => .source (identities name)) (inventory.holes.erase hole)
            (.source (identities hole)) value := by
          refine ⟨?_,scope⟩
          intro model valid
          apply GeneralNominalUniformCaptureProduction.meaning_holds value shape
            (valuation := fun name => (model (identities name)).1)
          · exact ⟨⟨_,.source _⟩,by intro actual seen; cases seen; exact equal model valid⟩
          · intro name member
            exact ⟨⟨_,.source _⟩,by intro actual seen; cases seen; exact ⟨subtype_refl _,subtype_refl _⟩⟩
        obtain ⟨extra,bounded⟩ := encoded_bounded pattern allowed.1 allowed.2
        let op : Operation := ⟨hole,pattern,value,extra+1⟩
        have smaller : (op.updated inventory).holes.length < length := by
          change (inventory.holes.erase hole).length < length
          rw [List.length_erase_of_mem present,size]
          exact Nat.sub_lt (size ▸ List.length_pos_of_mem present) (by decide)
        have rootEqual := replacement_equal equal anchor
        have nextKnown : ∀ term ∈ terms.map (replace hole value),
            Canonical term ∧ Vocabulary tests term ∧ Closed (op.updated inventory).holes term ∧
            EqualTerms models (fun model name => (model (identities name)).1) (replace hole value anchor) term := by
          intro term member
          obtain ⟨old,present,rfl⟩ := List.mem_map.mp member
          have prior := known old present
          exact ⟨replacement_canonical prior.1 shape,replacement_vocabulary prior.2.1 vocab,
            replacement_closed prior.2.2.1 scope,
            equal_trans rootEqual (equal_trans prior.2.2.2 (equal_symm (replacement_equal equal old)))⟩
        obtain ⟨after,operations,rest,common⟩ := ih _ smaller (op.updated inventory) rfl
          (replace hole value anchor) (terms.map (replace hole value))
          (replacement_canonical canonical shape) (replacement_vocabulary vocabulary vocab)
          (replacement_closed closed scope) nextKnown
        refine ⟨after,op :: operations,Refinement.next op present label readback allowed vocab
          (GeneralNominalSharedEnumeration.bounded_mono bounded (Nat.le_succ _)) (Nat.zero_lt_succ _) rest,?_⟩
        simpa only [transform,op,List.map_map,Function.comp_def] using common
  exact all _ inventory rfl anchor terms canonical vocabulary closed known

end Yulang.GeneralNominalCaptureRefinement
