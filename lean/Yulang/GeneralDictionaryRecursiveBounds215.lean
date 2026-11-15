import Yulang.GeneralDictionaryStructuralProjection215
import Yulang.GeneralDictionaryDefaultNominalProjection215
set_option backward.isDefEq.respectTransparency false

/-! Recursive actual observations remain within the inspected intervals.
Only current source Models, root interval containment and semantic schema tests
are used; no point-input or finite-center hypothesis is imposed. -/
namespace Yulang.GeneralDictionaryRecursiveBounds215
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalInspection (Query Bounds)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryStructuralProjection215 (Bounded)
open GeneralNominalOriginTerms (Head)
open GeneralNominalFiniteBracket (reindex)

def Anchors (state : GeneralNominalState.State) (model : Assignment) (report : Report state) : Prop :=
  ∀ anchor ∈ report.anchors, Bounded state model anchor.2 anchor.1

theorem appended (one : Anchors state model first) (two : Anchors state model last) :
    Anchors state model (first.append last) := by
  intro anchor member
  exact (List.mem_append.mp member).elim (one anchor) (two anchor)

theorem visited (bounded : Bounded state model bounds origin) (rest : Anchors state model report) :
    Anchors state model (report.visit bounds (some origin) test) := by
  intro anchor member
  simp only [Report.visit,Option.toList_some,List.map_cons,List.map_nil,List.singleton_append,List.mem_cons] at member
  rcases member with rfl | member
  · exact bounded
  · exact rest anchor member

mutual
 theorem inspect_bounds (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model) (query : Query) (bounds : Bounds state) (origin : Origin)
    (bounded : Bounded state model bounds origin)
    (tests : ∀ test ∈ (schema query origin .actual).tests, Head model test.1 test.2) :
    Anchors state model (inspect state query bounds (some origin)) := by
  cases query with
  | variables names =>
    intro anchor member
    simp only [inspect,Option.toList_some,List.map_cons,List.map_nil,List.mem_singleton] at member
    cases member
    exact bounded
  | deferred reason => intro anchor member; simp only [inspect,block,List.not_mem_nil] at member
  | scalar base =>
    simp only [inspect]
    apply visited bounded
    split
    · intro anchor member; cases member
    · split
      · split <;> intro anchor member <;> cases member
      · intro anchor member; cases member
      · intro anchor member; cases member
  | node shape children =>
    simp only [inspect]
    apply visited bounded
    split
    · rename_i lowerKind lower upperKind upper lowerAt upperAt
      split
      · rename_i matching
        have head := tests (origin,.structural shape) (by simp [schema])
        have childTests : ∀ test ∈ (schemas children (fun i => .structural origin shape i) .actual 0).tests,
            Head model test.1 test.2 := by
          intro test member
          apply tests test
          simpa only [schema] using List.mem_cons_of_mem (origin,.structural shape) member
        apply many_bounds state model valid children _ (fun i => .structural origin shape i) 0 _ childTests
        intro index
        have length : ((List.ofFn lower).zip (List.ofFn upper)).length = shape.arity := by
          simp only [List.length_zip,List.length_ofFn,matching.1,matching.2,Nat.min_self]
        let position : Fin shape.arity := ⟨index.val,by rw [← length]; exact index.isLt⟩
        have result := GeneralDictionaryStructuralProjection215.structural_child state model valid bounds
          lowerKind upperKind lower upper lowerAt upperAt matching.1 matching.2 bounded head position
        simpa only [Fin.getElem_fin,List.getElem_zip,List.getElem_ofFn,reindex,position,Nat.zero_add] using result
      · intro anchor member; cases member
    · intro anchor member; cases member
    · intro anchor member; cases member
  | nominal name children =>
    simp only [inspect]
    apply visited bounded
    split
    · split <;> intro anchor member <;> cases member
    · rename_i lower lowerAt
      split
      · rename_i named
        split
        · intro anchor member; cases member
        · rename_i intervals found
          have childTests : ∀ test ∈ (schemas children (fun i => .nominal origin name i) .actual 0).tests,
              Head model test.1 test.2 := by
            intro test member
            apply tests test
            simpa only [schema] using List.mem_cons_of_mem (origin,.nominal name children.length) member
          have left : Anchors state model (inspectMany state children intervals
              (fun i => some (.nominal origin name i)) 0) := by
            apply many_bounds state model valid children intervals (fun i => .nominal origin name i) 0 _ childTests
            intro index
            have head : Head model origin (.nominal lower.declaration.name children.length) := by
              rw [named]
              exact tests (origin,.nominal name children.length) (by simp [schema])
            have result := GeneralDictionaryDefaultNominalProjection215.nominal_bounded valid bounds.1 lower lowerAt found
              (fun value seen => Or.inl (bounded.2 value seen).1) head index
            simpa only [named,Nat.zero_add,Bounded,GeneralDictionaryDefaultNominalProjection215.Bounded] using result
          simp only [Option.getD_some]
          split
          · exact left
          · split
            · intro anchor member; cases member
            · rename_i upper upperAt
              split
              · rename_i upperNamed
                split
                · intro anchor member; cases member
                · rename_i targets upperFound
                  apply appended left
                  apply many_bounds state model valid children targets (fun i => .nominal origin name i) 0 _ childTests
                  intro index
                  have head : Head model origin (.nominal upper.declaration.name children.length) := by
                    rw [upperNamed]
                    exact tests (origin,.nominal name children.length) (by simp [schema])
                  have result := GeneralDictionaryDefaultNominalProjection215.nominal_bounded valid bounds.2 upper upperAt upperFound
                    (fun value seen => Or.inr (bounded.2 value seen).2) head index
                  simpa only [upperNamed,Nat.zero_add,Bounded,GeneralDictionaryDefaultNominalProjection215.Bounded] using result
              · intro anchor member; cases member
      · intro anchor member; cases member
 termination_by sizeOf query

 theorem many_bounds (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model) (queries : List Query) (bounds : List (Bounds state))
    (origins : Nat → Origin) (offset : Nat)
    (bounded : ∀ index : Fin bounds.length, Bounded state model bounds[index] (origins (offset+index.val)))
    (tests : ∀ test ∈ (schemas queries origins .actual offset).tests, Head model test.1 test.2) :
    Anchors state model (inspectMany state queries bounds (fun i => some (origins i)) offset) := by
  cases queries with
  | nil => cases bounds <;> intro anchor member <;> simp only [inspectMany,List.not_mem_nil] at member
  | cons query rest => cases bounds with
    | nil => intro anchor member; simp only [inspectMany,List.not_mem_nil] at member
    | cons head tail =>
      simp only [inspectMany]
      apply appended
      · apply inspect_bounds state model valid query head (origins offset)
        · simpa only [Fin.getElem_fin,List.getElem_cons_zero,Nat.add_zero] using bounded ⟨0,by simp⟩
        · intro test member
          apply tests test
          simpa only [schemas,Schema.append] using List.mem_append_left (schemas rest origins .actual (offset+1)).tests member
      · apply many_bounds state model valid rest tail origins (offset+1)
        · intro index
          simpa only [Fin.getElem_fin,List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm 1] using
            bounded ⟨index.val+1,by simp⟩
        · intro test member
          apply tests test
          simpa only [schemas,Schema.append] using List.mem_append_right (schema query (origins offset) .actual).tests member
 termination_by sizeOf queries
end
end Yulang.GeneralDictionaryRecursiveBounds215
