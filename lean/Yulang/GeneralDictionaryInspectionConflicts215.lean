import Yulang.GeneralDictionaryInspectionHeads215
import Yulang.GeneralNominalInspectionAlignment
import Yulang.GeneralDictionaryStructuralProjection215
import Yulang.GeneralDictionaryDefaultNominalProjection215
set_option backward.isDefEq.respectTransparency false

/-! Semantic head tests and bounded actual observations exclude every recursive inspection conflict.
Only current source Models, root interval containment and semantic schema tests
are used; no point-input or finite-center hypothesis is imposed. -/
namespace Yulang.GeneralDictionaryInspectionConflicts215
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalInspection (Query Bounds)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryStructuralProjection215 (Bounded)
open GeneralNominalOriginTerms (Head)
open GeneralNominalFiniteBracket (reindex)

open GeneralDictionaryInspectionHeads215
open GeneralNominalFiniteHeadInversion (head)

def Clear (report : Report state) : Prop := report.conflicts = []
theorem appended (one : Clear first) (two : Clear last) : Clear (first.append last) := by
  change first.conflicts ++ last.conflicts = []
  rw [one,two]
  rfl
theorem visited (rest : Clear report) : Clear (report.visit bounds origin test) := rest

mutual
 theorem inspect_clear (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model) (query : Query) (bounds : Bounds state) (origin : Origin)
    (bounded : Bounded state model bounds origin)
    (tests : ∀ test ∈ (schema query origin .actual).tests, Head model test.1 test.2) :
    Clear (inspect state query bounds (some origin)) := by
  cases query with
  | variables names => simp only [Clear,inspect]
  | deferred reason => simp only [Clear,inspect,block]
  | scalar base =>
    have tested := tests (origin,.scalar base) (by simp [schema])
    simp only [inspect]
    apply visited
    split
    · rename_i descriptor recorded
      have impossible := lower_tag bounded tested (nominal_slot valid recorded)
      cases impossible
    · split
      · rename_i actual recorded
        have same := lower_tag bounded tested (scalar_slot valid recorded)
        have equal := CommonNominalFullDemand.Head.base.inj same
        simp only [equal,ite_true,Clear]
      · rename_i kind children recorded
        have impossible := lower_tag bounded tested (structural_slot valid recorded)
        cases shapeEq : state.view.shapes kind <;> simp only [shapeEq,head] at impossible <;> cases impossible
      · rfl
  | node shape children =>
    simp only [inspect]
    apply visited
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
        apply many_clear state model valid children _ (fun i => .structural origin shape i) 0 _ childTests
        intro index
        have length : ((List.ofFn lower).zip (List.ofFn upper)).length = shape.arity := by
          simp only [List.length_zip,List.length_ofFn,matching.1,matching.2,Nat.min_self]
        let position : Fin shape.arity := ⟨index.val,by rw [← length]; exact index.isLt⟩
        have result := GeneralDictionaryStructuralProjection215.structural_child state model valid bounds
          lowerKind upperKind lower upper lowerAt upperAt matching.1 matching.2 bounded head position
        simpa only [Fin.getElem_fin,List.getElem_zip,List.getElem_ofFn,reindex,position,Nat.zero_add] using result
      · rfl
    · rename_i actual upper recorded other
      have impossible := lower_tag bounded (tests (origin,.structural shape) (by simp [schema])) (scalar_slot valid other)
      cases shape <;> cases impossible
    · rfl
  | nominal name children =>
    simp only [inspect]
    apply visited
    split
    · split
      · rename_i actual recorded
        have impossible := lower_tag bounded (tests (origin,.nominal name children.length) (by simp [schema])) (scalar_slot valid recorded)
        cases impossible
      · rename_i kind xs recorded
        have impossible := lower_tag bounded (tests (origin,.nominal name children.length) (by simp [schema])) (structural_slot valid recorded)
        cases shapeEq : state.view.shapes kind <;> simp only [shapeEq,head] at impossible <;> cases impossible
      · rfl
    · rename_i lower lowerAt
      split
      · rename_i named
        split
        · rfl
        · rename_i intervals found
          have childTests : ∀ test ∈ (schemas children (fun i => .nominal origin name i) .actual 0).tests,
              Head model test.1 test.2 := by
            intro test member
            apply tests test
            simpa only [schema] using List.mem_cons_of_mem (origin,.nominal name children.length) member
          have left : Clear (inspectMany state children intervals
              (fun i => some (.nominal origin name i)) 0) := by
            apply many_clear state model valid children intervals (fun i => .nominal origin name i) 0 _ childTests
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
            · rfl
            · rename_i upper upperAt
              split
              · rename_i upperNamed
                split
                · rfl
                · rename_i targets upperFound
                  apply appended left
                  apply many_clear state model valid children targets (fun i => .nominal origin name i) 0 _ childTests
                  intro index
                  have head : Head model origin (.nominal upper.declaration.name children.length) := by
                    rw [upperNamed]
                    exact tests (origin,.nominal name children.length) (by simp [schema])
                  have result := GeneralDictionaryDefaultNominalProjection215.nominal_bounded valid bounds.2 upper upperAt upperFound
                    (fun value seen => Or.inr (bounded.2 value seen).2) head index
                  simpa only [upperNamed,Nat.zero_add,Bounded,GeneralDictionaryDefaultNominalProjection215.Bounded] using result
              · rename_i different
                have equal := upper_tag bounded (tests (origin,.nominal name children.length) (by simp [schema])) (nominal_slot valid upperAt)
                exact False.elim (different (CommonNominalFullDemand.Head.nominal.inj equal).1.symm)
      · rename_i different
        have equal := lower_tag bounded (tests (origin,.nominal name children.length) (by simp [schema])) (nominal_slot valid lowerAt)
        exact False.elim (different (CommonNominalFullDemand.Head.nominal.inj equal).1)
 termination_by sizeOf query

 theorem many_clear (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model) (queries : List Query) (bounds : List (Bounds state))
    (origins : Nat → Origin) (offset : Nat)
    (bounded : ∀ index : Fin bounds.length, Bounded state model bounds[index] (origins (offset+index.val)))
    (tests : ∀ test ∈ (schemas queries origins .actual offset).tests, Head model test.1 test.2) :
    Clear (inspectMany state queries bounds (fun i => some (origins i)) offset) := by
  cases queries with
  | nil => cases bounds <;> simp only [Clear,inspectMany]
  | cons query rest => cases bounds with
    | nil => simp only [Clear,inspectMany]
    | cons head tail =>
      simp only [inspectMany]
      apply appended
      · apply inspect_clear state model valid query head (origins offset)
        · simpa only [Fin.getElem_fin,List.getElem_cons_zero,Nat.add_zero] using bounded ⟨0,by simp⟩
        · intro test member
          apply tests test
          simpa only [schemas,Schema.append] using List.mem_append_left (schemas rest origins .actual (offset+1)).tests member
      · apply many_clear state model valid rest tail origins (offset+1)
        · intro index
          simpa only [Fin.getElem_fin,List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm 1] using
            bounded ⟨index.val+1,by simp⟩
        · intro test member
          apply tests test
          simpa only [schemas,Schema.append] using List.mem_append_right (schema query (origins offset) .actual).tests member
 termination_by sizeOf queries
end
theorem many_clear_any_origins (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model) (queries : List Query) (bounds : List (Bounds state))
    (origins : Nat → Origin) (offset : Nat)
    (bounded : ∀ index : Fin bounds.length, Bounded state model bounds[index] (origins (offset+index.val)))
    (tests : ∀ test ∈ (schemas queries origins .actual offset).tests, Head model test.1 test.2)
    (actual : Nat → Option Origin) (start : Nat) :
    (inspectMany state queries bounds actual start).conflicts = [] := by
  have known := many_clear state model valid queries bounds origins offset bounded tests
  have status := GeneralNominalInspectionAlignment.many_status state queries bounds actual (fun i => some (origins i)) start offset
  have equal : (inspectMany state queries bounds actual start).conflicts =
      (inspectMany state queries bounds (fun i => some (origins i)) offset).conflicts :=
    congrArg (fun value => value.2.1) status
  exact equal.trans known

end Yulang.GeneralDictionaryInspectionConflicts215
