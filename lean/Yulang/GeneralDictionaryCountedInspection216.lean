import Yulang.GeneralDictionaryCountedObservation216
import Yulang.GeneralNominalInspectionAlignment
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCountedInspection216
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalInspection (Query Bounds)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalOriginTerms GeneralNominalReadbackFunctionality
open GeneralDictionaryStructuralProjection215 (Bounded)
open GeneralDictionaryCountedObservation216 (Labelled)
open GeneralNominalInspectionAlignment
open GeneralNominalFiniteBracket (reindex)

mutual
 theorem inspect_tests (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model) (query : Query) (bounds : Bounds state) (origin : Origin)
    (known : Labelled constructors interpretation model origin)
    (bounded : Bounded state model bounds origin)
    (finished : Finished (inspect state query bounds (some origin))) :
    ∀ test ∈ (schema query origin .actual).tests, Head model test.1 test.2 := by
  cases query with
  | variables names => intro test member; simp [schema] at member
  | deferred reason => simp only [inspect,Finished,block] at finished; cases finished.1
  | scalar base =>
    have head : Head model origin (.scalar base) := by
      simp only [inspect,finished_visit] at finished
      split at finished
      · simp only [Finished] at finished; cases finished.2.1
      · split at finished
        · rename_i actual recorded
          split at finished
          · rename_i same
            cases same
            exact GeneralDictionaryCountedObservation216.scalar valid known bounded recorded
          · simp only [Finished] at finished; cases finished.2.1
        · simp only [Finished] at finished; cases finished.2.1
        · simp only [Finished,block] at finished; cases finished.1
    intro test member
    simp only [schema,List.mem_singleton] at member
    cases member
    exact head
  | node shape children =>
    simp only [inspect,finished_visit] at finished
    split at finished
    · rename_i lowerKind lows upperKind ups lowerAt upperAt
      split at finished
      · rename_i matching
        have canonical : shape.Canonical := matching.1 ▸ state.view.canonical lowerKind
        have head := GeneralDictionaryCountedObservation216.structural valid known bounded lowerAt upperAt matching.1 matching.2 canonical
        have length := finished_length state children _ _ 0 finished
        have slotsLength : ((List.ofFn lows).zip (List.ofFn ups)).length = shape.arity := by
          simp only [List.length_zip,List.length_ofFn,matching.1,matching.2,Nat.min_self]
        have descendants := many_tests state model valid children _ (fun i => .structural origin shape i) 0
          (fun index => by
            have i : index.val < shape.arity := by rw [← slotsLength]; exact index.isLt
            simpa only [project,Nat.zero_add] using GeneralDictionaryCountedObservation216.labelled_project known head canonical ⟨index.val,i⟩)
          (fun index => by
            let position : Fin shape.arity := ⟨index.val,by rw [← slotsLength]; exact index.isLt⟩
            have result := GeneralDictionaryStructuralProjection215.structural_child state model valid bounds
              lowerKind upperKind lows ups lowerAt upperAt matching.1 matching.2 bounded head position
            simpa only [Fin.getElem_fin,List.getElem_zip,List.getElem_ofFn,reindex,position,Nat.zero_add] using result)
          finished
        intro test member
        simp only [schema,List.mem_cons] at member
        rcases member with rfl | member
        · exact head
        · exact descendants test member
      · simp only [Finished,block] at finished; cases finished.1
    · simp only [Finished] at finished; cases finished.2.1
    · simp only [Finished,block] at finished; cases finished.1
  | nominal name children =>
    obtain ⟨descriptor,intervals,recorded,same,found,complete,_⟩ :=
      nominal_left state children bounds (some origin) finished
    simp only [Option.getD_some] at complete
    have length := finished_length state children intervals _ 0 complete
    have argLength : descriptor.arguments.length = children.length := by
      rw [GeneralNominalInspectionFiniteValues.type_arguments _ found,List.length_map]
      exact length.symm
    have head : Head model origin (.nominal name children.length) := by
      rw [← same]
      exact GeneralDictionaryCountedObservation216.nominal valid known bounded recorded argLength
    have descendants := many_tests state model valid children intervals (fun i => .nominal origin name i) 0
      (fun index => by
        have i : index.val < children.length := by rw [length]; exact index.isLt
        simpa only [project,Nat.zero_add] using GeneralDictionaryCountedObservation216.labelled_project known head trivial ⟨index.val,i⟩)
      (fun index => by
        have head' : Head model origin (.nominal descriptor.declaration.name children.length) := same ▸ head
        have result := GeneralDictionaryDefaultNominalProjection215.nominal_bounded valid bounds.1 descriptor recorded found
          (fun value seen => Or.inl (bounded.2 value seen).1) head' index
        simpa only [same,Nat.zero_add,Bounded,GeneralDictionaryDefaultNominalProjection215.Bounded] using result)
      complete
    intro test member
    simp only [schema,List.mem_cons] at member
    rcases member with rfl | member
    · exact head
    · exact descendants test member
 termination_by sizeOf query

 theorem many_tests (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model) (queries : List Query) (bounds : List (Bounds state))
    (origins : Nat → Origin) (offset : Nat)
    (known : ∀ index : Fin bounds.length, Labelled constructors interpretation model (origins (offset+index.val)))
    (bounded : ∀ index : Fin bounds.length, Bounded state model bounds[index] (origins (offset+index.val)))
    (finished : Finished (inspectMany state queries bounds (fun i => some (origins i)) offset)) :
    ∀ test ∈ (schemas queries origins .actual offset).tests, Head model test.1 test.2 := by
  cases queries with
  | nil => intro test member; simp [schemas] at member
  | cons query rest => cases bounds with
    | nil => simp only [inspectMany,Finished] at finished; cases finished.2.2
    | cons first tail =>
      simp only [inspectMany,finished_append] at finished
      intro test member
      simp only [schemas,Schema.append,List.mem_append] at member
      rcases member with member | member
      · exact inspect_tests state model valid query first (origins offset)
          (by simpa only [Nat.add_zero] using known ⟨0,by simp⟩)
          (by simpa only [Fin.getElem_fin,List.getElem_cons_zero,Nat.add_zero] using bounded ⟨0,by simp⟩)
          finished.1 test member
      · exact many_tests state model valid rest tail origins (offset+1)
          (fun index => by
            simpa only [Nat.add_assoc,Nat.add_comm 1] using known ⟨index.val+1,by simp⟩)
          (fun index => by
            simpa only [Fin.getElem_fin,List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm 1] using bounded ⟨index.val+1,by simp⟩)
          finished.2 test member
 termination_by sizeOf queries
end
end Yulang.GeneralDictionaryCountedInspection216
