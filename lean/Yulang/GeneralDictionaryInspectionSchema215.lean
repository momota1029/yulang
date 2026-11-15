import Yulang.GeneralNominalCenteredCaptureSchema
import Yulang.GeneralNominalCaptureAnchors

/-! Every test encountered by actual recursive inspection belongs to its
head schema. This direction needs no Finished or branch-model assumption. -/
namespace Yulang.GeneralDictionaryInspectionSchema215
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalInspection (Query Bounds)

mutual
 theorem inspect_tests (state : GeneralNominalState.State) (query : Query)
    (bounds : Bounds state) (origin : Origin) (test : Origin × Test)
    (member : test ∈ (inspect state query bounds (some origin)).tests) :
    test ∈ (schema query origin .actual).tests := by
  cases query with
  | variables names => simp [inspect] at member
  | deferred reason => simp [inspect,block] at member
  | scalar base =>
    simp only [inspect,Report.visit,Option.toList_some,List.map_cons,List.map_nil,
      List.singleton_append,List.mem_cons] at member
    rcases member with rfl | rest
    · simp [schema]
    · split at rest
      · cases rest
      · split at rest
        · split at rest <;> cases rest
        · cases rest
        · cases rest
  | node shape children =>
    simp only [schema]
    simp only [inspect,Report.visit,Option.toList_some,List.map_cons,List.map_nil,
      List.singleton_append,List.mem_cons] at member
    rcases member with rfl | rest
    · exact List.mem_cons_self
    · apply List.mem_cons_of_mem
      split at rest
      · split at rest
        · exact many_tests state children _ (fun i => .structural origin shape i) 0 test rest
        · cases rest
      · cases rest
      · cases rest
  | nominal name children =>
    simp only [schema]
    simp only [inspect,Report.visit,Option.toList_some,List.map_cons,List.map_nil,
      List.singleton_append,List.mem_cons] at member
    rcases member with rfl | rest
    · exact List.mem_cons_self
    · apply List.mem_cons_of_mem
      split at rest
      · split at rest <;> cases rest
      · split at rest
        · split at rest
          · cases rest
          · split at rest
            · exact many_tests state children _ (fun i => .nominal origin name i) 0 test rest
            · split at rest
              · cases rest
              · split at rest
                · split at rest
                  · cases rest
                  · rcases List.mem_append.mp rest with left | right
                    · exact many_tests state children _ (fun i => .nominal origin name i) 0 test left
                    · exact many_tests state children _ (fun i => .nominal origin name i) 0 test right
                · cases rest
        · cases rest
 termination_by sizeOf query

 theorem many_tests (state : GeneralNominalState.State) (queries : List Query)
    (bounds : List (Bounds state)) (origins : Nat → Origin) (offset : Nat) (test : Origin × Test)
    (member : test ∈ (inspectMany state queries bounds (fun i => some (origins i)) offset).tests) :
    test ∈ (schemas queries origins .actual offset).tests := by
  cases queries with
  | nil => cases bounds <;> simp only [inspectMany,List.not_mem_nil] at member
  | cons query rest => cases bounds with
    | nil => simp only [inspectMany,List.not_mem_nil] at member
    | cons head tail =>
      simp only [inspectMany,Report.append,schemas,Schema.append] at member ⊢
      rcases List.mem_append.mp member with first | last
      · exact List.mem_append_left _ (inspect_tests state query head (origins offset) test first)
      · exact List.mem_append_right _ (many_tests state rest tail origins (offset+1) test last)
 termination_by sizeOf queries
end
end Yulang.GeneralDictionaryInspectionSchema215
