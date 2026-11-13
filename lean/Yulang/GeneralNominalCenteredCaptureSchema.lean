import Yulang.GeneralNominalCenteredInspection
import Yulang.GeneralNominalRelationalMatching

/-! Captures produced from explicit origins retain their corresponding
actual-mode schema uses, including both sides of nominal intervals. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalCenteredCaptureSchema
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query Bounds)
open GeneralNominalMaterialization (schema schemas Schema Use)

mutual
  theorem inspect_capture (state : GeneralNominalState.State) (query : Query)
      (bounds : Bounds state) (origin : Origin) (captured : Capture state)
      (member : captured ∈ (inspect state query bounds (some origin)).captures) :
      ∃ actual, captured.origin = some actual ∧
        (⟨captured.name,actual,.actual⟩ : Use) ∈ (schema query origin .actual).variables := by
    cases query with
    | variables names =>
      simp only [inspect,schema] at member ⊢
      obtain ⟨name,found,equal⟩ := List.mem_map.mp member
      cases equal
      exact ⟨origin,rfl,List.mem_map.mpr ⟨name,found,rfl⟩⟩
    | deferred => simp only [inspect,block,List.not_mem_nil] at member
    | scalar base =>
      simp only [inspect,Report.visit] at member
      split at member
      · cases member
      · split at member
        · split at member <;> cases member
        · cases member
        · cases member
    | node shape children =>
      simp only [schema]
      simp only [inspect,Report.visit] at member
      split at member
      · split at member
        · exact many_capture state children _ (fun i => .structural origin shape i) 0 captured member
        · cases member
      · cases member
      · cases member
    | nominal name children =>
      simp only [schema]
      simp only [inspect,Report.visit] at member
      split at member
      · split at member <;> cases member
      · split at member
        · split at member
          · cases member
          · split at member
            · exact many_capture state children _ (fun i => .nominal origin name i) 0 captured member
            · split at member
              · cases member
              · split at member
                · split at member
                  · cases member
                  · rcases List.mem_append.mp member with left | right
                    · exact many_capture state children _ (fun i => .nominal origin name i) 0 captured left
                    · exact many_capture state children _ (fun i => .nominal origin name i) 0 captured right
                · cases member
        · cases member
    termination_by sizeOf query

  theorem many_capture (state : GeneralNominalState.State) (queries : List Query)
      (bounds : List (Bounds state)) (origins : Nat → Origin) (offset : Nat) (captured : Capture state)
      (member : captured ∈ (inspectMany state queries bounds (fun i => some (origins i)) offset).captures) :
      ∃ actual, captured.origin = some actual ∧
        (⟨captured.name,actual,.actual⟩ : Use) ∈ (schemas queries origins .actual offset).variables := by
    cases queries with
    | nil => cases bounds <;> simp only [inspectMany,List.not_mem_nil] at member
    | cons query rest =>
      cases bounds with
      | nil => simp only [inspectMany,List.not_mem_nil] at member
      | cons head tail =>
        simp only [inspectMany,Report.append,schemas,Schema.append] at member ⊢
        rcases List.mem_append.mp member with first | last
        · obtain ⟨actual,recorded,found⟩ := inspect_capture state query head (origins offset) captured first
          exact ⟨actual,recorded,List.mem_append_left _ found⟩
        · obtain ⟨actual,recorded,found⟩ := many_capture state rest tail origins (offset+1) captured last
          exact ⟨actual,recorded,List.mem_append_right _ found⟩
    termination_by sizeOf queries
end

end Yulang.GeneralNominalCenteredCaptureSchema
