import Yulang.GeneralNominalCenteredCaptureSchema
import Yulang.GeneralNominalInspectionAlignment

/-! Finished actual schemas have capture witnesses at the identical origin.
No branch-model, representability or covered-pattern premise is added. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalSchemaCapture187
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalInspection (Query Bounds)
open GeneralNominalInspectionAlignment

mutual
 theorem schema_capture (state : GeneralNominalState.State) (query : Query)
    (bounds : Bounds state) (origin : Origin)
    (finished : Finished (inspect state query bounds (some origin)))
    (entry : Use) (member : entry ∈ (schema query origin .actual).variables) :
    ∃ captured ∈ (inspect state query bounds (some origin)).captures,
      captured.name = entry.name ∧ captured.origin = some entry.origin := by
  cases query with
  | variables names =>
    simp only [schema] at member
    simp only [inspect]
    obtain ⟨name,present,rfl⟩ := List.mem_map.mp member
    exact ⟨⟨name,bounds,some origin⟩,List.mem_map.mpr ⟨name,present,rfl⟩,rfl,rfl⟩
  | deferred reason => simp [schema] at member
  | scalar value => simp [schema] at member
  | node shape children =>
    simp only [schema] at member
    simp only [inspect,finished_visit] at finished
    split at finished
    · rename_i lower childrenBounds upper targets low high
      split at finished
      · rename_i same
        obtain ⟨captured,present,name,ref⟩ := schemas_capture state children _
          (fun i => .structural origin shape i) 0 finished entry member
        refine ⟨captured,?_,name,ref⟩
        simpa only [inspect,low,high,same,and_self,ite_true,Report.visit,Option.map_some] using present
      · simp only [Finished,block] at finished; cases finished.1
    · simp only [Finished] at finished; cases finished.2.1
    · simp only [Finished,block] at finished; cases finished.1
  | nominal key children =>
    simp only [schema] at member
    obtain ⟨descriptor,intervals,recorded,same,found,complete,included⟩ :=
      nominal_left state children bounds (some origin) finished
    obtain ⟨captured,present,name,ref⟩ := schemas_capture state children intervals
      (fun i => .nominal origin key i) 0 complete entry member
    exact ⟨captured,included present,name,ref⟩
 termination_by sizeOf query

 theorem schemas_capture (state : GeneralNominalState.State) (queries : List Query)
    (bounds : List (Bounds state)) (origins : Nat → Origin) (offset : Nat)
    (finished : Finished (inspectMany state queries bounds (fun i => some (origins i)) offset))
    (entry : Use) (member : entry ∈ (schemas queries origins .actual offset).variables) :
    ∃ captured ∈ (inspectMany state queries bounds (fun i => some (origins i)) offset).captures,
      captured.name = entry.name ∧ captured.origin = some entry.origin := by
  cases queries with
  | nil => simp [schemas] at member
  | cons query rest =>
    cases bounds with
    | nil => simp only [inspectMany,Finished] at finished; cases finished.2.2
    | cons head tail =>
      simp only [inspectMany] at finished ⊢
      have parts := (finished_append ..).mp finished
      simp only [schemas,Schema.append] at member
      rcases List.mem_append.mp member with first | last
      · obtain ⟨captured,present,name,ref⟩ := schema_capture state query head (origins offset) parts.1 entry first
        exact ⟨captured,List.mem_append_left _ present,name,ref⟩
      · obtain ⟨captured,present,name,ref⟩ := schemas_capture state rest tail origins (offset+1) parts.2 entry last
        exact ⟨captured,List.mem_append_right _ present,name,ref⟩
 termination_by sizeOf queries
end

end Yulang.GeneralNominalSchemaCapture187
