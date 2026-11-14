import Yulang.GeneralNominalCaptureNames
import Yulang.GeneralNominalInspectionAlignment

/-! A finished concrete inspection captures every variable name in its query.
This is independent of any assignment, branch model, capture usability or
caller-supplied coverage witness. It does not identify a new candidate's origin
with a historical origin. -/
namespace Yulang.GeneralNominalCaptureCoverage183
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query Bounds)
open GeneralNominalCaptureNames (names manyNames)
open GeneralNominalInspectionAlignment

mutual
  theorem inspect_covers (state : GeneralNominalState.State) (query : Query)
      (bounds : Bounds state) (origin : Option Origin)
      (finished : Finished (inspect state query bounds origin))
      (name : Nat) (member : name ∈ names query) :
      ∃ captured ∈ (inspect state query bounds origin).captures, captured.name = name := by
    cases query with
    | variables binders =>
      simp only [inspect]
      exact ⟨⟨name,bounds,origin⟩,List.mem_map.mpr ⟨name,member,rfl⟩,rfl⟩
    | scalar => cases member
    | deferred => cases member
    | node shape children =>
      simp only [names] at member
      simp only [inspect,finished_visit] at finished
      split at finished
      · rename_i lower slots upper targets low high
        split at finished
        · rename_i same
          obtain ⟨captured,present,equal⟩ := many_covers state children _ _ 0 finished name member
          refine ⟨captured,?_,equal⟩
          simpa only [inspect,low,high,same,and_self,ite_true,Report.visit] using present
        · simp only [Finished,block] at finished
          cases finished.1
      · simp only [Finished] at finished
        cases finished.2.1
      · simp only [Finished,block] at finished
        cases finished.1
    | nominal key children =>
      obtain ⟨descriptor,intervals,recorded,same,found,complete,included⟩ :=
        GeneralNominalInspectionAlignment.nominal_left state children bounds origin finished
      obtain ⟨captured,present,equal⟩ := many_covers state children intervals _ 0 complete name member
      exact ⟨captured,included present,equal⟩
  termination_by sizeOf query

  theorem many_covers (state : GeneralNominalState.State) (queries : List Query)
      (bounds : List (Bounds state)) (origins : Nat → Option Origin) (offset : Nat)
      (finished : Finished (inspectMany state queries bounds origins offset))
      (name : Nat) (member : name ∈ manyNames queries) :
      ∃ captured ∈ (inspectMany state queries bounds origins offset).captures, captured.name = name := by
    cases queries with
    | nil => cases member
    | cons query rest =>
      cases bounds with
      | nil =>
        simp only [inspectMany,Finished] at finished
        cases finished.2.2
      | cons head tail =>
        simp only [inspectMany] at finished ⊢
        have parts := (finished_append ..).mp finished
        rcases List.mem_append.mp member with first | last
        · obtain ⟨captured,present,equal⟩ := inspect_covers state query head (origins offset) parts.1 name first
          exact ⟨captured,List.mem_append_left _ present,equal⟩
        · obtain ⟨captured,present,equal⟩ := many_covers state rest tail origins (offset+1) parts.2 name last
          exact ⟨captured,List.mem_append_right _ present,equal⟩
  termination_by sizeOf queries
end

theorem inspect_name_iff (state : GeneralNominalState.State) (query : Query)
    (bounds : Bounds state) (origin : Option Origin)
    (finished : Finished (inspect state query bounds origin)) (name : Nat) :
    (∃ captured ∈ (inspect state query bounds origin).captures, captured.name = name) ↔
      name ∈ names query := by
  constructor
  · rintro ⟨captured,member,equal⟩
    exact equal ▸ GeneralNominalCaptureNames.inspect_named state query bounds origin captured member
  · exact inspect_covers state query bounds origin finished name

theorem many_name_iff (state : GeneralNominalState.State) (queries : List Query)
    (bounds : List (Bounds state)) (origins : Nat → Option Origin) (offset : Nat)
    (finished : Finished (inspectMany state queries bounds origins offset)) (name : Nat) :
    (∃ captured ∈ (inspectMany state queries bounds origins offset).captures, captured.name = name) ↔
      name ∈ manyNames queries := by
  constructor
  · rintro ⟨captured,member,equal⟩
    exact equal ▸ GeneralNominalCaptureNames.many_named state queries bounds origins offset captured member
  · exact many_covers state queries bounds origins offset finished name

end Yulang.GeneralNominalCaptureCoverage183
