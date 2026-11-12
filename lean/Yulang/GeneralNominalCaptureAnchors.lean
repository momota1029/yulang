import Yulang.GeneralNominalCapturedChildOrigins

/-! Every retained actual capture origin has its observation anchor in the
recursive inspection report. The invariant is derived from inspection, not
requested from a caller. Captures without an actual origin remain explicit. -/
namespace Yulang.GeneralNominalCaptureAnchors

open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Bounds Query)

def Anchored (result : Report state) : Prop :=
  ∀ capture ∈ result.captures, ∀ origin, capture.origin = some origin → (origin,capture.bounds) ∈ result.anchors

private theorem empty (state : GeneralNominalState.State) : Anchored ({} : Report state) := by
  intro capture member; cases member

private theorem blocked (state : GeneralNominalState.State) (bounds : Bounds state) : Anchored (block bounds) := by
  intro capture member; cases member

private theorem conflict (state : GeneralNominalState.State) (bounds : Bounds state) :
    Anchored ({conflicts := [bounds]} : Report state) := by intro capture member; cases member

private theorem arity (state : GeneralNominalState.State) (first last : Nat) :
    Anchored ({arity := [(first,last)]} : Report state) := by intro capture member; cases member

private theorem appended (one : Anchored (first : Report state)) (two : Anchored (last : Report state)) :
    Anchored (first.append last) := by
  intro capture member origin recorded
  rcases List.mem_append.mp member with a | b
  · exact List.mem_append_left _ (one capture a origin recorded)
  · exact List.mem_append_right _ (two capture b origin recorded)

private theorem visited (bounds : Bounds state) (origin : Option Origin) (test : Test)
    (result : Report state) (valid : Anchored result) : Anchored (Report.visit bounds origin test result) := by
  intro capture member source recorded
  exact List.mem_append_right _ (valid capture member source recorded)

mutual
  theorem inspect_anchored (state : GeneralNominalState.State) (query : Query)
      (bounds : Bounds state) (origin : Option Origin) : Anchored (inspect state query bounds origin) := by
    cases query with
    | variables names =>
        simp only [inspect]
        intro capture member source recorded
        obtain ⟨name,_,same⟩ := List.mem_map.mp member
        subst capture
        change origin = some source at recorded
        simp [recorded]
    | deferred => simpa only [inspect] using blocked state bounds
    | scalar expected =>
        simp only [inspect]
        apply visited
        split
        · exact conflict state bounds
        · split
          · split <;> first | exact empty state | exact conflict state bounds
          · exact conflict state bounds
          · exact blocked state bounds
    | node expected patterns =>
        simp only [inspect]
        apply visited
        split
        · split
          · exact many_anchored state patterns _ _ _
          · exact blocked state bounds
        · exact conflict state bounds
        · exact blocked state bounds
    | nominal expected patterns =>
        simp only [inspect]
        apply visited
        split
        · split
          · exact conflict state bounds
          · exact conflict state bounds
          · exact blocked state bounds
        · split
          · split
            · exact blocked state bounds
            · split
              · exact many_anchored state patterns _ _ _
              · split
                · exact blocked state bounds
                · split
                  · split
                    · exact blocked state bounds
                    · exact appended (many_anchored state patterns _ _ _) (many_anchored state patterns _ _ _)
                  · exact conflict state bounds
          · exact conflict state bounds
  termination_by sizeOf query

  theorem many_anchored (state : GeneralNominalState.State) (queries : List Query)
      (bounds : List (Bounds state)) (origins : Nat → Option Origin) (index : Nat) :
      Anchored (inspectMany state queries bounds origins index) := by
    cases queries with
    | nil => cases bounds <;> simp only [inspectMany] <;> first | exact empty state | exact arity state _ _
    | cons query queries =>
      cases bounds with
      | nil => simpa only [inspectMany,List.length_nil] using arity state (query :: queries).length 0
      | cons interval intervals =>
          simp only [inspectMany]
          exact appended (inspect_anchored state query interval (origins index))
            (many_anchored state queries intervals origins (index+1))
  termination_by sizeOf queries
end

theorem report_anchored (context : GeneralNominalCandidates.Context) (declaration : GeneralDeclarations.Declaration)
    (bounds : List (Bounds context.state)) :
    Anchored (GeneralNominalRecursiveCandidates.report context declaration bounds) :=
  many_anchored context.state _ bounds _ 0

end Yulang.GeneralNominalCaptureAnchors
