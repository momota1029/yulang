import Yulang.GeneralNominalCanonicalPaths

/-! Every capture in the complete recursive inspector, when started from a
retained actual origin, follows canonical constructor argument positions.
Both nominal endpoint reports retain the same path from that actual input. -/
namespace Yulang.GeneralNominalReportPaths
open GeneralNominalRecursiveInspection GeneralNominalCanonicalPaths
open GeneralNominalInspection (Query Bounds)

def Rooted (report : Report state) (root : Origin) : Prop :=
  ∀ capture ∈ report.captures, ∃ origin, capture.origin = some origin ∧ Path root origin

theorem rooted_trans (path : Path root middle) (rooted : Rooted report middle) : Rooted report root := by
  intro capture member
  obtain ⟨origin,same,followed⟩ := rooted capture member
  exact ⟨origin,same,GeneralNominalCanonicalPaths.trans path followed⟩

private theorem append_rooted (first : Rooted (one : Report state) root) (last : Rooted two root) :
    Rooted (one.append two) root := by
  intro capture member
  rcases List.mem_append.mp member with one | two
  · exact first capture one
  · exact last capture two

mutual
  theorem inspect_rooted (state : GeneralNominalState.State) (query : Query)
      (bounds : Bounds state) (origin : Origin) : Rooted (inspect state query bounds (some origin)) origin := by
    cases query with
    | variables names =>
      intro capture member
      simp only [inspect] at member
      obtain ⟨name,_,rfl⟩ := List.mem_map.mp member
      exact ⟨origin,rfl,.root⟩
    | deferred => simp [Rooted,inspect,block]
    | scalar base =>
      simp only [inspect,Report.visit]
      split
      · intro capture member; cases member
      · split
        · split <;> (intro capture member; cases member)
        · intro capture member; cases member
        · intro capture member; cases member
    | node shape children =>
      simp only [inspect,Report.visit]
      split
      · rename_i lower xs upper ys _ _
        split
        · rename_i matched
          apply many_rooted
          intro index
          refine ⟨.structural origin shape index,rfl,.structural ?_ .root⟩
          rw [← matched.1]
          exact state.view.canonical lower
        · intro capture member; cases member
      · intro capture member; cases member
      · intro capture member; cases member
    | nominal name children =>
      simp only [inspect,Report.visit]
      have origins (fallback : Origin) : ∀ index, ∃ ref,
          some (.nominal ((some origin).getD fallback) name index) = some ref ∧ Path origin ref := by
        intro index
        exact ⟨.nominal origin name index,rfl,.nominal .root⟩
      split
      · split <;> (intro capture member; cases member)
      · split
        · split
          · intro capture member; cases member
          · split
            · exact many_rooted state children _ _ 0 (origins _)
            · split
              · intro capture member; cases member
              · split
                · split
                  · intro capture member; cases member
                  · exact append_rooted (many_rooted state children _ _ 0 (origins _))
                      (many_rooted state children _ _ 0 (origins _))
                · intro capture member; cases member
        · intro capture member; cases member
    termination_by sizeOf query

  theorem many_rooted (state : GeneralNominalState.State) (queries : List Query)
      (bounds : List (Bounds state)) (origins : Nat → Option Origin) (offset : Nat)
      (known : ∀ index, ∃ origin, origins index = some origin ∧ Path root origin) :
      Rooted (inspectMany state queries bounds origins offset) root := by
    cases queries with
    | nil => cases bounds <;> simp [Rooted,inspectMany]
    | cons query rest =>
      cases bounds with
      | nil => simp [Rooted,inspectMany]
      | cons head tail =>
        simp only [inspectMany]
        apply append_rooted
        · obtain ⟨origin,recorded,path⟩ := known offset
          rw [recorded]
          exact rooted_trans path (inspect_rooted state query head origin)
        · exact many_rooted state rest tail origins (offset+1) known
    termination_by sizeOf queries
end

theorem capture_closed (state : GeneralNominalState.State) (query : Query) (bounds : Bounds state)
    {capture : Capture state} {model : GeneralNominalCommonBridge.Assignment}
    (root : Origin) (closed : GeneralNominalGroundAccessibility.ClosedTerm context pattern term)
    (known : GeneralNominalFiniteMeaning.At model .actual root
      (GeneralNominalFiniteMeaning.denote (fun _ => .bottom) term))
    (member : capture ∈ (inspect state query bounds (some root)).captures)
    (recorded : capture.origin = some origin) (observed : Observes model origin actual) :
    ∃ source part, GeneralNominalSourcePatternParts.Part (GeneralDeclarationPatterns.normalize pattern) source ∧
      GeneralNominalGroundAccessibility.ClosedTerm context source part ∧
      GeneralNominalFiniteMeaning.At model .actual origin
        (GeneralNominalFiniteMeaning.denote (fun _ => .bottom) part) ∧
      GeneralNominalPatersonLineage.mass [source] ≤ GeneralNominalPatersonLineage.mass [pattern] := by
  obtain ⟨endpoint,same,path⟩ := inspect_rooted state query bounds root capture member
  have identical : endpoint = origin := Option.some.inj (same.symm.trans recorded)
  subst endpoint
  exact GeneralNominalCanonicalPaths.closed_pattern path closed known observed

end Yulang.GeneralNominalReportPaths
