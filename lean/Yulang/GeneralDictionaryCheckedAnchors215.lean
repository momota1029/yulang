import Yulang.GeneralNominalCaptureAnchors

/-! Every checked interval in centered inspection has an inhabited observation
anchor. This is structural inspection provenance, not a feasibility assumption. -/
namespace Yulang.GeneralDictionaryCheckedAnchors215
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Bounds Query)

def Anchored (result : Report state) : Prop :=
  ∀ bounds ∈ result.checked, ∃ origin, (origin,bounds) ∈ result.anchors

private theorem empty (state : GeneralNominalState.State) : Anchored ({} : Report state) := by
  intro bounds member; cases member
private theorem blocked (state : GeneralNominalState.State) (bounds : Bounds state) : Anchored (block bounds) := by
  intro pair member; cases member
private theorem conflict (state : GeneralNominalState.State) (bounds : Bounds state) :
    Anchored ({conflicts := [bounds]} : Report state) := by intro pair member; cases member
private theorem arity (state : GeneralNominalState.State) (first last : Nat) :
    Anchored ({arity := [(first,last)]} : Report state) := by intro pair member; cases member
private theorem appended (one : Anchored (first : Report state)) (two : Anchored (last : Report state)) :
    Anchored (first.append last) := by
  intro bounds member
  rcases List.mem_append.mp member with a | b
  · obtain ⟨origin,present⟩ := one bounds a
    exact ⟨origin,List.mem_append_left _ present⟩
  · obtain ⟨origin,present⟩ := two bounds b
    exact ⟨origin,List.mem_append_right _ present⟩
private theorem visited (bounds : Bounds state) (origin : Origin) (test : Test)
    (result : Report state) (valid : Anchored result) : Anchored (Report.visit bounds (some origin) test result) := by
  intro pair member
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨origin,by simp [Report.visit]⟩
  · obtain ⟨source,present⟩ := valid pair member
    exact ⟨source,List.mem_append_right _ present⟩

mutual
  theorem inspect_anchored (state : GeneralNominalState.State) (query : Query)
      (bounds : Bounds state) (origin : Origin) : Anchored (inspect state query bounds (some origin)) := by
    cases query with
    | variables names =>
        intro pair member
        have same : pair = bounds := List.mem_singleton.mp (by simpa only [inspect] using member)
        subst pair
        exact ⟨origin,by simp [inspect]⟩
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
          · simpa only [Option.map_some,Option.getD_some] using many_anchored state patterns _ _ _
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
              · simpa only [Option.map_some,Option.getD_some] using many_anchored state patterns _ _ _
              · split
                · exact blocked state bounds
                · split
                  · split
                    · exact blocked state bounds
                    · simpa only [Option.map_some,Option.getD_some] using appended (many_anchored state patterns _ _ _) (many_anchored state patterns _ _ _)
                  · exact conflict state bounds
          · exact conflict state bounds
  termination_by sizeOf query

  theorem many_anchored (state : GeneralNominalState.State) (queries : List Query)
      (bounds : List (Bounds state)) (origins : Nat → Origin) (index : Nat) :
      Anchored (inspectMany state queries bounds (fun i => some (origins i)) index) := by
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

end Yulang.GeneralDictionaryCheckedAnchors215
