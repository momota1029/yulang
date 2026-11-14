import Yulang.GeneralNominalReportTransport188

/-! The actual recursive inspector respects semantic origin transport without
pointness, shape restrictions or disjoint capture names. -/
namespace Yulang.GeneralNominalInspectionTransport188
open GeneralNominalRecursiveInspection GeneralNominalOriginAlias181
open GeneralNominalReportTransport188 GeneralNominalStructuralOrigin188
open GeneralNominalInspection (Bounds Query)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
variable {model : Assignment}

 theorem structural_optional (same : Optional model first last) (shape) (index) :
    Optional model (first.map fun parent => .structural parent shape index)
      (last.map fun parent => .structural parent shape index) := by
  cases same with
  | none => exact .none
  | some relation =>
    apply Optional.some
    have transport := structural_congr model _ _ relation shape index
    exact ⟨fun value seen => ⟨value,(transport value).mp seen,⟨subtype_refl _,subtype_refl _⟩⟩,
      fun value seen => ⟨value,(transport value).mpr seen,⟨subtype_refl _,subtype_refl _⟩⟩⟩

 theorem nominal_default (same : Optional model first last) (fallback : Origin) (name index : Nat) :
    Optional model (some (.nominal (first.getD fallback) name index))
      (some (.nominal (last.getD fallback) name index)) := by
  cases same with
  | none => exact .some (similar_refl _ _)
  | some relation =>
    apply Optional.some
    have transport := nominal_congr model _ _ relation name index
    exact ⟨fun value seen => ⟨value,(transport value).mp seen,⟨subtype_refl _,subtype_refl _⟩⟩,
      fun value seen => ⟨value,(transport value).mpr seen,⟨subtype_refl _,subtype_refl _⟩⟩⟩

mutual
 theorem inspect_related (state : GeneralNominalState.State) (query : Query) (bounds : Bounds state)
    (first last : Option Origin) (same : Optional model first last) :
    Related model (inspect state query bounds first) (inspect state query bounds last) := by
  cases query with
  | variables names =>
    refine ⟨?_,?_,by intro test member; simp [inspect] at member⟩
    · intro capture member
      simp only [inspect] at member
      obtain ⟨name,present,rfl⟩ := List.mem_map.mp member
      refine ⟨⟨name,bounds,last⟩,?_,rfl,rfl,same⟩
      simp only [inspect]
      exact List.mem_map.mpr ⟨name,present,rfl⟩
    · cases same with
      | none => intro anchor member; simp [inspect] at member
      | @some a b relation =>
        intro anchor member
        simp only [inspect,Option.toList_some,List.map_cons,List.map_nil,List.mem_singleton] at member
        subst anchor
        exact ⟨(b,bounds),by simp [inspect],rfl,relation⟩
  | deferred reason => simp only [inspect]; exact related_refl _ _
  | scalar base =>
    simp only [inspect]
    exact related_visit _ _ _ _ (related_refl _ _) same
  | node shape children =>
    simp only [inspect]
    apply related_visit _ _ _ _ _ same
    split
    · split
      · exact many_related state children _ _ _ 0 (fun index => structural_optional same shape index)
      · exact related_refl _ _
    · exact related_refl _ _
    · exact related_refl _ _
  | nominal name children =>
    simp only [inspect]
    apply related_visit _ _ _ _ _ same
    split
    · exact related_refl _ _
    · split
      · split
        · exact related_refl _ _
        · split
          · exact many_related state children _ _ _ 0 (fun index => nominal_default same _ name index)
          · split
            · exact related_refl _ _
            · split
              · split
                · exact related_refl _ _
                · apply related_append
                  · exact many_related state children _ _ _ 0 (fun index => nominal_default same _ name index)
                  · exact many_related state children _ _ _ 0 (fun index => nominal_default same _ name index)
              · exact related_refl _ _
      · exact related_refl _ _
 termination_by sizeOf query

 theorem many_related (state : GeneralNominalState.State) (queries : List Query) (bounds : List (Bounds state))
    (first last : Nat → Option Origin) (offset : Nat) (same : ∀ index, Optional model (first index) (last index)) :
    Related model (inspectMany state queries bounds first offset) (inspectMany state queries bounds last offset) := by
  cases queries with
  | nil => cases bounds <;> simp only [inspectMany] <;> exact related_refl _ _
  | cons query rest =>
    cases bounds with
    | nil => simp only [inspectMany]; exact related_refl _ _
    | cons head tail =>
      simp only [inspectMany]
      exact related_append (inspect_related state query head _ _ (same offset))
        (many_related state rest tail first last (offset+1) same)
 termination_by sizeOf queries
end

 theorem projection_transport (state : GeneralNominalState.State) (query : Query) (bounds : Bounds state)
    (first last : Option Origin) (same : Optional model first last)
    (valid : ProjectionModels state (inspect state query bounds last) model) :
    ProjectionModels state (inspect state query bounds first) model :=
  projection state _ _ (inspect_related state query bounds first last same) valid

end Yulang.GeneralNominalInspectionTransport188
