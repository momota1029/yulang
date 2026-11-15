import Yulang.GeneralDictionaryWeakReport215
import Yulang.GeneralDictionaryRecursiveBounds215
import Yulang.GeneralDictionaryDefaultNominalFallback215
import Yulang.GeneralNominalInspectionTransport188

/-! Forgetting explicit root centers preserves projection semantics. Nominal
fallback origins are compared with the actual center via invariant nominal
subtyping; structural missing origins are recursively propagated. -/
namespace Yulang.GeneralDictionaryRawProjection215
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalInspection (Query Bounds)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryStructuralProjection215 (Bounded)
open GeneralNominalOriginTerms (Head)
open GeneralNominalFiniteBracket (reindex)
open GeneralDictionaryWeakReport215
open GeneralNominalOriginAlias181 GeneralNominalStructuralOrigin188
set_option backward.isDefEq.respectTransparency false

theorem nominal_origins (same : GeneralNominalOriginTerms.Same model actual fallback) (name index : Nat) :
    GeneralNominalReportTransport188.Optional model (some (.nominal fallback name index))
      (some (.nominal actual name index)) := by
  have transport := nominal_congr model fallback actual (similar_symm (same_similar same)) name index
  exact .some ⟨fun value seen => ⟨value,(transport value).mp seen,CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩,
    fun value seen => ⟨value,(transport value).mpr seen,CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩⟩

mutual
 theorem inspect_related (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model) (query : Query) (bounds : Bounds state) (origin : Origin)
    (bounded : Bounded state model bounds origin)
    (tests : ∀ test ∈ (schema query origin .actual).tests, Head model test.1 test.2) :
    Related model (inspect state query bounds none) (inspect state query bounds (some origin)) := by
  cases query with
  | variables names =>
      simp only [inspect]
      refine ⟨?_,?_,?_⟩
      · intro capture member
        obtain ⟨name,present,rfl⟩ := List.mem_map.mp member
        exact ⟨⟨name,bounds,some origin⟩,List.mem_map.mpr ⟨name,present,rfl⟩,rfl,rfl,.none _⟩
      · intro anchor member; cases member
      · intro test member; cases member
  | deferred reason => simp only [inspect]; exact related_refl _ _
  | scalar base =>
      simp only [inspect]
      exact related_visit _ _ _ _ (related_refl _ _) (.none _)
  | node shape children =>
      simp only [inspect]
      apply related_visit _ _ _ _ _ (.none _)
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
          apply many_related state model valid children _ (fun i => .structural origin shape i) 0 _ childTests
          intro index
          have length : ((List.ofFn lower).zip (List.ofFn upper)).length = shape.arity := by
            simp only [List.length_zip,List.length_ofFn,matching.1,matching.2,Nat.min_self]
          let position : Fin shape.arity := ⟨index.val,by rw [← length]; exact index.isLt⟩
          have result := GeneralDictionaryStructuralProjection215.structural_child state model valid bounds
            lowerKind upperKind lower upper lowerAt upperAt matching.1 matching.2 bounded head position
          simpa only [Fin.getElem_fin,List.getElem_zip,List.getElem_ofFn,reindex,position,Nat.zero_add] using result
        · exact related_refl _ _
      · exact related_refl _ _
      · exact related_refl _ _
  | nominal name children =>
      simp only [inspect]
      apply related_visit _ _ _ _ _ (.none _)
      split
      · exact related_refl _ _
      · rename_i lower lowerAt
        split
        · rename_i named
          split
          · exact related_refl _ _
          · rename_i intervals found
            have head := tests (origin,.nominal name children.length) (by simp [schema])
            have lowerSame := GeneralDictionaryDefaultNominalFallback215.parent_same valid bounds.1 lower lowerAt
              (fun value seen => Or.inl (bounded.2 value seen).1) head
            have left : Related model (inspectMany state children intervals
                (fun i => some (.nominal (.source (state.base.source bounds.1)) name i)) 0)
                (inspectMany state children intervals (fun i => some (.nominal origin name i)) 0) :=
              from_strong (GeneralNominalInspectionTransport188.many_related state children intervals _ _ 0
                (fun index => nominal_origins lowerSame name index))
            simp only [Option.getD_none,Option.getD_some]
            split
            · exact left
            · split
              · exact related_refl _ _
              · rename_i upper upperAt
                split
                · split
                  · exact related_refl _ _
                  · rename_i targets upperFound
                    have upperSame := GeneralDictionaryDefaultNominalFallback215.parent_same valid bounds.2 upper upperAt
                      (fun value seen => Or.inr (bounded.2 value seen).2) head
                    exact related_append left (from_strong
                      (GeneralNominalInspectionTransport188.many_related state children targets _ _ 0
                        (fun index => nominal_origins upperSame name index)))
                · exact related_refl _ _
        · exact related_refl _ _
 termination_by sizeOf query

 theorem many_related (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model) (queries : List Query) (bounds : List (Bounds state))
    (origins : Nat → Origin) (offset : Nat)
    (bounded : ∀ index : Fin bounds.length, Bounded state model bounds[index] (origins (offset+index.val)))
    (tests : ∀ test ∈ (schemas queries origins .actual offset).tests, Head model test.1 test.2) :
    Related model (inspectMany state queries bounds (fun _ => none) offset)
      (inspectMany state queries bounds (fun i => some (origins i)) offset) := by
  cases queries with
  | nil => cases bounds <;> simp only [inspectMany] <;> exact related_refl _ _
  | cons query rest => cases bounds with
    | nil => simp only [inspectMany]; exact related_refl _ _
    | cons head tail =>
      simp only [inspectMany]
      apply related_append
      · apply inspect_related state model valid query head (origins offset)
        · simpa only [Fin.getElem_fin,List.getElem_cons_zero,Nat.add_zero] using bounded ⟨0,by simp⟩
        · intro test member
          apply tests test
          simpa only [schemas,Schema.append] using List.mem_append_left (schemas rest origins .actual (offset+1)).tests member
      · apply many_related state model valid rest tail origins (offset+1)
        · intro index
          simpa only [Fin.getElem_fin,List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm 1] using
            bounded ⟨index.val+1,by simp⟩
        · intro test member
          apply tests test
          simpa only [schemas,Schema.append] using List.mem_append_right (schema query (origins offset) .actual).tests member
 termination_by sizeOf queries
end

end Yulang.GeneralDictionaryRawProjection215
