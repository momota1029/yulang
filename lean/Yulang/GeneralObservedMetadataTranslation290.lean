import Yulang.GeneralObservedMetadataLocal290

/-! The finite metadata agreement controls the original translator, not a
reimplementation. The bound includes potentially deferred paths. -/
set_option maxHeartbeats 12000000
namespace Yulang.GeneralObservedMetadataTranslation290
open GeneralDeclarationPatterns (Constructors Pattern)
open GeneralNominalInspection (Interpretation translate)
open GeneralObservedMetadataKeys290 (keys keysMany member_many app_self app_nested)
open GeneralObservedMetadataEntry290 (LocalEqual)

theorem translate_eq (c : Constructors) (i : Interpretation) (d : Constructors) (j : Interpretation)
    (p : Pattern) (localEq : LocalEqual (keys p) c i d j) : translate c i p = translate d j p := by
  cases p with
  | var _ => simp [translate]
  | join _ _ => simp [translate]
  | variant label p =>
    have same := translate_eq c i d j p localEq
    simp only [translate,same]
  | record label payload tail =>
    have p := translate_eq c i d j payload
      (localEq.restrict (fun k h => List.mem_append_left (keys tail) h))
    have t := translate_eq c i d j tail
      (localEq.restrict (fun k h => List.mem_append_right (keys payload) h))
    simp only [translate,p,t]
  | app key args =>
    obtain ⟨cat,prim,nom⟩ := localEq key (app_self key args)
    have recEq (a : Pattern) (member : a ∈ args) : translate c i a = translate d j a :=
      translate_eq c i d j a (localEq.restrict (fun _ h => app_nested member h))
    unfold translate
    rw [cat,prim,nom]
    split
    all_goals try rfl
    · rename_i first last hp
      rw [recEq first (by simp),recEq last (by simp)]
    · rename_i actuals no
      split
      · rename_i spec eq
        split
        · congr 1
          exact List.map_congr_left (fun a _ => recEq a.val a.property)
        · rfl
      · rfl
termination_by sizeOf p
decreasing_by
 all_goals simp_all
 all_goals first | omega | have h := List.sizeOf_lt_of_mem member; omega

end Yulang.GeneralObservedMetadataTranslation290
