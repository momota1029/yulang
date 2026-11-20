import Yulang.GeneralSourceMetadataDiagnosticFixture291

/-! A missing or extra declaration code at an out-of-domain key witnesses
unequal exported tables without probing arbitrary functions. -/
namespace Yulang.GeneralSourceMetadataFresh291
open GeneralSourceMetadataRows291

theorem below_max (xs : List Nat) (key : Nat) (seen : key ∈ xs) : key ≤ xs.foldr max 0 := by
  induction xs with
  | nil => cases seen
  | cons a rest ih =>
    rcases List.mem_cons.mp seen with rfl | tail
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih tail) (Nat.le_max_right _ _)

def freshKey (s t : Source) : Nat :=
  ((s.rows.map Row.key ++ t.rows.map Row.key).foldr max 0) + 1

theorem fresh_absent (s t : Source) :
    freshKey s t ∉ (s.rows.map Row.key ++ t.rows.map Row.key) := by
  intro duplicate
  have bounded := below_max _ _ duplicate
  unfold freshKey at bounded
  omega

theorem left_defaults (s t : Source) :
    constructors s (freshKey s t) = s.fallback.decode (freshKey s t) :=
  outside_constructor _ _ (fun h => fresh_absent s t (List.mem_append_left _ h))

theorem right_defaults (s t : Source) :
    constructors t (freshKey s t) = t.fallback.decode (freshKey s t) :=
  outside_constructor _ _ (fun h => fresh_absent s t (List.mem_append_right _ h))

theorem code_injective (a b : DefaultCode) (key : Nat) (same : a.decode key = b.decode key) : a = b := by
  cases a <;> cases b <;> first | rfl | cases same

theorem different_table_at_fresh (s t : Source) (different : s.fallback ≠ t.fallback) :
    constructors s (freshKey s t) ≠ constructors t (freshKey s t) := by
  intro conflict
  rw [left_defaults s t,right_defaults s t] at conflict
  exact different (code_injective _ _ _ conflict)

theorem equal_table_implies_same_code (s t : Source) (same : constructors s = constructors t) :
    s.fallback = t.fallback := by
  have value := congrFun same (freshKey s t)
  rw [left_defaults s t,right_defaults s t] at value
  exact code_injective _ _ _ value

end Yulang.GeneralSourceMetadataFresh291
