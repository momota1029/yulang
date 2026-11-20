import Yulang.GeneralGeneratedDictionaryMinFuel299

namespace Yulang.GeneralGeneratedDictionaryHeight299
open CommonRoleOutermostResolver (All₂ Dictionary)
open GeneralGeneratedDictionaryRun299
open GeneralGeneratedDictionaryAcc299
open GeneralGeneratedDictionaryMinFuel299

mutual
def height : Dictionary → Nat
  | .node _ children => tall children + 1
termination_by d => sizeOf d

def tall : List Dictionary → Nat
  | [] => 0
  | d::ds => max (height d) (tall ds)
termination_by ds => sizeOf ds
end

theorem tall_bound {α : Type} {P : α → Dictionary → Prop}
    {xs : List α} {ds : List Dictionary} (h : All₂ P xs ds)
    (n : Nat) (bound : ∀ x d, P x d → height d ≤ n) : tall ds ≤ n := by
  induction h with
  | nil => simp [tall]
  | cons t _ ih =>
    simp only [tall]
    exact Nat.max_le.mpr ⟨bound _ _ t,ih⟩

theorem lower_children {α : Type} {P Q : α → Dictionary → Prop}
    {xs : List α} {ds : List Dictionary} (h : All₂ P xs ds)
    (n : Nat) (next : ∀ x d, P x d → height d ≤ n → Q x d)
    (bound : tall ds ≤ n) : All₂ Q xs ds := by
  induction h with
  | nil => exact .nil
  | cons here _ ih =>
    have hh := (Nat.max_le.mp (show max (height _) (tall _) ≤ n from by
      simpa only [tall] using bound))
    exact .cons (next _ _ here hh.1) (ih hh.2)

theorem lower_bound (read : Read) (n x : Nat) (d : Dictionary)
    (hit : run read n x = some d) : height d ≤ n := by
  induction n generalizing x d with
  | zero => cases hit
  | succ n ih =>
    obtain ⟨row,ds,_,all,rfl⟩ := (run_exact _ _ _ _).mp hit
    have h := tall_bound all n ih
    simpa only [height,Nat.succ_eq_add_one] using Nat.add_le_add_right h 1

theorem replay_height (read : Read) (n x : Nat) (d : Dictionary)
    (hit : run read n x = some d) (m : Nat) (enough : height d ≤ m) :
    run read m x = some d := by
  induction n generalizing m x d with
  | zero => cases hit
  | succ n ih =>
    obtain ⟨row,ds,here,all,rfl⟩ := (run_exact _ _ _ _).mp hit
    have ht : tall ds+1 ≤ m := by simpa only [height] using enough
    cases m with
    | zero => omega
    | succ m =>
      apply (run_exact _ _ _ _).mpr
      refine ⟨row,ds,here,?_,rfl⟩
      exact lower_children all m (fun i d yes leq => ih i d yes m leq) (by omega)

theorem height_threshold (read : Read) (n x : Nat) (d : Dictionary)
    (hit : run read n x = some d) (m : Nat) : run read m x = some d ↔ height d ≤ m :=
  ⟨lower_bound read m x d,replay_height read n x d hit m⟩

theorem earliest_is_height (read : Read) (cap x k : Nat)
    (hit : earliest read x cap = some k) (n : Nat) (d : Dictionary)
    (out : run read n x = some d) : k = height d := by
  obtain ⟨_,⟨e,ready⟩,small⟩ := earliest_some read x cap k hit
  have same : e = d := by
    have one := monotone_fuel read k (max k n) x e (Nat.le_max_left _ _) ready
    have two := monotone_fuel read n (max k n) x d (Nat.le_max_right _ _) out
    exact Option.some.inj (one.symm.trans two)
  subst e
  have leq := lower_bound read k x d ready
  have geq : k ≤ height d := by
    by_cases h : k ≤ height d
    · exact h
    · have no := small (height d) (by omega)
      have ok := replay_height read n x d out (height d) (Nat.le_refl _)
      rw [no] at ok
      cases ok
  omega

end Yulang.GeneralGeneratedDictionaryHeight299
