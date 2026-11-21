import Yulang.GeneralOrderedDictionaryFault309

namespace Yulang.GeneralOrderedDictionaryFootprint309
open CommonRoleOutermostResolver (Dictionary)
open GeneralGeneratedDictionaryRun299 (Read run Entry)
open GeneralOrderedDictionaryCheck309 (Error validate ordered)

def need (read : Read) : Nat → Nat → List Nat
  | 0,_ => []
  | n+1,i => i :: match read i with
    | none => []
    | some row => row.children.flatMap (need read n)

def AgreeOn (xs : List Nat) (a b : Read) : Prop := ∀ i ∈ xs, a i = b i

theorem ordered_congr (a b : Nat → Dictionary → Except Error Unit) (parent ordinal : Nat)
    (xs : List Nat) (ds : List Dictionary)
    (agree : ∀ i ∈ xs, ∀ d, a i d = b i d) :
    ordered a parent ordinal xs ds = ordered b parent ordinal xs ds := by
  induction xs generalizing ds ordinal with
  | nil => cases ds <;> rfl
  | cons x xs ih =>
    cases ds with
    | nil => rfl
    | cons d ds =>
      unfold ordered
      rw [agree x List.mem_cons_self d]
      cases b x d with
      | error => rfl
      | ok => exact ih (ordinal+1) ds (fun i hi => agree i (List.mem_cons_of_mem _ hi))

theorem validate_agrees (a b : Read) (fuel i : Nat) (agree : AgreeOn (need a fuel i) a b)
    (d : Dictionary) : validate a fuel i d = validate b fuel i d := by
  induction fuel generalizing i d with
  | zero => rfl
  | succ n ih =>
    have here : a i = b i := agree i List.mem_cons_self
    cases d with
    | node key ds =>
      unfold validate
      rw [← here]
      cases hit : a i with
      | none => rfl
      | some r =>
        have split : ordered (validate a n) i 0 r.children ds =
            ordered (validate b n) i 0 r.children ds := by
          apply ordered_congr
          intro child appears data
          apply ih
          intro node used
          apply agree node
          change node ∈ i :: (match a i with | none => [] | some e => e.children.flatMap (need a n))
          rw [hit]
          exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨child,appears,used⟩)
        simpa only using (show (if key ≠ r.key then Except.error (.wrongKey i r.key key) else
          if ds.length ≠ r.children.length then Except.error (.wrongArity i r.children.length ds.length) else
            ordered (validate a n) i 0 r.children ds) = _ from by rw [split])

theorem run_agrees (a b : Read) (fuel i : Nat) (agree : AgreeOn (need a fuel i) a b) :
    run a fuel i = run b fuel i := by
  cases ha : run a fuel i with
  | none =>
    cases hb : run b fuel i with
    | none => rfl
    | some d =>
      have accepted := (GeneralOrderedDictionaryCheck309.exact ..).mpr hb
      rw [← validate_agrees a b fuel i agree d] at accepted
      have contradiction := (GeneralOrderedDictionaryCheck309.exact ..).mp accepted
      rw [ha] at contradiction
      cases contradiction
  | some d =>
    have accepted := (GeneralOrderedDictionaryCheck309.exact ..).mpr ha
    rw [validate_agrees a b fuel i agree d] at accepted
    exact ((GeneralOrderedDictionaryCheck309.exact ..).mp accepted).symm

end Yulang.GeneralOrderedDictionaryFootprint309
