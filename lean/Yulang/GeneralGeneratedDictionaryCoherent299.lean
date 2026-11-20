import Yulang.GeneralGeneratedDictionaryScope299

namespace Yulang.GeneralGeneratedDictionaryCoherent299
open CommonRoleOutermostResolver (All₂ Dictionary Frontier)
open B4Target (Vocabulary)
open B4TargetV8
variable {v : Vocabulary} {b : SourceBoundary v} {r : v.Registry} {s : v.State}

mutual
theorem selected_unique (a c : Dictionary) (d : v.Demand)
    (one : Classify b r s d (.selected a))
    (two : Classify b r s d (.selected c)) : a = c := by
  cases a with
  | node left da =>
    cases c with
    | node right dc =>
      cases one with
      | selected locA allA =>
        cases two with
        | selected locC allC =>
          have eq := Frontier.selected.inj (local_functional locA locC)
          obtain ⟨rfl,rfl⟩ := eq
          exact congrArg (Dictionary.node left) (ordered_unique da dc _ allA allC)
termination_by sizeOf a

theorem ordered_unique (a c : List Dictionary) (ds : List v.Demand)
    (one : All₂ (fun d dict => Classify b r s d (.selected dict)) ds a)
    (two : All₂ (fun d dict => Classify b r s d (.selected dict)) ds c) : a = c := by
  cases one with
  | nil => cases two; rfl
  | cons ha ta =>
    cases two with
    | cons hc tc =>
      rw [selected_unique _ _ _ ha hc,ordered_unique _ _ _ ta tc]
termination_by sizeOf a
end

open GeneralGeneratedDictionaryRun299
open GeneralGeneratedDictionaryScope299

theorem cross_table (first second : Read) (decode₁ decode₂ : Nat → v.Demand)
    (check₁ : Faithful (b:=b) (r:=r) (s:=s) first decode₁)
    (check₂ : Faithful (b:=b) (r:=r) (s:=s) second decode₂)
    (n m i j : Nat) (a c : Dictionary) (same : decode₁ i = decode₂ j)
    (one : run first n i = some a) (two : run second m j = some c) : a = c := by
  exact selected_unique a c _ (classifies _ _ check₁ _ _ _ one)
    (same.symm ▸ classifies _ _ check₂ _ _ _ two)

end Yulang.GeneralGeneratedDictionaryCoherent299
