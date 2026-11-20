import Yulang.GeneralRebasePriorWitness297

namespace Yulang.GeneralRebaseSignedIndex297
open GeneralNominalCenters (Plan)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseSignedModels297 (Sign Test)
open GeneralRebaseSourceQuestions297 (Question Checked questions holds signed)
open GeneralRebaseFiniteWitnessTable297 (Covers hit)

structure Reply where
  pass : Bool
  reject : Bool
 deriving DecidableEq, Repr

def Reply.at (row : Reply) : Sign → Bool
 | .pass => row.pass
 | .reject => row.reject

def emit (xs : List Assignment) (prior : Assignment → Bool)
    (candidate : Plan roles → Assignment → Bool) (p : Plan roles) : Reply :=
  ⟨hit xs (signed prior candidate) (p,.pass),hit xs (signed prior candidate) (p,.reject)⟩

def compile (plans : List (Plan roles)) (xs : List Assignment) (prior : Assignment → Bool)
    (candidate : Plan roles → Assignment → Bool) : List Reply :=
  plans.map (emit xs prior candidate)

def lookup (plans : List (Plan roles)) (xs : List Assignment) (prior : Assignment → Bool)
    (candidate : Plan roles → Assignment → Bool) (index : Nat) (sign : Sign) : Option Bool :=
  ((compile plans xs prior candidate)[index]?).map (·.at sign)

theorem length_exact (plans : List (Plan roles)) (xs : List Assignment) (prior : Assignment → Bool)
    (candidate : Plan roles → Assignment → Bool) :
    (compile plans xs prior candidate).length = plans.length := by simp [compile]

theorem lookup_exact (plans : List (Plan roles)) (xs : List Assignment) (prior : Assignment → Bool)
    (candidate : Plan roles → Assignment → Bool) (index : Nat) (sign : Sign) :
    lookup plans xs prior candidate index sign =
      (plans[index]?).map (fun p => hit xs (signed prior candidate) (p,sign)) := by
  unfold lookup compile
  rw [List.getElem?_map]
  cases plans[index]? <;> cases sign <;> rfl

theorem missing_index (plans : List (Plan roles)) (xs : List Assignment) (prior : Assignment → Bool)
    (candidate : Plan roles → Assignment → Bool) (index : Nat) (sign : Sign) :
    lookup plans xs prior candidate index sign = none ↔ plans.length ≤ index := by
  rw [lookup_exact]
  cases h : plans[index]? with
  | none =>
    exact ⟨fun _ => List.getElem?_eq_none_iff.mp h,fun _ => rfl⟩
  | some p =>
    constructor
    · intro h; cases h
    · intro oob
      have no := List.getElem?_eq_none_iff.mpr oob
      rw [no] at h
      cases h

theorem same_plan_same_answer (plans : List (Plan roles)) (xs : List Assignment) (prior : Assignment → Bool)
    (candidate : Plan roles → Assignment → Bool) {i j : Nat}
    (same : plans[i]? = plans[j]?) (sign : Sign) :
    lookup plans xs prior candidate i sign = lookup plans xs prior candidate j sign := by
  rw [lookup_exact,lookup_exact,same]

theorem true_exact {s : State roles} {plans : List (Plan roles)} {xs : List Assignment}
    {prior : Assignment → Bool} {candidate : Plan roles → Assignment → Bool}
    (cover : Covers (holds s) (questions plans) xs) (cert : Checked s plans xs prior candidate)
    (i : Nat) (p : Plan roles) (found : plans[i]? = some p) (sign : Sign) :
    lookup plans xs prior candidate i sign = some true ↔ ∃ a, Test s p sign a := by
  have listed : p ∈ plans := List.mem_of_getElem? found
  rw [lookup_exact,found,Option.map_some,Option.some.injEq]
  exact GeneralRebaseSourceQuestions297.exact cover cert p listed sign

theorem false_exact {s : State roles} {plans : List (Plan roles)} {xs : List Assignment}
    {prior : Assignment → Bool} {candidate : Plan roles → Assignment → Bool}
    (cover : Covers (holds s) (questions plans) xs) (cert : Checked s plans xs prior candidate)
    (i : Nat) (p : Plan roles) (found : plans[i]? = some p) (sign : Sign) :
    lookup plans xs prior candidate i sign = some false ↔ ¬ ∃ a, Test s p sign a := by
  have listed : p ∈ plans := List.mem_of_getElem? found
  rw [lookup_exact,found,Option.map_some,Option.some.injEq]
  exact Bool.eq_false_iff.trans (not_congr (GeneralRebaseSourceQuestions297.exact cover cert p listed sign))

end Yulang.GeneralRebaseSignedIndex297
