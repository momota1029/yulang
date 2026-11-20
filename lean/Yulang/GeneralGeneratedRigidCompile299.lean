import Yulang.GeneralGeneratedRigidNested299

namespace Yulang.GeneralGeneratedRigidCompile299
open Roles Roles.Examples
open GeneralGeneratedDictionaryRun299
open GeneralGeneratedRigidNested299 (decode table eraseKeys)

def keys (encode : Goal → Option Nat) : List Goal → Option (List Nat)
  | [] => some []
  | first::rest => do
      let n ← encode first
      let ns ← keys encode rest
      return n::ns

def fromGoals (visible : List Impl) (source : Nat → Option Goal)
    (encode : Goal → Option Nat) : Read := fun i => do
  let goal ← source i
  match candidates visible goal with
  | [chosen] =>
    let goals := chosen.constraints.map (fun g => g.subst (matchingSubst chosen.head goal.args))
    let children ← keys encode goals
    return ⟨chosen.key,children⟩
  | _ => none

theorem keys_exact (encode : Goal → Option Nat) (source : Nat → Option Goal)
    (roundtrip : ∀ g i, encode g = some i → source i = some g)
    (goals : List Goal) (indices : List Nat) (eq : keys encode goals = some indices) :
    indices.map source = goals.map some := by
  induction goals generalizing indices with
  | nil =>
    have he : indices = [] := (Option.some.inj eq).symm
    subst indices
    rfl
  | cons g gs ih =>
    cases a : encode g with
    | none => simp [keys,a] at eq
    | some i =>
      cases b : keys encode gs with
      | none => simp [keys,a,b] at eq
      | some is =>
        have he : i::is = indices := by simpa [keys,a,b] using eq
        subst indices
        simp only [List.map_cons,roundtrip _ _ a,ih _ b]

theorem row_exact (visible : List Impl) (source : Nat → Option Goal)
    (encode : Goal → Option Nat) (roundtrip : ∀ g i, encode g = some i → source i = some g)
    (i : Nat) (e : Entry) (read : fromGoals visible source encode i = some e) :
    ∃ goal chosen, source i = some goal ∧ candidates visible goal = [chosen] ∧
      chosen.key = e.key ∧ e.children.map source =
        (chosen.constraints.map (fun g => g.subst (matchingSubst chosen.head goal.args))).map some := by
  cases h : source i with
  | none => simp [fromGoals,h] at read
  | some goal =>
    cases ys : candidates visible goal with
    | nil => simp [fromGoals,h,ys] at read
    | cons chosen rest =>
      cases rest with
      | cons another tail => simp [fromGoals,h,ys] at read
      | nil =>
        cases k : keys encode (chosen.constraints.map (fun g =>
          g.subst (matchingSubst chosen.head goal.args))) with
        | none => simp [fromGoals,h,ys,k] at read
        | some children =>
          have he : (⟨chosen.key,children⟩ : Entry) = e := by simpa [fromGoals,h,ys,k] using read
          subst e
          exact ⟨goal,chosen,rfl,ys,rfl,keys_exact encode source roundtrip _ _ k⟩

def source (i : Nat) : Option Goal := if i < 3 then some (decode i) else none

def encode (g : Goal) : Option Nat :=
  if g = decode 0 then some 0
  else if g = decode 1 then some 1
  else if g = decode 2 then some 2
  else none

theorem roundtrip (g : Goal) (i : Nat) (seen : encode g = some i) :
    source i = some g := by
  unfold encode at seen
  split at seen
  · rename_i h
    cases Option.some.inj seen
    subst g
    rfl
  · split at seen
    · rename_i h
      cases Option.some.inj seen
      subst g
      rfl
    · split at seen
      · rename_i h
        cases Option.some.inj seen
        subst g
        rfl
      · cases seen

theorem computed_table : fromGoals goodImpls source encode = table := by
  funext i
  cases i with
  | zero => decide +kernel
  | succ i =>
    cases i with
    | zero => decide +kernel
    | succ i =>
      cases i with
      | zero => decide +kernel
      | succ i => rfl

def incomplete (g : Goal) : Option Nat :=
  if g = decode 2 then none else encode g

theorem missing_grandchild : fromGoals goodImpls source incomplete 1 = none := by
  decide +kernel

theorem unfinished_is_no_result : run (fromGoals goodImpls source incomplete) 3 0 = none := by
  rfl

theorem matches_elaboration :
    ∃ plan, RoleDictionaries.elaborate goodImpls goodImpls_wellFormed (decode 0) = .resolved plan ∧
      run (fromGoals goodImpls source encode) 3 0 = some (eraseKeys plan) := by
  rw [computed_table]
  exact GeneralGeneratedRigidNested299.full_nested

end Yulang.GeneralGeneratedRigidCompile299
