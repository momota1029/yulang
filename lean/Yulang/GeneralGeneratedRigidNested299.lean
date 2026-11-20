import Yulang.GeneralGeneratedDictionaryRun299
import Yulang.RoleDictionaries

namespace Yulang.GeneralGeneratedRigidNested299
open Roles Roles.Examples
open RoleDictionaries (Plan elaborate)
open CommonRoleOutermostResolver (Dictionary)
open GeneralGeneratedDictionaryRun299

def decode : Nat → Goal
  | 0 => display (list (list int))
  | 1 => display (list int)
  | _ => display int

def table : Read
  | 0 => some ⟨listImpl.key,[1]⟩
  | 1 => some ⟨listImpl.key,[2]⟩
  | 2 => some ⟨intImpl.key,[]⟩
  | _ => none

def rank : Nat → Nat
  | 0 => 2
  | 1 => 1
  | _ => 0

def eraseKeys : Plan → Dictionary
  | .node chosen children => .node chosen.key (children.map eraseKeys)

def localImpl (i key : Nat) (children : List Nat) : Prop :=
  ∃ chosen, candidates goodImpls (decode i) = [chosen] ∧ chosen.key = key ∧
    (children.map decode) = chosen.constraints.map
      (fun goal => goal.subst (matchingSubst chosen.head (decode i).args))

theorem rows (i : Nat) (e : Entry) (hit : table i = some e) :
    (i = 0 ∧ e = ⟨listImpl.key,[1]⟩) ∨
    (i = 1 ∧ e = ⟨listImpl.key,[2]⟩) ∨
    (i = 2 ∧ e = ⟨intImpl.key,[]⟩) := by
  cases i with
  | zero => exact .inl ⟨rfl,(Option.some.inj hit).symm⟩
  | succ i =>
    cases i with
    | zero => exact .inr (.inl ⟨rfl,(Option.some.inj hit).symm⟩)
    | succ i =>
      cases i with
      | zero => exact .inr (.inr ⟨rfl,(Option.some.inj hit).symm⟩)
      | succ i => cases hit

theorem faithful (i : Nat) (e : Entry) (hit : table i = some e) :
    localImpl i e.key e.children := by
  rcases rows i e hit with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨listImpl,by decide +kernel,rfl,rfl⟩
  · exact ⟨listImpl,by decide +kernel,rfl,rfl⟩
  · exact ⟨intImpl,by decide +kernel,rfl,rfl⟩

theorem ranked : Ranked table rank := by
  intro i e hit child member
  rcases rows i e hit with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases List.mem_singleton.mp member; decide
  · cases List.mem_singleton.mp member; decide
  · cases member

theorem closed : Closed table := by
  intro i e hit child member
  rcases rows i e hit with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases List.mem_singleton.mp member; exact ⟨_,rfl⟩
  · cases List.mem_singleton.mp member; exact ⟨_,rfl⟩
  · cases member

theorem full_nested :
    ∃ plan, elaborate goodImpls goodImpls_wellFormed (decode 0) = .resolved plan ∧
      run table 3 0 = some (eraseKeys plan) := by
  exact ⟨.node listImpl [.node listImpl [.node intImpl []]],
    RoleDictionaries.Examples.all_nested_children_use_caller_scope,by simp [eraseKeys]; rfl⟩

theorem computed_nested :
    run table 3 0 = some (.node listImpl.key [.node listImpl.key [.node intImpl.key []]]) := rfl

theorem short_budget : run table 2 0 = none := rfl

end Yulang.GeneralGeneratedRigidNested299
