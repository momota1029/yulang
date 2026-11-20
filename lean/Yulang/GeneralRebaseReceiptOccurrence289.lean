import Yulang.GeneralRebaseReceiptIdentityCollision289

/-! Finite occurrence encoding is injective at a fixed role environment.
It records ordered endpoints and ordered named outputs, not merely IDs. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseReceiptOccurrence289
open GeneralSourceDictionaries (Occurrence)
open GeneralSourceState (Output)

structure Key where
  identity : Nat
  role : Nat
  arguments : List (Nat × Nat)
  outputs : List (Nat × Nat)
  deriving Repr, DecidableEq

def packOutput (o : Output) : Nat × Nat := (o.name,o.target)
def unpackOutput (o : Nat × Nat) : Output := ⟨o.1,o.2⟩

def encode (o : Occurrence roles) : Key :=
  ⟨o.identity,o.demand.role,List.ofFn o.demand.arguments,o.demand.outputs.map packOutput⟩

theorem output_round_trip (outputs : List Output) :
    (outputs.map packOutput).map unpackOutput = outputs := by
  induction outputs with
  | nil => rfl
  | cons first rest ih =>
    cases first
    simp only [List.map_cons,packOutput,unpackOutput,ih]

theorem injective {roles : Roles.RoleDecls} : Function.Injective (@encode roles) := by
  intro first last same
  rcases first with ⟨firstId,⟨firstRole,firstArgs,firstOut,firstOk⟩⟩
  rcases last with ⟨lastId,⟨lastRole,lastArgs,lastOut,lastOk⟩⟩
  have rolesEq : firstRole = lastRole := congrArg Key.role same
  subst lastRole
  have ids : firstId = lastId := congrArg Key.identity same
  subst lastId
  have arguments : List.ofFn firstArgs = List.ofFn lastArgs := congrArg Key.arguments same
  have sameArgs : firstArgs = lastArgs := by
    funext i
    have get := congrArg (fun l : List (Nat × Nat) => l[i.val]?) arguments
    simpa only [List.getElem?_ofFn,dite_eq_left i.isLt,Option.some.injEq,Fin.eta] using get
  subst lastArgs
  have outs : firstOut.map packOutput = lastOut.map packOutput := congrArg Key.outputs same
  have retain := congrArg (List.map unpackOutput) outs
  rw [output_round_trip,output_round_trip] at retain
  subst lastOut
  rfl

theorem code_eq_iff {first last : Occurrence roles} : encode first = encode last ↔ first = last :=
  ⟨fun h => injective h,congrArg encode⟩

end Yulang.GeneralRebaseReceiptOccurrence289
