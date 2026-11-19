import Yulang.GeneralRebaseNominalWindow269

namespace Yulang.GeneralRebaseTypedNominalWindow269
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Equal Edge)
open GeneralNominalRecursiveInspection (Origin)
open GeneralNominalOriginTerms (arity project source_self)
open GeneralRebaseNominalOrigin269 (Raw origin tag head exhaust member_equal observed_is_type)
open GeneralNominalState (Descriptor)
open GeneralRebaseActualArguments269 (TypeSlots)
open GeneralRebasePartialFinite268 (any any_sound transfer)
open GeneralRebasePartialBool268 (Answer Reflect)
open GeneralRebaseOriginCycles268 (Window Sound)

theorem edge_iff (state : State roles) (s : Fin (Raw state).base.slots)
 (target : Origin) (d : Descriptor (Raw state).base.slots)
 (known : (Raw state).nominals s = some d) (model : ∃ m, Models state m) :
 Edge state (origin state s) target ↔
 ∃ idx ∈ TypeSlots d, Equal state (project (origin state s) (tag d) idx) target := by
 constructor
 · intro edge
   obtain ⟨_,test,idx,has,found⟩ := (GeneralRebaseOriginCongruence269.edge_normal state _ _).mp edge
   have positive : arity test ≠ 0 := fun zero => Nat.not_lt_zero idx.val (zero ▸ idx.isLt)
   cases exhaust state s d known model test has positive
   exact ⟨idx,observed_is_type state s d known idx model ⟨target,found⟩,found⟩
 · rintro ⟨idx,_,found⟩
   exact ⟨origin state s,tag d,idx,head state s d known,fun model _ => source_self model _,found⟩

def edge (state : State roles) (s : Fin (Raw state).base.slots)
 (target : Origin) (same : Origin → Origin → Answer) : Answer :=
 match (Raw state).nominals s with
 | none => none
 | some d => any (fun idx => same (project (origin state s) (tag d) idx) target) (TypeSlots d)

theorem edge_sound (state : State roles) (s : Fin (Raw state).base.slots) (target : Origin)
 (same : Origin → Origin → Answer) (cert : ∀ a b, Reflect (Equal state a b) (same a b))
 (model : ∃ m, Models state m) :
 Reflect (Edge state (origin state s) target) (edge state s target same) := by
 unfold edge
 split
 · trivial
 · rename_i descriptor known
   exact transfer (edge_iff state s target descriptor known model).symm
     (any_sound _ _ _ (fun _ _ => cert _ _))

def window (state : State roles) (points : Fin n → Fin (Raw state).base.slots)
 (same : Origin → Origin → Answer) : Window n :=
 ⟨origin state ∘ points,fun a b => edge state (points a) (origin state (points b)) same,some true⟩

theorem window_sound (state : State roles) (points : Fin n → Fin (Raw state).base.slots)
 (same : Origin → Origin → Answer) (cert : ∀ a b, Reflect (Equal state a b) (same a b))
 (model : ∃ m, Models state m) :
 Sound state (window state points same) :=
 ⟨fun a b => edge_sound state (points a) (origin state (points b)) same cert model,model⟩

theorem typed_forward (state : State roles) (points : Fin n → Fin (Raw state).base.slots)
 (same : Origin → Origin → Answer) (found : GeneralRebaseNominalWindow269.check state points = true)
 (model : ∃ m, Models state m) :
 GeneralRebaseOriginQuotient269.Forward state (window state points same).point :=
 GeneralRebaseOriginQuotient269.forward_of_tests state _ _ (GeneralRebaseNominalWindow269.check_sound state points found model)

end Yulang.GeneralRebaseTypedNominalWindow269
