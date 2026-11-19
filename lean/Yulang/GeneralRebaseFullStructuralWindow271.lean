import Yulang.GeneralRebaseStructuralCompare271
import Yulang.GeneralRebaseMixedOriginWindow270

namespace Yulang.GeneralRebaseFullStructuralWindow271
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Equal Edge)
open GeneralNominalRecursiveInspection (Origin)
open GeneralRebaseNominalOrigin269 (Raw origin tag)
open GeneralRebaseStructuralOrigin270 (Slots shape scalar_no_edge)
open GeneralRebasePartialBool268 (Answer Reflect)
open GeneralRebasePartialFinite268 (any any_sound transfer)
open GeneralRebaseVersionedK2Probe268 (indexed indexed_sound)
open GeneralRebaseOriginCycles268 (Window Sound)
open GeneralRebaseRecordEdge271 (structural_edge_iff)
open GeneralRebaseMixedOriginWindow270 (nominalPart nominalPart_sound sourceEq sourceEq_sound)
open GeneralRebaseActualArguments269 (TypeSlots)
open GeneralRebaseOriginCongruence269 (equal_symm equal_trans)

def edge (state : State roles) (fallback : Origin → Origin → Answer) (a b : Slots state) : Answer :=
 match (Raw state).nominals a with
 | some d => any (nominalPart state fallback a b d) (TypeSlots d)
 | none =>
   match (Raw state).view.heads a with
   | .scalar _ => some false
   | .structural _ children => indexed (fun i => sourceEq state fallback (children i) b)
   | .deferred _ => none

theorem edge_sound (state : State roles) (fallback : Origin → Origin → Answer)
 (cert : ∀ a b, Reflect (Equal state a b) (fallback a b)) (a b : Slots state)
 (inhabited : ∃ m, Models state m) :
 Reflect (Edge state (origin state a) (origin state b)) (edge state fallback a b) := by
 unfold edge
 split
 · rename_i d recorded
   apply transfer (GeneralRebaseTypedNominalWindow269.edge_iff state a (origin state b) d recorded inhabited).symm
   exact any_sound _ _ _ (fun i _ => nominalPart_sound state fallback a b d i recorded (cert _ _))
 · split
   · rename_i base known
     exact scalar_no_edge state a base known inhabited (origin state b)
   · rename_i kind children known
     exact transfer (structural_edge_iff state a kind children known inhabited _).symm
         (indexed_sound _ _ (fun i => sourceEq_sound state fallback (children i) b (cert _ _)))
   · trivial

def covered (state : State roles) (point : Fin n → Slots state) (a : Fin n) : Bool :=
 match (Raw state).nominals (point a) with
 | some d => (TypeSlots d).all (GeneralRebaseNominalWindow269.target state point d)
 | none =>
   match (Raw state).view.heads (point a) with
   | .scalar _ => true
   | .structural kind children =>
     (List.finRange (shape state kind).arity).all (fun i => (List.finRange n).any (fun j => point j == children i))
   | .deferred _ => false

def check (state : State roles) (point : Fin n → Slots state) : Bool :=
 (List.finRange n).all (covered state point)

theorem forward (state : State roles) (point : Fin n → Slots state)
 (closed : check state point = true) (inhabited : ∃ m, Models state m) :
 GeneralRebaseOriginQuotient269.Forward state (origin state ∘ point) := by
 intro a dest advance
 have loc := List.all_eq_true.mp closed a (List.mem_finRange _)
 unfold covered at loc
 split at loc
 · rename_i d recorded
   obtain ⟨i,onList,equal⟩ := (GeneralRebaseTypedNominalWindow269.edge_iff state (point a) dest d recorded inhabited).mp advance
   obtain ⟨b,seen⟩ := GeneralRebaseNominalWindow269.target_sound state point a d recorded i
     (List.all_eq_true.mp loc i onList)
   exact ⟨b,equal_trans (equal_symm equal) seen⟩
 · split at loc
   · rename_i base recorded
     exact False.elim (scalar_no_edge state (point a) base recorded inhabited dest advance)
   · rename_i kind children recorded
     obtain ⟨i,equal⟩ := (structural_edge_iff state (point a) kind children recorded inhabited dest).mp advance
     obtain ⟨j,_,same⟩ := List.any_eq_true.mp (List.all_eq_true.mp loc i (List.mem_finRange _))
     refine ⟨j,?_⟩
     change Equal state dest (origin state (point j))
     rw [beq_iff_eq.mp same]
     exact equal_symm equal
   · cases loc

def window (state : State roles) (point : Fin n → Slots state)
 (fallback : Origin → Origin → Answer) : Window n :=
 ⟨origin state ∘ point,fun a b => edge state fallback (point a) (point b),some true⟩

theorem certified (state : State roles) (point : Fin n → Slots state) (fallback : Origin → Origin → Answer)
 (cert : ∀ a b, Reflect (Equal state a b) (fallback a b))
 (closed : check state point = true) (model : ∃ m, Models state m) :
 Sound state (window state point fallback) ∧
 GeneralRebaseOriginQuotient269.Forward state (window state point fallback).point :=
 ⟨⟨fun a b => edge_sound state fallback cert (point a) (point b) model,model⟩,forward state point closed model⟩

end Yulang.GeneralRebaseFullStructuralWindow271
