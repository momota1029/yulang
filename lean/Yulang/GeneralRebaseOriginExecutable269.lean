import Yulang.GeneralRebaseOriginQuotient269
import Yulang.GeneralRebasePartialFinite268

namespace Yulang.GeneralRebaseOriginExecutable269
open GeneralNominalRecursiveInspection (Origin)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Equal Cyclic)
open GeneralRebaseOriginCycles268 (Window Sound NonemptyCycle graph graph_sound)
open GeneralRebaseOriginQuotient269 (Forward short_closure nonempty_cycle_iff)
open GeneralRebasePartialBool268 (Answer Reflect both)
open GeneralRebasePartialFinite268 (any any_sound transfer)

def lookup (matchOrigin : Origin → Fin n → Answer) (o : Origin) : Option (Fin n) :=
 (List.finRange n).find? (fun i => matchOrigin o i == some true)

def located (matchOrigin : Origin → Fin n → Answer) (o : Origin) : Answer :=
 any (matchOrigin o) (List.finRange n)

theorem lookup_sound (w : Window n) (matchOrigin : Origin → Fin n → Answer)
 (validMatch : ∀ i, Reflect (Equal state o (w.point i)) (matchOrigin o i))
 (found : lookup matchOrigin o = some j) : Equal state o (w.point j) := by
 have hit : matchOrigin o j = some true := beq_iff_eq.mp (List.find?_some (p := fun i => matchOrigin o i == some true) found)
 simpa only [hit,Reflect] using validMatch j

theorem located_sound (w : Window n) (matchOrigin : Origin → Fin n → Answer)
 (validMatch : ∀ i, Reflect (Equal state o (w.point i)) (matchOrigin o i)) :
 Reflect (∃ j, Equal state o (w.point j)) (located matchOrigin o) :=
 transfer (by simp : (∃ j ∈ List.finRange n, Equal state o (w.point j)) ↔ ∃ j, Equal state o (w.point j))
   (any_sound _ _ _ (fun i _ => validMatch i))

/-- Entries need not globally cover all syntax. The optional negative
exhaustion cut covers the query only when an actual cycle would be present. -/
def graphQuery (w : Window n) (matchOrigin : Origin → Fin n → Answer)
 (forwardCover : Fin n → Bool) (rootCover : Origin → Bool) (o : Origin) : Answer :=
 match lookup matchOrigin o with
 | some j => graph w forwardCover j
 | none => if rootCover o && located matchOrigin o == some false then some false else none

theorem graphQuery_sound (w : Window n) (sound : Sound state w)
 (matchOrigin : Origin → Fin n → Answer) (forwardCover : Fin n → Bool) (rootCover : Origin → Bool)
 (validMatch : ∀ i, Reflect (Equal state o (w.point i)) (matchOrigin o i))
 (forward : ∀ j, forwardCover j = true → GeneralRebaseOriginCycles268.Closure state w j)
 (cover : rootCover o = true → NonemptyCycle state o → ∃ j, Equal state o (w.point j)) :
 Reflect (NonemptyCycle state o) (graphQuery w matchOrigin forwardCover rootCover o) := by
 unfold graphQuery
 split
 · rename_i j found
   exact transfer (nonempty_cycle_iff state (lookup_sound w matchOrigin validMatch found)).symm
     (graph_sound w sound forwardCover forward j)
 · split
   · rename_i enough
     have flags := (Bool.and_eq_true ..).mp enough
     have absent := located_sound w matchOrigin validMatch
     rw [beq_iff_eq.mp flags.2] at absent
     exact fun original => absent (cover flags.1 original)
   · trivial

def cyclic (w : Window n) (matchOrigin : Origin → Fin n → Answer)
 (forwardCover : Fin n → Bool) (rootCover : Origin → Bool) (o : Origin) : Answer :=
 both (graphQuery w matchOrigin forwardCover rootCover o) w.model

theorem cyclic_sound (w : Window n) (sound : Sound state w)
 (matchOrigin : Origin → Fin n → Answer) (forwardCover : Fin n → Bool) (rootCover : Origin → Bool)
 (validMatch : ∀ i, Reflect (Equal state o (w.point i)) (matchOrigin o i))
 (forward : ∀ j, forwardCover j = true → GeneralRebaseOriginCycles268.Closure state w j)
 (cover : rootCover o = true → NonemptyCycle state o → ∃ j, Equal state o (w.point j)) :
 Reflect (Cyclic state o) (cyclic w matchOrigin forwardCover rootCover o) :=
 GeneralRebasePartialBool268.both_sound (graphQuery_sound w sound matchOrigin forwardCover rootCover validMatch forward cover) sound.model

theorem with_semantic_closure (w : Window n) (sound : Sound state w)
 (matchOrigin : Origin → Fin n → Answer)
 (validMatch : ∀ i, Reflect (Equal state o (w.point i)) (matchOrigin o i))
 (closed : Forward state w.point) :
 Reflect (Cyclic state o) (cyclic w matchOrigin (fun _ => true) (fun _ => false) o) :=
 cyclic_sound w sound matchOrigin _ _ validMatch (fun i _ => short_closure state w closed i)
   (fun invalid => Bool.noConfusion invalid)

end Yulang.GeneralRebaseOriginExecutable269
