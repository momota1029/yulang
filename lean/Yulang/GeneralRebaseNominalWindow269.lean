import Yulang.GeneralRebaseNominalOrigin269
import Yulang.GeneralRebaseIntervalArgument269

namespace Yulang.GeneralRebaseNominalWindow269
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Equal Head)
open GeneralNominalRecursiveInspection (Test Origin)
open GeneralNominalOriginTerms (arity project)
open GeneralRebaseNominalOrigin269 (Raw origin tag head exhaust member_equal observed_is_type)
open GeneralNominalState (Descriptor)
open GeneralRebaseActualArguments269 (TypeSlots)
open GeneralRebaseSlotInequalities269 (prove prove_sound)
open GeneralRebaseOriginQuotient269 (TestsCover)
open GeneralRebasePartialBool268 (Answer Reflect)
open GeneralRebaseOriginCycles268 (Window Sound)

def tests (state : State roles) (point : Fin n → Fin (Raw state).base.slots) (a : Fin n) : List Test :=
 match (Raw state).nominals (point a) with
 | none => []
 | some d => [tag d]

def target (state : State roles) (point : Fin n → Fin (Raw state).base.slots)
 (d : Descriptor (Raw state).base.slots) (i : Fin d.arguments.length) : Bool :=
 match d.arguments[i.val] with
 | .row _ => false
 | .type (lo,hi) => (List.finRange n).any fun b =>
     prove (Raw state) (point b) lo && prove (Raw state) hi (point b)

def check (state : State roles) (point : Fin n → Fin (Raw state).base.slots) : Bool :=
 (List.finRange n).all fun a =>
   match (Raw state).nominals (point a) with
   | none => false
   | some d => (TypeSlots d).all (target state point d)

theorem target_sound (state : State roles) (point : Fin n → Fin (Raw state).base.slots)
 (a : Fin n) (d : Descriptor (Raw state).base.slots) (known : (Raw state).nominals (point a) = some d)
 (i : Fin d.arguments.length) (found : target state point d i = true) :
 ∃ b, Equal state (project (origin state (point a)) (tag d) i) (origin state (point b)) := by
 unfold target at found
 split at found
 · cases found
 · rename_i bounds located
   obtain ⟨b,_,accepted⟩ := List.any_eq_true.mp found
   have bits := (Bool.and_eq_true ..).mp accepted
   have lo := prove_sound (Raw state) _ _ bits.1
   have hi := prove_sound (Raw state) _ _ bits.2
   have entry := (List.getElem?_eq_getElem i.isLt).trans (congrArg some located)
   exact ⟨b,member_equal state (point a) (point b) d i
      (GeneralRebaseIntervalArgument269.interval_tight (Raw state) (point a) (point b) d known _ _ _ entry lo hi)⟩

theorem test_sound (state : State roles) (point : Fin n → Fin (Raw state).base.slots)
 (a : Fin n) (t : Test) (found : t ∈ tests state point a) :
 Head state (origin state (point a)) t := by
 unfold tests at found
 split at found
 · cases found
 · rename_i d recorded
   cases List.mem_singleton.mp found
   exact head state (point a) d recorded

theorem check_sound (state : State roles) (point : Fin n → Fin (Raw state).base.slots)
 (found : check state point = true) (inhabited : ∃ model, Models state model) :
 TestsCover state (origin state ∘ point) (tests state point) := by
 constructor
 · intro a t _ head hasIndex
   have safe := List.all_eq_true.mp found a (List.mem_finRange _)
   unfold tests
   split
   · rename_i no
     simp [no] at safe
   · rename_i d recorded
     exact List.mem_singleton.mpr (exhaust state (point a) d recorded inhabited t head hasIndex)
 · intro a t listed i _ _ active
   have safe := List.all_eq_true.mp found a (List.mem_finRange _)
   unfold tests at listed
   split at listed
   · cases listed
   · rename_i d recorded
     cases List.mem_singleton.mp listed
     have hasType := observed_is_type state (point a) d recorded i inhabited active
     have allKnown : (TypeSlots d).all (target state point d) = true := by simpa only [recorded] using safe
     exact target_sound state point a d recorded i (List.all_eq_true.mp allKnown i hasType)

def window (state : State roles) (point : Fin n → Fin (Raw state).base.slots)
 (equal : Origin → Origin → Answer) : Window n :=
 GeneralRebaseOriginEdgeScan269.assemble (origin state ∘ point) (tests state point)
   (fun _ _ => some true) equal (some true)

theorem window_sound (state : State roles) (point : Fin n → Fin (Raw state).base.slots)
 (equal : Origin → Origin → Answer) (cert : ∀ a b, Reflect (Equal state a b) (equal a b))
 (found : check state point = true) (inhabited : ∃ model, Models state model) :
 Sound state (window state point equal) ∧
 GeneralRebaseOriginQuotient269.Forward state (window state point equal).point := by
 have checked := check_sound state point found inhabited
 exact ⟨GeneralRebaseOriginEdgeScan269.assemble_sound state _ _ _ _ _ checked
   (test_sound state point) cert inhabited,GeneralRebaseOriginQuotient269.forward_of_tests state _ _ checked⟩

end Yulang.GeneralRebaseNominalWindow269
