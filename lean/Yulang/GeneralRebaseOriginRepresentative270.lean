import Yulang.GeneralRebaseOriginNegativeTags270

namespace Yulang.GeneralRebaseOriginRepresentative270
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Equal)
open GeneralNominalRecursiveInspection (Origin)
open GeneralNominalOriginTerms (project)
open GeneralRebaseNominalOrigin269 (Raw origin tag member_equal)
open GeneralRebaseStructuralOrigin270 (Slots)
open GeneralRebaseOriginNegativeTags270 (sourceSlot sourceSlot_sound onSlots onSlots_sound)
open GeneralRebasePartialBool268 (Answer Reflect)
open GeneralRebaseSlotInequalities269 (prove prove_sound)
open GeneralRebaseOriginCongruence269 (equal_symm equal_trans)

def tightSlot (state : State roles) (lo hi : Slots state) : Option (Slots state) :=
 (List.finRange (Raw state).base.slots).find? (fun s => prove (Raw state) s lo && prove (Raw state) hi s)

def representative (state : State roles) : Origin → Option (Slots state)
 | .source n => sourceSlot state n
 | .nominal (.source parent) name index => do
   let a ← sourceSlot state parent
   let d ← (Raw state).nominals a
   if d.declaration.name = name then
     match d.arguments[index]? with
     | some (.type (lo,hi)) => tightSlot state lo hi
     | _ => none
   else none
 | _ => none

theorem tightSlot_sound (state : State roles) (parent : Slots state)
 (d : GeneralNominalState.Descriptor (Raw state).base.slots) (recorded : (Raw state).nominals parent = some d)
 (index : Nat) {lo hi target : Slots state} (entry : d.arguments[index]? = some (.type (lo,hi)))
 (found : tightSlot state lo hi = some target) :
 Equal state (.nominal (origin state parent) d.declaration.name index) (origin state target) := by
 have hit : (prove (Raw state) target lo && prove (Raw state) hi target) = true := List.find?_some (p := fun s => prove (Raw state) s lo && prove (Raw state) hi s) found
 have bits := (Bool.and_eq_true ..).mp hit
 have lt := List.getElem?_eq_some_iff.mp entry
 exact member_equal state parent target d ⟨index,lt.1⟩
   (GeneralRebaseIntervalArgument269.interval_tight (Raw state) parent target d recorded _ _ _ entry
     (prove_sound _ _ _ bits.1) (prove_sound _ _ _ bits.2))

theorem representative_sound (state : State roles) (o : Origin) (s : Slots state)
 (found : representative state o = some s) : Equal state o (origin state s) := by
 unfold representative at found
 split at found
 · rename_i n
   rw [sourceSlot_sound state n s found]
   exact fun m _ => GeneralNominalOriginTerms.source_self m _
 · rename_i parent name index
   cases one : sourceSlot state parent with
   | none => simp [one] at found
   | some a =>
     cases two : (Raw state).nominals a with
     | none => simp [one,two] at found
     | some d =>
       simp [one,two,Bind.bind,Option.bind] at found
       split at found
       · rename_i lo hi entry
         rw [← sourceSlot_sound state parent a one,← found.1]
         exact tightSlot_sound state a d two index entry found.2
       · cases found.2
 · contradiction

def compare (state : State roles) (a b : Origin) : Answer :=
 (GeneralRebaseOriginNegativeTags270.compare state a b).or
  (match representative state a, representative state b with
    | some x, some y => onSlots state x y
    | _, _ => none)

theorem compare_sound (state : State roles) (inhabited : ∃ m, Models state m) (a b : Origin) :
 Reflect (Equal state a b) (compare state a b) := by
 unfold compare
 cases previous : GeneralRebaseOriginNegativeTags270.compare state a b with
 | some answer =>
   simpa [previous,Option.or] using GeneralRebaseOriginNegativeTags270.compare_sound state inhabited a b
 | none =>
   simp only [Option.or]
   split
   · rename_i x y left right
     have xEq := representative_sound state a x left
     have yEq := representative_sound state b y right
     exact GeneralRebasePartialFinite268.transfer (show Equal state a b ↔ Equal state (origin state x) (origin state y) from
       ⟨fun e => equal_trans (equal_symm xEq) (equal_trans e yEq),
         fun e => equal_trans xEq (equal_trans e (equal_symm yEq))⟩).symm
       (onSlots_sound state x y inhabited)
   · trivial

def window (state : State roles) (point : Fin n → Slots state) :=
 GeneralRebaseMixedOriginWindow270.window state point (compare state)

def query (state : State roles) (point : Fin n → Slots state) (o : Origin) : Answer :=
 GeneralRebaseOriginExecutable269.cyclic (window state point)
   (fun x i => compare state x (origin state (point i))) (fun _ => true) (fun _ => false) o

theorem query_sound (state : State roles) (point : Fin n → Slots state)
 (closed : GeneralRebaseMixedOriginWindow270.check state point = true)
 (inhabited : ∃ m, Models state m) (o : Origin) :
 Reflect (GeneralNominalVersionedCycles232.Cyclic state o) (query state point o) := by
 have cert := GeneralRebaseMixedOriginWindow270.certified state point (compare state)
   (compare_sound state inhabited) closed inhabited
 exact GeneralRebaseOriginExecutable269.with_semantic_closure _ cert.1 _
   (fun i => compare_sound state inhabited o (origin state (point i))) cert.2

end Yulang.GeneralRebaseOriginRepresentative270
