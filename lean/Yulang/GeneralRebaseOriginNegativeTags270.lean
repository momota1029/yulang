import Yulang.GeneralRebaseMixedOriginWindow270

namespace Yulang.GeneralRebaseOriginNegativeTags270
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Equal)
open GeneralNominalRecursiveInspection (Origin Test)
open GeneralRebaseNominalOrigin269 (Raw origin)
open GeneralRebaseStructuralOrigin270 (Slots shape shape_head scalar_head)
open GeneralRebasePartialBool268 (Answer Reflect)
open GeneralNominalFiniteHeadInversion renaming head → tag
open GeneralDictionaryInspectionHeads215 (tag_subtype tagged_test)

def test (state : State roles) (s : Slots state) : Option Test :=
 match (Raw state).nominals s with
 | some d => some (GeneralRebaseNominalOrigin269.tag d)
 | none =>
   match (Raw state).view.heads s with
   | .structural k _ => some (.structural (shape state k))
   | .scalar b => some (.scalar b)
   | .deferred _ => none

theorem test_sound (state : State roles) (s : Slots state) (t : Test) (found : test state s = some t) :
 GeneralNominalVersionedCycles232.Head state (origin state s) t := by
 unfold test at found
 split at found
 · rename_i d recorded
   injection found with eq
   exact eq ▸ GeneralRebaseNominalOrigin269.head state s d recorded
 · split at found
   · rename_i k children recorded
     injection found with eq
     exact eq ▸ shape_head state s k children recorded
   · rename_i base recorded
     injection found with eq
     exact eq ▸ scalar_head state s base recorded
   · contradiction

theorem distinct (state : State roles) (a b : Slots state) (t u : Test)
 (left : test state a = some t) (right : test state b = some u)
 (different : tag t ≠ tag u) (inhabited : ∃ m, Models state m) :
 ¬ Equal state (origin state a) (origin state b) := by
 obtain ⟨m,valid⟩ := inhabited
 intro semantic
 have both := semantic m valid
 have one := (test_sound state a t left m valid).2 _ (.source _)
 have two := (test_sound state b u right m valid).2 _ (.source _)
 exact different (tag_subtype (tagged_test t one) (tagged_test u two) (both.2.2 _ _ (.source _) (.source _)).1)

def onSlots (state : State roles) (a b : Slots state) : Answer :=
 if (Raw state).base.source a = (Raw state).base.source b then some true
 else match test state a, test state b with
 | some t, some u => if tag t ≠ tag u then some false else none
 | _, _ => none

theorem onSlots_sound (state : State roles) (a b : Slots state) (inhabited : ∃ m, Models state m) :
 Reflect (Equal state (origin state a) (origin state b)) (onSlots state a b) := by
 unfold onSlots
 split
 · rename_i same
   unfold origin
   rw [same]
   exact fun m _ => GeneralNominalOriginTerms.source_self m _
 · split
   · rename_i t u left right
     split
     · exact distinct state a b t u left right (by assumption) inhabited
     · trivial
   · trivial

def sourceSlot (state : State roles) (id : Nat) : Option (Slots state) :=
 (List.finRange (Raw state).base.slots).find? (fun s => (Raw state).base.source s == id)

theorem sourceSlot_sound (state : State roles) (id : Nat) (s : Slots state)
 (known : sourceSlot state id = some s) : origin state s = .source id := by
 have hit := List.find?_some known
 exact congrArg Origin.source (beq_iff_eq.mp hit)

def compare (state : State roles) : Origin → Origin → Answer
 | .source a, .source b =>
   if a = b then some true
   else match sourceSlot state a, sourceSlot state b with
   | some s, some t => onSlots state s t
   | _, _ => none
 | _, _ => none

theorem compare_sound (state : State roles) (inhabited : ∃ m, Models state m) (a b : Origin) :
 Reflect (Equal state a b) (compare state a b) := by
 unfold compare
 split
 · rename_i i j
   split
   · rename_i same
     subst j
     exact fun m _ => GeneralNominalOriginTerms.source_self m _
   · split
     · rename_i s t left right
       exact sourceSlot_sound state i s left ▸ sourceSlot_sound state j t right ▸ onSlots_sound state s t inhabited
     · trivial
 · trivial

end Yulang.GeneralRebaseOriginNegativeTags270
