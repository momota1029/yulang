import Yulang.GeneralRebaseJournalInequalities269
import Yulang.GeneralRebaseOriginCongruence269
import Yulang.GeneralRebaseMergeCenters267

namespace Yulang.GeneralRebaseSameInputs269
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Equal)
open GeneralNominalDemandMerging (All₂ Related)
open GeneralNominalCenters (Site SameInputs)
open GeneralNominalRecursiveInspection (Origin Observes)
open GeneralRebaseJournalInequalities269 (Between prove prove_sound)
open GeneralRebasePartialBool268 (Answer Reflect both)
open GeneralRebasePartialFinite268 (transfer)
open CommonNominalFullCarrier

theorem raw_source_eq (state : State roles) (a b : Nat) :
 Equal state (.source a) (.source b) ↔ Between state a b ∧ Between state b a := by
 constructor
 · intro same
   constructor <;> intro model valid
   · exact ((same model valid).2.2 _ _ (.source a) (.source b)).1
   · exact ((same model valid).2.2 _ _ (.source a) (.source b)).2
 · rintro ⟨one,two⟩ model valid
   refine ⟨⟨_,.source a⟩,⟨_,.source b⟩,?_⟩
   intro x y hx hy
   cases hx
   cases hy
   exact ⟨one model valid,two model valid⟩

def le (state : State roles) (fallback : Nat → Nat → Answer) (a b : Nat) : Answer :=
 if prove state a b then some true else fallback a b

theorem le_sound (state : State roles) (fallback : Nat → Nat → Answer) (a b : Nat)
 (cert : Reflect (Between state a b) (fallback a b)) : Reflect (Between state a b) (le state fallback a b) := by
 unfold le
 split
 · rename_i yes
   exact prove_sound state a b yes
 · exact cert

def eq (state : State roles) (fallback : Nat → Nat → Answer) (a b : Nat) : Answer :=
 both (le state fallback a b) (le state fallback b a)

theorem eq_sound (state : State roles) (fallback : Nat → Nat → Answer)
 (cert : ∀ a b, Reflect (Between state a b) (fallback a b)) (a b : Nat) :
 Reflect (Equal state (.source a) (.source b)) (eq state fallback a b) :=
 transfer (raw_source_eq state a b).symm
   (GeneralRebasePartialBool268.both_sound (le_sound state fallback a b (cert a b))
      (le_sound state fallback b a (cert b a)))

def givenNames (names : List Nat) : List (Option Origin) := names.map (fun a => some (.source a))

theorem related_source (state : State roles) (a b : Nat) :
 Related (Models state) (some (.source a)) (some (.source b)) ↔ Equal state (.source a) (.source b) := by
 constructor
 · rintro ⟨x,y,hx,hy,same⟩
   cases Option.some.inj hx
   cases Option.some.inj hy
   exact same
 · intro same
   exact ⟨_,_,rfl,rfl,same⟩

def zipped (test : Nat → Nat → Answer) : List Nat → List Nat → Answer
 | [],[] => some true
 | a :: as,b :: bs => both (test a b) (zipped test as bs)
 | _,_ => some false

theorem zipped_sound (state : State roles) (test : Nat → Nat → Answer)
 (cert : ∀ a b, Reflect (Equal state (.source a) (.source b)) (test a b)) (one two : List Nat) :
 Reflect (All₂ (Related (Models state)) (givenNames one) (givenNames two)) (zipped test one two) := by
 induction one generalizing two with
 | nil =>
   cases two with
   | nil => exact .nil
   | cons b bs => intro bad; cases bad
 | cons a as ih =>
   cases two with
   | nil => intro bad; cases bad
   | cons b bs =>
     apply transfer (p := Related (Models state) (some (.source a)) (some (.source b)) ∧
       All₂ (Related (Models state)) (givenNames as) (givenNames bs))
     · constructor
       · rintro ⟨head,tail⟩
         exact .cons head tail
       · intro hs
         cases hs with
         | cons head tail => exact ⟨head,tail⟩
     · exact GeneralRebasePartialBool268.both_sound
         (transfer (related_source state a b).symm (cert a b)) (ih bs)

def probe (state : State roles) (fallback : Nat → Nat → Answer) (first last : Site roles) : Answer :=
 if first.occurrence.demand.role = last.occurrence.demand.role then
   zipped (eq state fallback) (GeneralRebaseMergeCenters267.centers first) (GeneralRebaseMergeCenters267.centers last)
 else some false

theorem probe_sound (state : State roles) (fallback : Nat → Nat → Answer)
 (cert : ∀ a b, Reflect (Between state a b) (fallback a b)) (first last : Site roles) :
 Reflect (SameInputs (Models state) first last) (probe state fallback first last) := by
 unfold probe
 split
 · rename_i role
   apply transfer (p := All₂ (Related (Models state))
       (givenNames (GeneralRebaseMergeCenters267.centers first))
       (givenNames (GeneralRebaseMergeCenters267.centers last)))
   · unfold SameInputs GeneralNominalDemandMerging.SameInputs givenNames
     rw [GeneralRebaseMergeCenters267.observed first,GeneralRebaseMergeCenters267.observed last]
     exact ⟨fun h => ⟨role,h⟩,And.right⟩
   · exact zipped_sound state _ (eq_sound state fallback cert) _ _
 · rename_i role
   exact fun h => role h.1

end Yulang.GeneralRebaseSameInputs269
