import Yulang.GeneralRebaseFiniteTreeCode272
import Yulang.GeneralRebaseTreeActual218272

namespace Yulang.GeneralRebaseFiniteTreeCompare272
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Origin)
open GeneralNominalOriginTerms (Same same_symm)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Equal)
open GeneralRebaseTreeReadbackState272 (Result Meaning)
open GeneralRebaseTreeInterpreter272 (Source Certified run run_sound)
open GeneralRebaseFiniteTree272 (Tree)
open GeneralRebaseFiniteTreeCode272 (same same_exact)
open GeneralRebasePartialBool268 (Answer Reflect)

theorem absent_left (m : Assignment) (a b : Origin) (cert : Meaning m a .absent) : ¬ Same m a b :=
 fun matched => let ⟨actual,found⟩ := matched.1; cert actual found

theorem many_left (m : Assignment) (a b : Origin) (cert : Meaning m a .many) : ¬ Same m a b := by
 intro found
 obtain ⟨u,observed⟩ := found.2.1
 have first := found.2.2 _ _ (cert (.base .int)) observed
 have other := found.2.2 _ _ (cert (.base .str)) observed
 have clash := GeneralDictionaryInspectionHeads215.tag_subtype
   (GeneralDictionaryInspectionHeads215.tagged_scalar .int) (GeneralDictionaryInspectionHeads215.tagged_scalar .str)
   (subtype_trans first.1 other.2)
 cases clash

theorem found_exact (m : Assignment) (a b : Origin) (t u : Tree)
 (left : Meaning m a (.found t)) (right : Meaning m b (.found u)) : Same m a b ↔ t = u := by
 constructor
 · intro both
   obtain ⟨x,first⟩ := left.2.1
   obtain ⟨y,last⟩ := right.2.1
   have one := left.2.2 _ first
   have two := right.2.2 _ last
   have same := both.2.2 _ _ first last
   exact GeneralRebaseCanonicalUniqueness272.exact _ _ left.1 right.1
     ⟨subtype_trans one.2 (subtype_trans same.1 two.1),subtype_trans two.2 (subtype_trans same.2 one.1)⟩
 · rintro rfl
   refine ⟨left.2.1,right.2.1,?_⟩
   intro x y one two
   exact ⟨subtype_trans (left.2.2 _ one).1 (right.2.2 _ two).2,
     subtype_trans (right.2.2 _ two).1 (left.2.2 _ one).2⟩

def compare : Result → Result → Answer
 | .found a,.found b => some (same a b)
 | .absent,_ | _,.absent | .many,_ | _,.many => some false
 | _,_ => none

theorem compare_sound (m : Assignment) (a b : Origin) (left right : Result)
 (one : Meaning m a left) (two : Meaning m b right) :
 Reflect (Same m a b) (compare left right) := by
 cases left <;> cases right
 all_goals first
   | exact absent_left m a b one
   | exact fun h => absent_left m b a two (same_symm h)
   | exact many_left m a b one
   | exact fun h => many_left m b a two (same_symm h)
   | rename_i x y
     exact GeneralRebaseRawK2Probe268.bool_reflect _ _ ((same_exact x y).trans (found_exact m a b x y one two).symm)
   | trivial

def modelLookup (seed : Source) (a b : Origin) : Answer := compare (run seed a) (run seed b)

theorem local_sound (m : Assignment) (seed : Source) (cert : Certified m seed) (a b : Origin) :
 Reflect (Same m a b) (modelLookup seed a b) :=
 compare_sound m a b _ _ (run_sound m seed cert a) (run_sound m seed cert b)

def reject (seed : Source) (a b : Origin) : Answer :=
 if modelLookup seed a b = some false then some false else none

theorem reject_sound (state : State roles) (m : Assignment) (valid : Models state m)
 (seed : Source) (cert : Certified m seed) (a b : Origin) : Reflect (Equal state a b) (reject seed a b) := by
 unfold reject
 split
 · rename_i hits
   have answer := local_sound m seed cert a b
   rw [hits] at answer
   exact fun eq => answer (eq m valid)
 · trivial

/-- Agreement alone is not allowed to set the all-model positive bit. -/
theorem no_positive (seed : Source) (a b : Origin) : reject seed a b ≠ some true := by
 unfold reject
 split <;> intro clash <;> cases clash

namespace Actual218
open GeneralRebaseTreeActual218272 (source certified)
open GeneralDictionaryGroundCopy218Install (model)
open GeneralDictionaryMixedGround218Install234 (installed installed_model)

def left : Origin := .nominal (.source 6) 5 0
def right : Origin := .nominal (.source 6) 5 1

theorem computed_unequal : reject source left right = some false := rfl

theorem current_not_equal : ¬ Equal installed left right := by
 have cert := reject_sound installed model installed_model source certified left right
 rw [computed_unequal] at cert
 exact cert

end Actual218
end Yulang.GeneralRebaseFiniteTreeCompare272
