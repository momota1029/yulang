import Yulang.GeneralDeclarativeWitnessNativeNestedMatch361

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessNestedReflection361
open GeneralDeclarativeWitnessConstructorModes357 (SourceMode Mode Use readUse)
open GeneralDeclarativeWitnessModeCoverage357 (available readUse_exact)
open GeneralDeclarativeWitnessNativeKinds361 (Ctor readCtor)
open GeneralDeclarativeWitnessNativeNestedMatch361 (Matches)

theorem sourced_mode_unique {e n} {first last : Mode}
    (left : SourceMode e n first) (right : SourceMode e n last) : first = last := by
  obtain ⟨a,found,x⟩ := available left
  obtain ⟨b,also,y⟩ := available right
  have up : a = b := Option.some.inj (found.symm.trans also)
  exact x.symm.trans ((congrArg Subtype.val up).trans y)

theorem checked_constructor_mode_unique {e n k} (a b : Ctor e n k) : a.mode = b.mode := by
  have same := sourced_mode_unique a.use.sourced b.use.sourced
  have reference := a.exact
  rw [same] at reference
  exact Option.some.inj (reference.symm.trans b.exact)

theorem read_constructor_returns_same_mode {e n k} (independent : Ctor e n k) :
    ∃ result, readCtor e n k = some result ∧ result.mode = independent.mode := by
  have can := readUse_exact.mpr ⟨independent.use⟩
  cases found : readUse e n k with
  | none => simp [found] at can
  | some u =>
    have same := sourced_mode_unique independent.use.sourced u.sourced
    have value := independent.exact
    rw [same] at value
    refine ⟨⟨u,independent.mode,value⟩,?_,rfl⟩
    simp only [readCtor,found,bind,Option.bind]
    split
    · rename_i absent
      rw [value] at absent
      cases absent
    · rename_i selected seen
      have sameTag := Option.some.inj (seen.symm.trans value)
      cases sameTag
      rfl

/-- Exact recovery for the explicitly represented unary/nullary
source-route judgment, not for Yulang selection as a whole. In
particular, the entire interval, not just its value in one model,
is recovered for each captured binder. -/
theorem read_recovers_source_intervals {e locals source code pattern caps}
    (independent : Matches e locals source code pattern caps) :
    ∃ result, GeneralDeclarativeWitnessNativeNestedMatch361.read e locals source code pattern = some result ∧ result.1 = caps := by
  induction independent with
  | leaf proof =>
    refine ⟨⟨_,.leaf proof⟩,?_,rfl⟩
    simp only [GeneralDeclarativeWitnessNativeNestedMatch361.read]
    split
    · rename_i absent
      rw [proof] at absent
      cases absent
    · rename_i stated seen
      have same := Option.some.inj (seen.symm.trans proof)
      cases same
      simp
  | empty u =>
    obtain ⟨found,actual,_⟩ := read_constructor_returns_same_mode u
    exact ⟨⟨[],.empty found⟩,by simp [GeneralDeclarativeWitnessNativeNestedMatch361.read,actual],rfl⟩
  | unary u _ ih =>
    obtain ⟨out,ran,same⟩ := ih
    obtain ⟨found,actual,_⟩ := read_constructor_returns_same_mode u
    refine ⟨⟨out.1,.unary found out.2⟩,?_,same⟩
    simp [GeneralDeclarativeWitnessNativeNestedMatch361.read,actual,ran]

theorem read_has_exact_represented_judgment {e locals source code pattern} :
    (GeneralDeclarativeWitnessNativeNestedMatch361.read e locals source code pattern).isSome = true ↔
      ∃ captures,Nonempty (Matches e locals source code pattern captures) := by
  constructor
  · intro h
    cases eq : GeneralDeclarativeWitnessNativeNestedMatch361.read e locals source code pattern with
    | none => simp [eq] at h
    | some out => exact ⟨out.1,⟨out.2⟩⟩
  · rintro ⟨_,⟨sourceProof⟩⟩
    obtain ⟨_,h,_⟩ := read_recovers_source_intervals sourceProof
    simp [h]


theorem same_lexical_read_cannot_choose_two_capture_lists {e locals source code pattern a b}
    (first : Matches e locals source code pattern a) (last : Matches e locals source code pattern b) :
    a = b := by
  obtain ⟨one,exactOne,chosenOne⟩ := read_recovers_source_intervals first
  obtain ⟨two,exactTwo,chosenTwo⟩ := read_recovers_source_intervals last
  have same := Option.some.inj (exactOne.symm.trans exactTwo)
  exact chosenOne.symm.trans ((congrArg Sigma.fst same).trans chosenTwo)

def left : GeneralDeclarativeWhere319.Capture := ⟨4,42,5⟩
def right : GeneralDeclarativeWhere319.Capture := ⟨6,42,7⟩

/-- Numerical equality of the native leaf exposes only the common
center. The actual lexical read determines the entire capture. -/
theorem same_center_does_not_recover_source_intervals
    (e : GeneralDeclarativeWitnessConstructorModes357.Environment) :
    Nonempty (Matches e (fun _ => some left) (.bind 80) (.leaf 42) (.var 92) [(92,left)]) ∧
    Nonempty (Matches e (fun _ => some right) (.bind 80) (.leaf 42) (.var 92) [(92,right)]) ∧
    left.lower ≠ right.lower ∧ left.upper ≠ right.upper := by
  refine ⟨⟨Matches.leaf (writer := 80) (receiver := 92) (span := left) rfl⟩,?_,by decide,by decide⟩
  exact ⟨Matches.leaf (writer := 80) (receiver := 92) (span := right) rfl⟩

end Yulang.GeneralDeclarativeWitnessNestedReflection361
