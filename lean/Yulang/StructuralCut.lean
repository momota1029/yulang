import Yulang.StructuralBase

/-!
# Cut elimination for the existing finite structural subtype preorder

`Comparison` has the structural, lattice and record rules of `Subtype`, but no
transitivity constructor. Its transitivity theorem eliminates arbitrary
intermediate types by recursion on the three finite endpoint sizes. In
particular, it does not assume that intermediate types have a fixed shape or
omit unions, intersections, duplicate record labels, or arrow input rows.

This is a theorem about the existing `StructuralBase` reference algebra, not a
choice of recursive MLsub semantics. Row transitivity is the only algebraic
assumption used for cut elimination.
-/

namespace Yulang.StructuralDecisions

open StructuralBase

variable {RowType : Type u} {leRow : RowType → RowType → Prop}

def nodes : Ty RowType → Nat
  | .base _ | .bottom | .top | .emptyRecord => 1
  | .union left right | .inter left right | .pair left right =>
      1 + nodes left + nodes right
  | .record _ value rest => 1 + nodes value + nodes rest
  | .variant _ value => 1 + nodes value
  | .arrow input _ output _ => 1 + nodes input + nodes output

theorem lookup_nodes_lt (type : Ty RowType) (label : Nat) (value : Ty RowType)
    (found : type.lookup label = some value) : nodes value < nodes type := by
  induction type with
  | record name head tail _ ih =>
      by_cases equal : label = name
      · simp [Ty.lookup, equal] at found
        cases found
        simp only [nodes]
        omega
      · have inside : tail.lookup label = some value := by
          simpa only [Ty.lookup, ite_eq_right equal] using found
        have smaller := ih inside
        simp only [nodes]
        omega
  | _ => simp [Ty.lookup] at found

inductive Comparison (leRow : RowType → RowType → Prop) :
    Ty RowType → Ty RowType → Prop where
  | refl (type : Ty RowType) : Comparison leRow type type
  | bottom (type : Ty RowType) : Comparison leRow .bottom type
  | top (type : Ty RowType) : Comparison leRow type .top
  | unionElim : Comparison leRow left target → Comparison leRow right target →
      Comparison leRow (.union left right) target
  | interIntro : Comparison leRow source left → Comparison leRow source right →
      Comparison leRow source (.inter left right)
  | unionLeft : Comparison leRow source left →
      Comparison leRow source (.union left right)
  | unionRight : Comparison leRow source right →
      Comparison leRow source (.union left right)
  | interLeft : Comparison leRow left target →
      Comparison leRow (.inter left right) target
  | interRight : Comparison leRow right target →
      Comparison leRow (.inter left right) target
  | pair : Comparison leRow left left' → Comparison leRow right right' →
      Comparison leRow (.pair left right) (.pair left' right')
  | variant : Comparison leRow payload payload' →
      Comparison leRow (.variant label payload) (.variant label payload')
  | arrow : Comparison leRow input' input → leRow inputRow' inputRow →
      Comparison leRow output output' → leRow outputRow outputRow' →
      Comparison leRow (.arrow input inputRow output outputRow)
        (.arrow input' inputRow' output' outputRow')
  | record : IsRecord source → IsRecord target →
      (∀ label expected, target.lookup label = some expected →
        ∃ actual, source.lookup label = some actual) →
      (∀ label actual expected, source.lookup label = some actual →
        target.lookup label = some expected → Comparison leRow actual expected) →
      Comparison leRow source target

theorem Comparison.sound {source target : Ty RowType}
    (comparison : Comparison leRow source target) : Subtype leRow source target := by
  induction comparison with
  | refl => exact .refl _
  | bottom => exact .bottom _
  | top => exact .top _
  | unionElim _ _ left right => exact .unionElim left right
  | interIntro _ _ left right => exact .interIntro left right
  | unionLeft _ ih => exact .trans ih (.unionLeft _ _)
  | unionRight _ ih => exact .trans ih (.unionRight _ _)
  | interLeft _ ih => exact .trans (.interLeft _ _) ih
  | interRight _ ih => exact .trans (.interRight _ _) ih
  | pair _ _ left right => exact .pair left right
  | variant _ ih => exact .variant ih
  | arrow _ rowIn _ rowOut input output => exact .arrow input rowIn output rowOut
  | record sourceShape targetShape fields _ ih =>
      exact .record sourceShape targetShape fields ih

/-- Cut elimination does not bound the size of a hypothetical intermediate
type. Its three endpoints strictly shrink in every recursive call. -/
theorem Comparison.trans
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    {source middle target : Ty RowType}
    (first : Comparison leRow source middle) (second : Comparison leRow middle target) :
    Comparison leRow source target := by
  cases first with
  | refl => exact second
  | bottom => exact .bottom _
  | top =>
      cases second with
      | refl => exact .top _
      | top => exact .top _
      | interIntro left right =>
          exact .interIntro (trans rowTrans (.top _) left) (trans rowTrans (.top _) right)
      | unionLeft rest => exact .unionLeft (trans rowTrans (.top _) rest)
      | unionRight rest => exact .unionRight (trans rowTrans (.top _) rest)
      | record shape _ _ _ => cases shape
  | unionElim left right =>
      exact .unionElim (trans rowTrans left second) (trans rowTrans right second)
  | interLeft part => exact .interLeft (trans rowTrans part second)
  | interRight part => exact .interRight (trans rowTrans part second)
  | unionLeft part =>
      cases second with
      | refl => exact .unionLeft part
      | top => exact .top _
      | unionElim left _ => exact trans rowTrans part left
      | interIntro left right =>
          exact .interIntro (trans rowTrans (.unionLeft part) left)
            (trans rowTrans (.unionLeft part) right)
      | unionLeft rest => exact .unionLeft (trans rowTrans (.unionLeft part) rest)
      | unionRight rest => exact .unionRight (trans rowTrans (.unionLeft part) rest)
      | record shape _ _ _ => cases shape
  | unionRight part =>
      cases second with
      | refl => exact .unionRight part
      | top => exact .top _
      | unionElim _ right => exact trans rowTrans part right
      | interIntro left right =>
          exact .interIntro (trans rowTrans (.unionRight part) left)
            (trans rowTrans (.unionRight part) right)
      | unionLeft rest => exact .unionLeft (trans rowTrans (.unionRight part) rest)
      | unionRight rest => exact .unionRight (trans rowTrans (.unionRight part) rest)
      | record shape _ _ _ => cases shape
  | interIntro left right =>
      cases second with
      | refl => exact .interIntro left right
      | top => exact .top _
      | interLeft rest => exact trans rowTrans left rest
      | interRight rest => exact trans rowTrans right rest
      | interIntro first last =>
          exact .interIntro (trans rowTrans (.interIntro left right) first)
            (trans rowTrans (.interIntro left right) last)
      | unionLeft rest => exact .unionLeft (trans rowTrans (.interIntro left right) rest)
      | unionRight rest => exact .unionRight (trans rowTrans (.interIntro left right) rest)
      | record shape _ _ _ => cases shape
  | pair left right =>
      cases second with
      | refl => exact .pair left right
      | top => exact .top _
      | interIntro first last =>
          exact .interIntro (trans rowTrans (.pair left right) first)
            (trans rowTrans (.pair left right) last)
      | unionLeft rest => exact .unionLeft (trans rowTrans (.pair left right) rest)
      | unionRight rest => exact .unionRight (trans rowTrans (.pair left right) rest)
      | pair first last => exact .pair (trans rowTrans left first) (trans rowTrans right last)
      | record shape _ _ _ => cases shape
  | variant payload =>
      cases second with
      | refl => exact .variant payload
      | top => exact .top _
      | interIntro first last =>
          exact .interIntro (trans rowTrans (.variant payload) first)
            (trans rowTrans (.variant payload) last)
      | unionLeft rest => exact .unionLeft (trans rowTrans (.variant payload) rest)
      | unionRight rest => exact .unionRight (trans rowTrans (.variant payload) rest)
      | variant rest => exact .variant (trans rowTrans payload rest)
      | record shape _ _ _ => cases shape
  | arrow input inputRow output outputRow =>
      cases second with
      | refl => exact .arrow input inputRow output outputRow
      | top => exact .top _
      | interIntro first last =>
          exact .interIntro (trans rowTrans (.arrow input inputRow output outputRow) first)
            (trans rowTrans (.arrow input inputRow output outputRow) last)
      | unionLeft rest =>
          exact .unionLeft (trans rowTrans (.arrow input inputRow output outputRow) rest)
      | unionRight rest =>
          exact .unionRight (trans rowTrans (.arrow input inputRow output outputRow) rest)
      | arrow first firstRow last lastRow =>
          exact .arrow (trans rowTrans first input) (rowTrans firstRow inputRow)
            (trans rowTrans output last) (rowTrans outputRow lastRow)
      | record shape _ _ _ => cases shape
  | @record source middle sourceShape middleShape fields comparisons =>
      cases second with
      | refl => exact .record sourceShape middleShape fields comparisons
      | top => exact .top _
      | interIntro first last =>
          exact .interIntro (trans rowTrans (.record sourceShape middleShape fields comparisons) first)
            (trans rowTrans (.record sourceShape middleShape fields comparisons) last)
      | unionLeft rest =>
          exact .unionLeft (trans rowTrans (.record sourceShape middleShape fields comparisons) rest)
      | unionRight rest =>
          exact .unionRight (trans rowTrans (.record sourceShape middleShape fields comparisons) rest)
      | @record _ target _ targetShape nextFields nextComparisons =>
          apply Comparison.record sourceShape targetShape
          · intro label expected expectedFound
            obtain ⟨between, betweenFound⟩ := nextFields label expected expectedFound
            exact fields label between betweenFound
          · intro label actual expected actualFound expectedFound
            obtain ⟨between, betweenFound⟩ := nextFields label expected expectedFound
            exact trans rowTrans (comparisons label actual between actualFound betweenFound)
              (nextComparisons label between expected betweenFound expectedFound)
      | bottom => cases middleShape
      | unionElim => cases middleShape
      | interLeft => cases middleShape
      | interRight => cases middleShape
      | pair => cases middleShape
      | variant => cases middleShape
      | arrow => cases middleShape
termination_by nodes source + nodes middle + nodes target
decreasing_by
  all_goals try simp_wf
  all_goals subst_vars
  all_goals try simp only [nodes]
  all_goals first
    | omega
    | have firstSmaller := lookup_nodes_lt _ _ _ actualFound
      have middleSmaller := lookup_nodes_lt _ _ _ betweenFound
      have lastSmaller := lookup_nodes_lt _ _ _ expectedFound
      omega

theorem Comparison.complete
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    {source target : Ty RowType} (subtype : Subtype leRow source target) :
    Comparison leRow source target := by
  induction subtype with
  | refl => exact .refl _
  | trans _ _ left right => exact Comparison.trans (leRow := leRow) rowTrans left right
  | bottom => exact .bottom _
  | top => exact .top _
  | unionLeft => exact .unionLeft (.refl _)
  | unionRight => exact .unionRight (.refl _)
  | unionElim _ _ left right => exact .unionElim left right
  | interLeft => exact .interLeft (.refl _)
  | interRight => exact .interRight (.refl _)
  | interIntro _ _ left right => exact .interIntro left right
  | pair _ _ left right => exact .pair left right
  | variant _ ih => exact .variant ih
  | arrow _ inputRow _ outputRow input output => exact .arrow input inputRow output outputRow
  | record sourceShape targetShape fields _ ih =>
      exact .record sourceShape targetShape fields ih

theorem comparison_iff_subtype
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (source target : Ty RowType) :
    Comparison leRow source target ↔ Subtype leRow source target :=
  ⟨Comparison.sound, fun proof => Comparison.complete (leRow := leRow) rowTrans proof⟩

end Yulang.StructuralDecisions
