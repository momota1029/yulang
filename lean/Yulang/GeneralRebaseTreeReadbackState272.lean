import Yulang.GeneralRebaseTreeAcyclic272

namespace Yulang.GeneralRebaseTreeReadbackState272
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Origin Observes shapeValue)
open GeneralNominalFiniteMeaning (At)
open GeneralNormalizedObservation (Shape)
open GeneralRebaseFiniteTree272 (Tree Canonical value)
open GeneralRebasePartialBool268 (Reflect Answer)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Cyclic)

inductive Result where
 | unknown
 | absent
 | many
 | found (tree : Tree)

def Meaning (m : Assignment) (o : Origin) : Result → Prop
 | .unknown => True
 | .absent => ∀ v, ¬ Observes m o v
 | .many => ∀ v, Observes m o v
 | .found tree => Canonical tree ∧ At m .actual o (value tree)

theorem no_structural_position (m : Assignment) (p : Origin) (s : Shape) (idx : Nat)
 (outside : s.arity ≤ idx) : Meaning m (.structural p s idx) .absent := by
 intro actual event
 cases event with
 | structural parent length rel found =>
   have bound := (List.getElem?_eq_some_iff.mp found).1
   rw [length] at bound
   omega

theorem any_structural (m : Assignment) (p : Origin) (s : Shape) (i : Nat)
 (all : Meaning m p .many) (inside : i < s.arity) :
 Meaning m (.structural p s i) .many := by
 intro value
 let values := List.replicate s.arity value
 have present : values[i]? = some value := by simp [values,inside]
 exact .structural (all (shapeValue s values)) (List.length_replicate ..)
   ⟨subtype_refl _,subtype_refl _⟩ present

theorem any_nominal (m : Assignment) (p : Origin) (name i : Nat)
 (all : Meaning m p .many) : Meaning m (.nominal p name i) .many := by
 intro value
 let payload : List Argument := List.replicate (i+1) (.inl value)
 exact .nominal (all (nominal name payload)) ⟨subtype_refl _,subtype_refl _⟩ (by simp [payload])

theorem no_child_of_absent_structural (m : Assignment) (p : Origin) (s : Shape) (i : Nat)
 (absent : Meaning m p .absent) : Meaning m (.structural p s i) .absent := by
 intro value event
 cases event with
 | structural parent _ _ _ => exact absent _ parent

theorem no_child_of_absent_nominal (m : Assignment) (p : Origin) (name i : Nat)
 (absent : Meaning m p .absent) : Meaning m (.nominal p name i) .absent := by
 intro value event
 cases event with
 | nominal parent _ _ => exact absent _ parent

theorem absent_acyclic {state : State roles} (m : Assignment) (valid : Models state m) (o : Origin)
 (missing : Meaning m o .absent) : ¬ Cyclic state o := by
 rintro ⟨⟨_,edge,_⟩,_⟩
 obtain ⟨v,seen⟩ := (GeneralRebaseOriginCongruence269.edge_left_live edge m valid).1
 exact missing v seen

theorem many_acyclic {state : State roles} (m : Assignment) (valid : Models state m) (o : Origin)
 (many : Meaning m o .many) : ¬ Cyclic state o := by
 rintro ⟨⟨_,edge,_⟩,_⟩
 have clash := (GeneralRebaseOriginCongruence269.edge_left_live edge m valid).2.2 _ _
   (many (.base .int)) (many (.base .str))
 have tags := GeneralDictionaryInspectionHeads215.tag_subtype
   (GeneralDictionaryInspectionHeads215.tagged_scalar .int) (GeneralDictionaryInspectionHeads215.tagged_scalar .str) clash.1
 cases tags

def decision : Result → Answer
 | .unknown => none
 | _ => some false

theorem decision_sound {state : State roles} (m : Assignment) (valid : Models state m) (o : Origin)
 (r : Result) (evidence : Meaning m o r) : Reflect (Cyclic state o) (decision r) := by
 cases r with
 | unknown => trivial
 | absent => exact absent_acyclic m valid o evidence
 | many => exact many_acyclic m valid o evidence
 | found tree => exact GeneralRebaseTreeAcyclic272.acyclic state m valid o tree evidence.1 evidence.2

end Yulang.GeneralRebaseTreeReadbackState272
