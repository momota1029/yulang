import Yulang.GeneralRebaseRecordRouting271
import Yulang.GeneralRebaseRecordRecursiveFixture271

namespace Yulang.GeneralRebaseRecordQueryCases271
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalRecursiveInspection (Origin)
open GeneralRebaseStructuralOrigin270 (Slots Kind shape)
open GeneralRebaseNominalOrigin269 (Raw)
open GeneralRebaseRecordAlignment271 (visibleSet_exact)
open GeneralRebaseRecordQuery271 (raw)

theorem total_on_record (state : State roles) (slot : Slots state) (kind : Kind state)
 (children : Fin (shape state kind).arity → Slots state) (keys read : List Nat) (j : Nat)
 (recorded : (Raw state).view.heads slot = .structural kind children) (known : shape state kind = .record keys) :
 raw state slot read j ≠ .unknown := by
 unfold raw
 split
 · intro impossible; cases impossible
 · rename_i key point
   split
   · intro impossible; cases impossible
   · rw [recorded]
     let choose : GeneralNormalizedObservation.Shape → GeneralRebaseRecordQuery271.Result (Slots state) :=
       fun s => match s with
       | .record checked =>
         if GeneralRebaseRecordAlignment271.visibleSet checked read then
           match (List.finRange (shape state kind).arity).find? (fun i => checked[i.val]? == some key) with
           | some found => .child (children found)
           | none => .unknown
         else .dead
       | _ => .unknown
     change choose (shape state kind) ≠ .unknown
     rw [congrArg choose known]
     dsimp only [choose]
     split
     · rename_i good
       have hasRead : key ∈ read := by
         obtain ⟨bound,same⟩ := List.getElem?_eq_some_iff.mp point
         exact same ▸ List.getElem_mem bound
       have hasKnown := ((visibleSet_exact _ _).mp good key).mpr hasRead
       obtain ⟨i,bound,equation⟩ := List.mem_iff_getElem.mp hasKnown
       let position : Fin (shape state kind).arity := ⟨i,by rw [known]; exact bound⟩
       have yes : (keys[position.val]? == some key) = true :=
         beq_iff_eq.mpr ((List.getElem?_eq_getElem bound).trans (congrArg some equation))
       split
       · intro impossible; cases impossible
       · rename_i absent
         have no := List.find?_eq_none.mp absent position (List.mem_finRange _)
         rw [yes] at no
         contradiction
     · intro impossible; cases impossible

namespace Recursive
open GeneralRebaseRecordRecursiveFixture271 (journal model full_model points)
open GeneralRebaseRecordRouting271 (inspect inspect_sound)
open GeneralNominalVersionedCycles232 (Cyclic)

def reorderedRoot : Origin := .structural (.source 0) (.record [7,2,2]) 1
def reorderedLeaf : Origin := .structural (.source 0) (.record [7,2,2]) 0
def hiddenRepeat : Origin := .structural (.source 0) (.record [7,2,2]) 2
def wrongSet : Origin := .structural (.source 0) (.record [7,8,2]) 2
def outOfRange : Origin := .structural (.source 0) (.record [7,2]) 3

theorem same_root : inspect journal reorderedRoot = some true := by decide +kernel
theorem same_leaf : inspect journal reorderedLeaf = some false := by decide +kernel
theorem later_duplicate : inspect journal hiddenRepeat = some false := by decide +kernel
theorem cannot_change_keys : inspect journal wrongSet = some false := by decide +kernel
theorem cannot_escape_index : inspect journal outOfRange = some false := by decide +kernel

theorem not_by_literal_test : Cyclic journal reorderedRoot ∧ ¬ Cyclic journal reorderedLeaf ∧
 ¬ Cyclic journal hiddenRepeat ∧ ¬ Cyclic journal wrongSet ∧ ¬ Cyclic journal outOfRange := by
 have a := inspect_sound journal ⟨model,full_model⟩ reorderedRoot
 have b := inspect_sound journal ⟨model,full_model⟩ reorderedLeaf
 have c := inspect_sound journal ⟨model,full_model⟩ hiddenRepeat
 have d := inspect_sound journal ⟨model,full_model⟩ wrongSet
 have e := inspect_sound journal ⟨model,full_model⟩ outOfRange
 rw [same_root] at a
 rw [same_leaf] at b
 rw [later_duplicate] at c
 rw [cannot_change_keys] at d
 rw [cannot_escape_index] at e
 exact ⟨a,b,c,d,e⟩

end Recursive
end Yulang.GeneralRebaseRecordQueryCases271
