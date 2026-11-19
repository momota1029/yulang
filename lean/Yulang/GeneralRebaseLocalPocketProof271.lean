import Yulang.GeneralRebaseLocalOriginPocket271

namespace Yulang.GeneralRebaseLocalPocketProof271
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseNominalOrigin269 (Raw)
open GeneralRebaseStructuralOrigin270 (Slots shape)
open GeneralRebaseLocalOriginPocket271 (adjacent nodes points checked nominalTargets)
open GeneralRebaseOriginRepresentative270 (tightSlot)
open GeneralRebaseActualArguments269 (TypeSlots)
open GeneralRebaseSlotInequalities269 (prove)

theorem reach (state : State roles) (start endSlot : Slots state) :
 endSlot ∈ nodes state start ↔ FiniteWorklist.Path (adjacent state) start endSlot :=
 FiniteWorklist.reachable_exact (adjacent state) (Raw state).base.slots (List.finRange _) (by simp) (by simp) start endSlot

theorem rooted (state : State roles) (start : Slots state) : start ∈ nodes state start :=
 (reach state start start).mpr (.nil _)

theorem includes_neighbor (state : State roles) (start first last : Slots state)
 (inside : first ∈ nodes state start) (edge : last ∈ adjacent state first) :
 last ∈ nodes state start :=
 (reach state start last).mpr (((reach state start first).mp inside).append (.cons edge (.nil _)))

theorem enumerate (state : State roles) (start s : Slots state) :
 (∃ i, points state start i = s) ↔ s ∈ nodes state start := by
 constructor
 · rintro ⟨i,rfl⟩
   exact List.getElem_mem i.isLt
 · intro located
   obtain ⟨i,idx,found⟩ := List.mem_iff_getElem.mp located
   exact ⟨⟨i,idx⟩,found⟩

def ready (state : State roles) (s : Slots state) : Prop :=
 match (Raw state).nominals s with
 | some d => ∀ i ∈ TypeSlots d,
      match d.arguments[i.val] with
      | .type (lo,hi) => ∃ dest, tightSlot state lo hi = some dest
      | .row _ => False
 | none => match (Raw state).view.heads s with
    | .deferred _ => False
    | _ => True

theorem pocket_closed (state : State roles) (start : Slots state)
 (every : ∀ s ∈ nodes state start, ready state s) :
 checked state start = true := by
 unfold checked GeneralRebaseFullStructuralWindow271.check
 apply List.all_eq_true.mpr
 intro a _
 have member : points state start a ∈ nodes state start := (enumerate ..).mp ⟨a,rfl⟩
 have allowed := every _ member
 unfold GeneralRebaseFullStructuralWindow271.covered
 split
 · rename_i d known
   unfold ready at allowed
   rw [known] at allowed
   apply List.all_eq_true.mpr
   intro i onList
   have possible := allowed i onList
   unfold GeneralRebaseNominalWindow269.target
   split
   · rename_i row rowEq
     rw [rowEq] at possible
     exact False.elim possible
   · rename_i lo hi selected
     rw [selected] at possible
     obtain ⟨dest,found⟩ := possible
     have good : (prove (Raw state) dest lo && prove (Raw state) hi dest) = true :=
       List.find?_some (p := fun s => prove (Raw state) s lo && prove (Raw state) hi s) found
     have neighbor : dest ∈ adjacent state (points state start a) := by
       unfold adjacent
       rw [known]
       apply List.mem_filterMap.mpr
       refine ⟨.type (lo,hi),List.getElem_mem i.isLt |> (selected ▸ ·),?_⟩
       exact found
     obtain ⟨b,located⟩ := (enumerate ..).mpr (includes_neighbor state start _ dest member neighbor)
     exact List.any_eq_true.mpr ⟨b,List.mem_finRange _,located.symm ▸ good⟩
 · rename_i none
   split
   · rfl
   · rename_i kind child shapeInfo
     apply List.all_eq_true.mpr
     intro i _
     have neighbor : child i ∈ adjacent state (points state start a) := by
       unfold adjacent
       rw [none,shapeInfo]
       exact List.mem_ofFn.mpr ⟨i,rfl⟩
     obtain ⟨b,found⟩ := (enumerate ..).mpr (includes_neighbor state start _ _ member neighbor)
     exact List.any_eq_true.mpr ⟨b,List.mem_finRange _,beq_iff_eq.mpr found⟩
   · rename_i deferred reason
     unfold ready at allowed
     rw [none,reason] at allowed
     exact False.elim allowed

end Yulang.GeneralRebaseLocalPocketProof271
