import Yulang.GeneralRebaseTreeProjection272

namespace Yulang.GeneralRebaseTreeAcyclic272
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Origin)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedCycles232 (Edge Path Cyclic)
open GeneralNominalFiniteMeaning (At)
open GeneralRebaseFiniteTree272 (Tree value height Canonical child_height height_invariant at_agree)

theorem edge_descends (state : State roles) (m : Assignment) (valid : Models state m)
 (first last : Origin) (tree : Tree) (can : Canonical tree)
 (known : At m .actual first (value tree)) (edge : Edge state first last) :
 ∃ child, Canonical child ∧ At m .actual last (value child) ∧ height child < height tree := by
 obtain ⟨_,q,i,head,live⟩ := (GeneralRebaseOriginCongruence269.edge_normal state _ _).mp edge
 cases tree with
 | node t kids =>
   obtain ⟨k,actual⟩ := GeneralRebaseTreeProjection272.child_of_live m first last t q
     (fun j => value (kids j)) i can.1 known (head m valid) (live m valid)
   exact ⟨kids k,can.2 k,actual,child_height t kids k⟩

theorem path_descends (state : State roles) (m : Assignment) (valid : Models state m)
 (actual : Path state first last) (tree : Tree) (can : Canonical tree)
 (known : At m .actual first (value tree)) :
 ∃ lower, Canonical lower ∧ At m .actual last (value lower) ∧ height lower ≤ height tree := by
 induction actual generalizing tree with
 | nil => exact ⟨tree,can,known,Nat.le_refl _⟩
 | cons edge _ ih =>
   obtain ⟨next,cert,actual,less⟩ := edge_descends state m valid _ _ _ can known edge
   obtain ⟨atEnd,checked,atLeast,nonincrease⟩ := ih next cert actual
   exact ⟨atEnd,checked,atLeast,Nat.le_trans nonincrease (Nat.le_of_lt less)⟩

/-- The checked finite readback of this particular origin in one full
model suffices. No claim is made that a witness can always be found. -/
theorem acyclic (state : State roles) (m : Assignment) (valid : Models state m)
 (origin : Origin) (tree : Tree) (can : Canonical tree) (known : At m .actual origin (value tree)) :
 ¬ Cyclic state origin := by
 rintro ⟨⟨next,edge,path⟩,_⟩
 obtain ⟨lower,lcan,lAt,strict⟩ := edge_descends state m valid _ _ _ can known edge
 obtain ⟨finish,fcan,fAt,small⟩ := path_descends state m valid path _ lcan lAt
 have same := height_invariant tree finish can fcan (at_agree m origin _ _ known fAt)
 omega

end Yulang.GeneralRebaseTreeAcyclic272
