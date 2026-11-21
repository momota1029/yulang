import Yulang.GeneralWhereOriginReservation318

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 3500000
namespace Yulang.GeneralWhereOriginEnumerate318
open GeneralDeclarations (Clause)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalCenters (Plan)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralWhereOriginDelta318 (Cell)
open GeneralVersionedEndpointAddress315 (Side)

def isCompound (p : Pattern) : Bool :=
  match normalize p with
  | .var _ => false
  | _ => true

theorem compound_iff (p : Pattern) : isCompound p = true ↔ ∀ n, normalize p ≠ .var n := by
  unfold isCompound
  cases normalize p <;> simp

def slotCell (p : Plan rs) (c : Clause) (listed : c ∈ p.packet.declaration.requirements)
    (i : Nat) (side : Side) : Option (Cell p) :=
  match has : c.arguments[i]? with
  | none => none
  | some pattern =>
    if compound : isCompound pattern = true then
      match code : translate p.packet.registry.constructors p.packet.context.interpretation pattern with
      | none => none
      | some expression =>
        some ⟨c,i,side,pattern,expression,listed,has,(compound_iff pattern).mp compound,code⟩
    else none

def enumerate (p : Plan rs) : List (Cell p) :=
  p.packet.declaration.requirements.attach.flatMap fun c =>
    (List.range c.val.arguments.length).flatMap fun i =>
      (slotCell p c.val c.property i .lower).toList ++ (slotCell p c.val c.property i .upper).toList

theorem slot_exact {p : Plan rs} (c : Cell p) :
    slotCell p c.clause c.listed c.index c.side = some c := by
  cases c with
  | mk clause index side pattern expression listed found good translated =>
    unfold slotCell
    split
    · rename_i missing
      rw [found] at missing
      cases missing
    · rename_i pat hit
      have same := Option.some.inj (found.symm.trans hit)
      subst pat
      rw [dite_eq_left ((compound_iff pattern).mpr good)]
      split
      · rename_i failed
        rw [translated] at failed
        cases failed
      · rename_i code goodCode
        have same := Option.some.inj (translated.symm.trans goodCode)
        subst code
        rfl

theorem includes {p : Plan rs} (c : Cell p) : c ∈ enumerate p := by
  apply List.mem_flatMap.mpr
  refine ⟨⟨c.clause,c.listed⟩,by simp,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨c.index,List.mem_range.mpr (List.getElem?_eq_some_iff.mp c.located).1,?_⟩
  have yes := slot_exact c
  cases h : c.side
  · rw [h] at yes
    exact List.mem_append_left _ (Option.mem_toList.mpr yes)
  · rw [h] at yes
    exact List.mem_append_right _ (Option.mem_toList.mpr yes)

end Yulang.GeneralWhereOriginEnumerate318
