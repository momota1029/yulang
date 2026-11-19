import Yulang.GeneralRebaseCompoundChildBoundary273

namespace Yulang.GeneralRebaseCompoundOwnerBlock273
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalAllocation (Bindings)

inductive Slot where
 | captureLo | captureHi | childLo | childHi | childCenter
 deriving DecidableEq, Repr

abbrev PublicSlot := Fin 5

structure Block where
 lo : PublicSlot
 hi : PublicSlot
 center : PublicSlot
 deriving DecidableEq, Repr

def loBind : Bindings := [(0,4,2),(0,4,2)]
def pointBind : Bindings := [(0,2,2),(0,2,2)]

/-- Only duplicated type endpoints are supported here. The actual center
source is a separately justified input, not inferred from the upper. -/
def compile (bindings : Bindings) (actual : PublicSlot) : Option Block :=
 match bindings with
 | [(name,a,b),(other,c,d)] =>
   if name = 0 ∧ other = name ∧ a = c ∧ b = d then
      if lower : a < 5 then
         if upper : b < 5 then some ⟨⟨a,lower⟩,⟨b,upper⟩,actual⟩ else none
      else none
   else none
 | _ => none

def loose : Block := ⟨4,2,2⟩
def point : Block := ⟨2,2,2⟩

theorem actual_loose :
 compile GeneralDictionaryCompoundPacket238.packet.bindings 2 = some loose := by
 rw [GeneralDictionaryCompoundPacket238.bindings_exact]
 rfl

theorem actual_point :
 compile GeneralDictionaryCompoundObstruction238.currentPlan.packet.bindings 2 = some point := by
 rw [GeneralDictionaryCompoundCurrent238.bindings_exact]
 rfl

def read (block : Block) : Slot → PublicSlot
 | .captureLo | .childLo => block.lo
 | .captureHi | .childHi => block.hi
 | .childCenter => block.center

def eval (boundary : Assignment) (block : Block) : Slot → Ty
 | .captureLo => (boundary block.lo.val).1
 | .captureHi => (boundary block.hi.val).1
 | .childLo => variant 0 (boundary block.lo.val).1
 | .childHi => variant 0 (boundary block.hi.val).1
 | .childCenter => variant 0 (boundary block.center.val).1

theorem normalized_lo (t : Ty) : Equivalent (.union t t) t :=
 ⟨(common_union_is_join ..).mpr ⟨subtype_refl _,subtype_refl _⟩,
  ((common_union_is_join ..).mp (subtype_refl (.union t t))).1⟩

theorem normalized_hi (t : Ty) : Equivalent (.inter t t) t :=
 ⟨((common_inter_is_meet ..).mp (subtype_refl (.inter t t))).1,
  (common_inter_is_meet ..).mpr ⟨subtype_refl _,subtype_refl _⟩⟩

theorem eval_agree (block : Block) (first last : Assignment)
 (same : GeneralRebaseCompoundPublic273.AgreesTypes first last) (slot : Slot) :
 eval first block slot = eval last block slot := by
 cases slot
 · exact same _ (Nat.le_of_lt_succ block.lo.isLt)
 · exact same _ (Nat.le_of_lt_succ block.hi.isLt)
 · exact congrArg (variant 0) (same _ (Nat.le_of_lt_succ block.lo.isLt))
 · exact congrArg (variant 0) (same _ (Nat.le_of_lt_succ block.hi.isLt))
 · exact congrArg (variant 0) (same _ (Nat.le_of_lt_succ block.center.isLt))

theorem compiler_exact (bindings : Bindings) (input : PublicSlot) (block : Block)
 (found : compile bindings input = some block) :
 bindings = [(0,block.lo.val,block.hi.val),(0,block.lo.val,block.hi.val)] ∧ block.center = input := by
 unfold compile at found
 split at found
 · rename_i name a b other c d
   split at found
   · rename_i ok
     split at found
     · split at found
       · cases Option.some.inj found
         rcases ok with ⟨rfl,rfl,rfl,rfl⟩
         exact ⟨rfl,rfl⟩
       · contradiction
     · contradiction
   · contradiction
 · contradiction

end Yulang.GeneralRebaseCompoundOwnerBlock273
