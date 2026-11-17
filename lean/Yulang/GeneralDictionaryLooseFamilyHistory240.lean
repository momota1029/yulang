import Yulang.GeneralDictionaryLooseFamilyInstallation240
/-! Finite historical input facts imply the complete aggregate-lower chain.
The plans use arbitrary per-stage bookkeeping, and the carrier assignment is
arbitrary. This is semantic readback from actual Inputs, not a claim that all
these facts have already been proved Trusted in an indexed reachable journal. -/
namespace Yulang.GeneralDictionaryLooseFamilyHistory240
open GeneralDictionaryLooseFamilyPacket240
open GeneralDictionaryLooseFamilyNames240
open GeneralDictionaryLooseLoopSource240 (F)
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)

theorem lower_step (n : Nat) (allocated reserved ordinary) (m : Assignment)
 (input : GeneralNominalVersionedPlans231.Inputs (plan n allocated reserved ordinary) m) :
 Equivalent (m (lower (n+1))).1 (m (lower n)).1 := by
 have merges := input.1.2.1
 have held : PresenceNormalForm.All CommonNominalFullCarrier.model m
   (GeneralNominalAllocation.equations (lower (n+1)) (.union (.var (lower n)) (.var (lower n)))) :=
   fun atom member => merges atom (GeneralDictionaryLooseFamilyInstallation240.lower_in_merges n allocated reserved ordinary member)
 have equation := (GeneralNominalCaptureMerges.equations_exact ..).mp held
 change Equivalent (m (lower (n+1))).1 (.union (m (lower n)).1 (m (lower n)).1) at equation
 have union : Equivalent (.union (m (lower n)).1 (m (lower n)).1) (m (lower n)).1 :=
   ⟨(common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩,
    (common_union_is_join _ _ _).mp (subtype_refl _) |>.1⟩
 exact ⟨subtype_trans equation.1 union.1,subtype_trans union.2 equation.2⟩

variable (allocations : Nat → List GeneralNominalIdentities.Origin)
 (reservations : Nat → List Nat) (atoms : Nat → List (PresenceNormalForm.Atom Nat))
def History (n : Nat) (m : Assignment) : Prop :=
 ∀ index < n, GeneralNominalVersionedPlans231.Inputs (plan index (allocations index) (reservations index) (atoms index)) m

theorem lower_chain (n : Nat) (m : Assignment)
 (source : GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot m)
 (history : History allocations reservations atoms n m) : Equivalent (m (lower n)).1 F := by
 induction n with
 | zero => exact GeneralDictionaryLooseLoopInitial240.foo_fixed m source
 | succ n ih =>
   have previous := ih (fun index before => history index (by omega))
   have next := lower_step n _ _ _ m (history n (by omega))
   exact ⟨subtype_trans next.1 previous.1,subtype_trans previous.2 next.2⟩

theorem every_lower (n : Nat) (m : Assignment)
 (source : GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot m)
 (history : History allocations reservations atoms n m) (index : Nat) (before : index ≤ n) :
 Equivalent (m (lower index)).1 F :=
 lower_chain allocations reservations atoms index m source (fun i earlier => history i (by omega))

open GeneralDictionaryLooseFamilyBase240 GeneralDictionaryLooseFamilySnapshot240

theorem base_models (n : Nat) (m : Assignment)
 (valid : GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot m) :
 GeneralNominalCommonBridge.Models (base n) m := by
 refine And.intro ?_ (And.intro (by intro _ _ h; cases h) (by intro _ h; cases h))
 change PresenceNormalForm.All CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment (base n) m)
   (GeneralDictionaryLooseLoopSource240.base.ordinary.map (PresenceNormalForm.Atom.rename (original n)))
 rw [PresenceNormalForm.all_rename]
 have same : GeneralNominalCommonBridge.assignment (base n) m ∘ original n =
   GeneralNominalCommonBridge.assignment GeneralDictionaryLooseLoopSource240.base m := by
   funext slot
   change ((m (source n (original n slot))).1,(m (source n (original n slot))).2) = ((m slot.val).1,(m slot.val).2)
   rw [source_original]
 rw [same]
 exact valid.1.1

theorem raw_models (n : Nat) (allocated reserved ordinary) (m : Assignment)
 (sourceValid : GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot m)
 (history : History allocations reservations atoms n m)
 (ordinaryValid : PresenceNormalForm.All CommonNominalFullCarrier.model m ordinary) :
 GeneralNominalState.Models (snapshot n allocated reserved ordinary) m := by
 refine ⟨base_models n m sourceValid,?_,ordinaryValid⟩
 intro slot descriptor found
 change (if slot.val=3 then some (GeneralDictionaryLooseFamilyBase240.pair n) else if slot.val=2 ∨ 4 ≤ slot.val then some (foo n) else none) = some descriptor at found
 split at found
 · rename_i three
   cases Option.some.inj found
   have anchorFits : GeneralNominalState.Fits (base n) m (.type (anchor n,original n 4)) (.inl F) := by
     change Subtype (m (source n (anchor n))).1 F ∧ Subtype F (m (source n (original n 4))).1
     rw [source_anchor,source_original]
     exact ⟨(lower_chain allocations reservations atoms n m sourceValid history).1, (GeneralDictionaryLooseLoopInitial240.foo4_fixed m sourceValid).2⟩
   refine ⟨[.inl F,.inl F],.cons anchorFits (.cons anchorFits .nil),?_⟩
   change Equivalent (m (source n slot)).1 GeneralDictionaryLooseLoopSource240.P
   rw [source_small slot (by omega),three]
   exact GeneralDictionaryLooseLoopInitial240.root_fixed m sourceValid
 · split at found
   · rename_i relevant
     cases Option.some.inj found
     have sourceFits : Equivalent (m (source n slot)).1 F := by
       rcases relevant with two | added
       · rw [source_small slot (by omega),two]
         exact GeneralDictionaryLooseLoopInitial240.foo_fixed m sourceValid
       · by_cases four : slot.val=4
         · rw [source_small slot (by omega),four]
           exact GeneralDictionaryLooseLoopInitial240.foo4_fixed m sourceValid
         · rw [source_large slot (by omega)]
           exact every_lower allocations reservations atoms n m sourceValid history (slot.val-4) (by have size : slot.val < n+5 := slot.isLt; omega)
     refine ⟨[.inl GeneralDictionaryLooseLoopSource240.S],.cons ?_ .nil,sourceFits⟩
     change Equivalent (m (source n (original n 0))).1 GeneralDictionaryLooseLoopSource240.S
     rw [source_original]
     exact GeneralDictionaryLooseLoopInitial240.scalar_fixed m sourceValid
   · cases found
end Yulang.GeneralDictionaryLooseFamilyHistory240
