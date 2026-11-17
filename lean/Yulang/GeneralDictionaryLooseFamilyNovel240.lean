import Yulang.GeneralDictionaryLooseFamilyFull240
import Yulang.GeneralNominalVersionedModelSupport237
set_option backward.isDefEq.respectTransparency false
/-! Uniform novelty from real semantic support, not allocation ownership.
The support and upper-exclusion hypotheses remain explicit until a producer
for the indexed operational journals supplies them. -/
namespace Yulang.GeneralDictionaryLooseFamilyNovel240
open GeneralDictionaryLooseLoopSource240
open GeneralDictionaryLooseFamilyPacket240
open GeneralDictionaryLooseFamilyNames240 (lower upper)
open GeneralDictionaryLooseLoopPacket240 (actual actual_value)
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedModelSupport237 (Support)
open CommonNominalFullCarrier
variable (n : Nat) (allocated : List GeneralNominalIdentities.Origin)
 (reserved : List Nat) (ordinary : List (PresenceNormalForm.Atom Nat))

noncomputable def bad : GeneralNominalCommonBridge.Assignment :=
 fun name => if name = upper n then (.bottom,(model name).2) else model name

theorem preserved (state : State roles) (supported : Support state names)
 (fresh : upper n ∉ names) (valid : Models state model) : Models state (bad n) := by
 apply (supported model (bad n) ?_).mp valid
 intro name member
 have different : name ≠ upper n := by intro equal; subst name; exact fresh member
 simp only [bad,different,ite_false]

theorem novel_from_bad (state : State roles) (valid : Models state (bad n)) :
 ¬ GeneralNominalVersionedKernel232.Committed state (plan n allocated reserved ordinary) := by
 intro committed
 have held := (committed.1 (bad n) valid).1
 have fits := GeneralNominalVersionedPlans231.shared_center held.2.1 (name := 0) (Or.inl (by change 0 ∈ declaration.inputNames; decide +kernel))
 rw [GeneralNominalVersionedFrame231.binder_eq,GeneralDictionaryLooseFamilyFull240.binder_exact] at fits
 change GeneralNominalCaptureMerges.Fits (bad n)
   ((GeneralNominalVersionedAllocation231.capture _ _ _ _ (packet n allocated reserved ordinary).bindings).inputs 0)
   (bad n actual).1 at fits
 rw [bindings_exact] at fits
 change Subtype (bad n (lower (n+1))).1 (bad n actual).1 ∧
   Subtype (bad n actual).1 (bad n (upper n)).1 at fits
 have ne : actual ≠ upper n := Ne.symm
   (GeneralNominalAggregateVersion231.not_legacy_slot 4 0 0 1 0 _ 0 0 8 0)
 have center : (bad n actual).1 = F := by simp only [bad,ne,ite_false,actual_value]
 have bound : (bad n (upper n)).1 = .bottom := by simp only [bad,ite_true]
 rw [center,bound] at fits
 exact GeneralNominalCenteredHeadMatHeadShape.bottom_no_head (.nominal 0 1)
   ⟨[.inl S],rfl,(by
     intro depth
     apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr
     intro rank env observation accepted
     exact CommonNominalFullDemand.probeAt_bottom rank observation),fits.2⟩
theorem novel (state : State roles) (supported : Support state names)
 (fresh : upper n ∉ names) (valid : Models state model) :
 ¬ GeneralNominalVersionedKernel232.Committed state (plan n allocated reserved ordinary) :=
 novel_from_bad n allocated reserved ordinary state (preserved n state supported fresh valid)
end Yulang.GeneralDictionaryLooseFamilyNovel240
