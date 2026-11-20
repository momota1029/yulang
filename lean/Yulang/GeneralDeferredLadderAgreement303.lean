import Yulang.GeneralDeferredLadderCount303
import Yulang.GeneralDeferredLadderUniversalLeaf302

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderAgreement303
open GeneralDeferredLadderAfterVariants302 (variantOwned)
open GeneralDeferredLadderOutcomes302 (terminal schedule)
open GeneralDeferredLadderCount303 (suffix_readback)
open GeneralDeferredLadderExact302 (RawStep Promotion)
open GeneralDeferredLadderRetargetFrames302 (endUnseen)
open GeneralObservedLadderBudget301 (Counted)
open GeneralObservedLadderJournalCompiler301 (table)
open GeneralObservedLadderEvidence301 (dictionary)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalExamples (registry displayRoot)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)

abbrev Readback (s : State roles) (n : Nat) :=
  GeneralGeneratedDictionaryRun299.run (table s) (n+2) 0

theorem supported_terminal_agreement (n k : Nat) (cap : k ≤ n+1) (extra : Nat)
    {count : Nat} {early late : State roles}
    (prePath : Counted count (variantOwned n k cap extra).state early)
    (halt : ∀ s, ¬ RawStep early s)
    (promoted : Promotion n (endUnseen n).state late) :
    count = n+1-k ∧
    Readback early n = Readback late n ∧
    Readback early n = some (dictionary (n+1)) ∧
    (∀ next, ¬ RawStep late next) ∧
    (∀ m : Assignment, Models early m → (boundary roles).Evidence registry early m displayRoot (dictionary (n+1))) ∧
    (∀ m : Assignment, Models late m → (boundary roles).Evidence registry late m displayRoot (dictionary (n+1))) := by
  obtain ⟨countEq,computed,evidence⟩ := suffix_readback (variantOwned n k cap extra) cap prePath halt
  obtain ⟨noMore,readback,evidenceLate⟩ :=
    GeneralDeferredLadderUniversalLeaf302.every_delayed_promotion_completes n late promoted
  have earlyRead : Readback early n = some (dictionary (n+1)) := by
    rw [Readback,computed]
    exact ite_eq_left (by omega)
  exact ⟨countEq,earlyRead.trans readback.symm,earlyRead,noMore,evidence,evidenceLate⟩

end Yulang.GeneralDeferredLadderAgreement303
