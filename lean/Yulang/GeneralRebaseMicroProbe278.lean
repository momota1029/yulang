import Yulang.GeneralRebaseVersionKnown278
import Yulang.GeneralRebaseLooseKnown278
import Yulang.GeneralRebaseFamilyRank278

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseMicroProbe278
open GeneralRebaseFamilyDecode278 (Style Lane version_lower version_upper loose_lower loose_upper)
open GeneralRebaseFamilyRank278 (rank lower_exact upper_exact)
open GeneralRebaseRoundMicro278 (Tick)
open GeneralRebaseInstallTimeline278 (installedCount observedCount)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalState (Known)

inductive Answer where
  | lowerKnown (index : Nat) (known : Bool)
  | upperPatch (index : Nat) (compatible : Bool)
  deriving DecidableEq, Repr

def probe (kind : Style) (t : Tick) (name : Nat) : Option Answer :=
  match rank kind name with
  | some (.lower,i) => some (.lowerKnown i (decide (i < observedCount t)))
  | some (.upper,i) => some (.upperPatch i (decide (installedCount t ≤ i)))
  | none => none

theorem versionLower (t : Tick) (i : Nat) :
    ∃ b, probe .version239 t (GeneralDictionaryVersionLoopNames238.lower (i+1)) = some (.lowerKnown i b) ∧
      (b = true ↔ Known (GeneralRebaseVersionMicro278.raw t).core.erased.current.context.state
        (GeneralDictionaryVersionLoopNames238.lower (i+1))) := by
  let name := GeneralDictionaryVersionLoopNames238.lower (i+1)
  have found := (lower_exact .version239 name i).mpr (version_lower (i+1))
  refine ⟨decide (i < observedCount t),?_,?_⟩
  · unfold probe
    rw [found]
  · exact (decide_eq_true_iff).trans (GeneralRebaseVersionKnown278.prefix_known t i).symm

theorem looseLower (t : Tick) (i : Nat) :
    ∃ b, probe .loose240 t (GeneralDictionaryLooseFamilyNames240.lower (i+1)) = some (.lowerKnown i b) ∧
      (b = true ↔ Known (GeneralRebaseLooseMicro278.raw t).core.erased.current.context.state
        (GeneralDictionaryLooseFamilyNames240.lower (i+1))) := by
  let name := GeneralDictionaryLooseFamilyNames240.lower (i+1)
  have found := (lower_exact .loose240 name i).mpr (loose_lower (i+1))
  refine ⟨decide (i < observedCount t),?_,?_⟩
  · unfold probe
    rw [found]
  · exact (decide_eq_true_iff).trans (GeneralRebaseLooseKnown278.prefix_known t i).symm

theorem versionUpper (t : Tick) (i : Nat) :
    ∃ b, probe .version239 t (GeneralDictionaryVersionLoopNames238.upper i) = some (.upperPatch i b) ∧
      (b = true ↔ Models (GeneralRebaseVersionMicro278.raw t) (GeneralDictionaryVersionLoopFamilyNovel239.bad i)) := by
  let name := GeneralDictionaryVersionLoopNames238.upper i
  have found := (upper_exact .version239 name i).mpr (version_upper i)
  refine ⟨decide (installedCount t ≤ i),?_,?_⟩
  · unfold probe
    rw [found]
  · exact (decide_eq_true_iff).trans (GeneralRebaseInstallTimeline278.Version.patch_exact t i).symm

theorem looseUpper (t : Tick) (i : Nat) :
    ∃ b, probe .loose240 t (GeneralDictionaryLooseFamilyNames240.upper i) = some (.upperPatch i b) ∧
      (b = true ↔ Models (GeneralRebaseLooseMicro278.raw t) (GeneralDictionaryLooseFamilyNovel240.bad i)) := by
  let name := GeneralDictionaryLooseFamilyNames240.upper i
  have found := (upper_exact .loose240 name i).mpr (loose_upper i)
  refine ⟨decide (installedCount t ≤ i),?_,?_⟩
  · unfold probe
    rw [found]
  · exact (decide_eq_true_iff).trans (GeneralRebaseInstallTimeline278.Loose.patch_exact t i).symm

end Yulang.GeneralRebaseMicroProbe278
