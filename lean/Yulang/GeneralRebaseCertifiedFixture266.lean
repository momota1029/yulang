import Yulang.GeneralRebaseCertifiedObserver266
import Yulang.GeneralRebaseSourceStrictFixture265

namespace Yulang.GeneralRebaseCertifiedFixture266
open GeneralRebaseSourceStrictFixture265
open GeneralRebaseStep258
open GeneralDictionaryCompoundFrame238 (before installed)
open GeneralDictionaryCompoundSource238 (sourceRegistry)
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralRebaseCertifiedObserver266 (Edge)
open GeneralRebaseScheduler259 (next scan)

abbrev registry := GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry

noncomputable def realEdge : Edge registry root :=
 ⟨before,installed,source_and_finite.1⟩

noncomputable def observe := GeneralRebaseCertifiedObserver266.observe owners pool [realEdge]

theorem initial_observation : observe first = [present last] := by
 have selected : GeneralRebaseCertifiedObserver266.chosen owners pool first realEdge = true :=
   (GeneralRebaseCertifiedObserver266.chosen_exact _ _ _ _).mpr ⟨rfl,strict⟩
 unfold observe GeneralRebaseCertifiedObserver266.observe
 simp only [List.filter_cons,selected,ite_true,List.filter_nil,List.map_cons,List.map_nil]
 rfl

theorem final_observation : observe last = [] := by
 have omitted : GeneralRebaseCertifiedObserver266.chosen owners pool last realEdge = false := by
   cases result : GeneralRebaseCertifiedObserver266.chosen owners pool last realEdge with
   | false => rfl
   | true =>
     have impossible := (GeneralRebaseCertifiedObserver266.chosen_exact _ _ _ _).mp result
     exact False.elim (strict impossible.1.symm)
 unfold observe GeneralRebaseCertifiedObserver266.observe
 simp only [List.filter_cons,omitted,Bool.false_eq_true,ite_false,List.filter_nil,List.map_nil]

theorem next_initial : next observe first = .ok (some last) := by
 rw [next,initial_observation]
 have covered : present last ⊆ GeneralRebaseUniversalBasis263.basis owners pool :=
   fun fact member => ((GeneralRebaseFactSemantics259.present_iff _ fact).mp member).1
 have exactWrite : write first (present last) = last :=
   GeneralRebaseProjectionObserver266.witness_write owners pool
     (⟨before,installed,source_and_finite.1,rfl,rfl⟩ :
       GeneralRebaseProjectionObserver266.Witness owners pool registry root first last)
 have committed : GeneralRebaseCheckedWrite259.commit first (present last) = .ok (some last) := by
   apply (GeneralRebaseCheckedWrite259.accepted ..).mpr
   exact ⟨covered,(tryWrite_exact ..).mpr
      ⟨exactWrite.symm,fun same => strict (state_ext _ _ same)⟩⟩
 simp only [scan,committed]

theorem next_final : next observe last = .ok none := by
 rw [next,final_observation]
 rfl

/-- The runner settles this supplied singleton of an actual guarded source
edge in one strict projected write, not by assuming a fixed table of facts. -/
theorem settles : GeneralRebaseSettle259.settle observe first = .ok last := by
 have settledLast : GeneralRebaseSettle259.settle observe last = .ok last := by
   rw [GeneralRebaseSettle259.settle,next_final]
 rw [GeneralRebaseSettle259.settle,next_initial]
 exact settledLast

theorem one_run : GeneralRebaseBudget258.Runs observe 1 first last :=
 .next (GeneralRebaseScheduler259.next_step observe first last next_initial) (.nil _)

end Yulang.GeneralRebaseCertifiedFixture266
