import Yulang.GeneralRebasePackedSource298
import Yulang.GeneralRebaseRowOuterBoundary287

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebasePackedRowFixture298
open GeneralRebaseRowChildSource287 (before model)
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseRowChildRaw287 (ambient_boundary changeAmbient fullRow OutputCheck)
open GeneralRebaseQuestionFootprint298 (prior prior_exact)
open GeneralRebaseExecutableJournal298 (compile)
open GeneralRebasePackedAnswers298 (pack fill retain)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open Core.PresenceGeneration (CompTerm)

def old := compile before CompTerm.var
noncomputable def installed := compile (after true) CompTerm.var

theorem before_exact (a : Assignment) : old.Models a ↔ Models before a := by
  unfold old
  rw [GeneralRebaseExecutableJournal298.compile_exact]
  exact GeneralNominalRebaseJournalView243.compile_exact before ⟨rfl,rfl⟩ CompTerm.var a

theorem installed_exact (a : Assignment) : installed.Models a ↔ OutputCheck a := by
  unfold installed
  rw [GeneralRebaseExecutableJournal298.compile_exact]
  exact (GeneralNominalRebaseJournalView243.compile_exact (after true) ⟨rfl,rfl⟩ CompTerm.var a).trans
    (GeneralRebaseRowParentFrame287.after_exact true a)

theorem requires_row_zero : 0 ∈ (prior old).rows := by
  apply Classical.byContradiction
  intro missing
  let a := model Common.rowEmpty
  let b := changeAmbient a 0 fullRow
  have disagree : Models before a ∧ ¬ Models before b := ambient_boundary.2
  have sameRow (n : Nat) (inside : n ∈ (prior old).rows) : (a n).2 = (b n).2 := by
    have notZero : n ≠ 0 := fun h => missing (h ▸ inside)
    simp [b,changeAmbient,notZero]
  have same := prior_exact old a b ⟨fun _ _ => rfl,sameRow⟩
  exact disagree.2 ((before_exact b).mp (same.mp ((before_exact a).mpr disagree.1)))

theorem retained_after (a fallback : Assignment) :
    OutputCheck (fill (prior installed) (pack (prior installed) a) fallback) ↔ OutputCheck a :=
  (installed_exact _).symm.trans ((prior_exact installed _ _ (retain _ _ _)).trans (installed_exact _))

end Yulang.GeneralRebasePackedRowFixture298
