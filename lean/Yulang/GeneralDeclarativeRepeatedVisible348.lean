import Yulang.GeneralDeclarativeTxnComplete348
import Yulang.GeneralDeclarativeRepeatedPlacement348

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 35000
set_option maxHeartbeats 46000000
namespace Yulang.GeneralDeclarativeRepeatedVisible348
open GeneralWhereVersionInstall317 (before fixed Models)
open GeneralWhereVersionSnapshot317 (context)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralLiveCompoundRegistry316 (sourceRegistry)
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralWhereVersionCase317 (site occ lower upper)
open GeneralDeclarativeRepeatedRows348 (low high loRow hiRow exact_at observes_lower observes_upper)
open GeneralDeclarativeTxnNormalized348 (Observed attach typed exact_support same_rhs)
open GeneralDeclarativeTxnComplete348 (Done)
open GeneralDeclarativeRepeatedTxn348 (checked)
open GeneralDeclarativeOrigins321 (Supported restriction Backed backed_iff)
open GeneralDeclarativeNamedProjection347 (base ordinary_holds)
open GeneralWhereOriginTrace318 (rawOf)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCommonBridge (Assignment)

abbrev done := Done sourceRegistry before context rootPlan

theorem silent : GeneralWhereOriginSuccessor318.SilentChildren rootPlan := by
  intro placed present
  rw [GeneralWhereVersionInstall317.fixture_emitted] at present
  cases List.mem_singleton.mp present
  rfl

theorem completed : done rootPlan.packet.site.occurrence.identity :=
  GeneralDeclarativeTxnComplete348.carry_by_literal checked silent
    (GeneralDeclarativeRepeatedTxn348.original_focus.symm ▸ GeneralDeclarativeCurrentBarrier345.ready.2)

theorem exact_rows (m : Assignment) (fit : Models fixed m) :
    Observed before fixed rootPlan low 0 site loRow ∧ Observed before fixed rootPlan high 0 site hiRow :=
  ⟨⟨(exact_at m fit).1,observes_lower⟩,⟨(exact_at m fit).2,observes_upper⟩⟩

/-- This checked former regression exports only current normalized
reads with authentic provenance. The archived site and the raw
compiler form remain separate evidence, not readonly aliases. -/
theorem current_source (m : Assignment) (fit : Models fixed m) :
    ∃ (a : Observed before fixed rootPlan low 0 site loRow) (b : Observed before fixed rootPlan high 0 site hiRow),
      let prior : Supported (base (rawOf fixed)) done := ⟨fun _ _ => False,False.elim⟩
      let lowSupport := attach prior a
      let withBoth := attach lowSupport b
      loRow ∈ (restriction withBoth).equations ∧ hiRow ∈ (restriction withBoth).equations ∧
      GeneralDeclarativeHead320.Models
        (appendFacts (appendFacts (base (rawOf fixed)) [loRow,GeneralDeclarativeWhereAttributed346.literal low])
          [hiRow,GeneralDeclarativeWhereAttributed346.literal high]) m := by
  obtain ⟨a,b⟩ := exact_rows m fit
  let prior : Supported (base (rawOf fixed)) done := ⟨fun _ _ => False,False.elim⟩
  let lo := attach prior a
  have lowKnown := (exact_support prior a (use := loRow)).mpr (.inr ⟨rfl,completed⟩)
  refine ⟨a,b,?_,?_,typed b m fit (typed a m fit (ordinary_holds _ m fit.1.1.1))⟩
  · exact (exact_support lo b).mpr (.inl ((backed_iff lo _).mp lowKnown))
  · exact (exact_support lo b).mpr (.inr ⟨rfl,completed⟩)

end Yulang.GeneralDeclarativeRepeatedVisible348
