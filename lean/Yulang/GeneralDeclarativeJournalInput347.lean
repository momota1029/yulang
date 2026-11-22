import Yulang.GeneralDeclarativeJournalFixture347
import Yulang.GeneralDeclarativeNamedProjection347
import Yulang.GeneralDeclarativeJournalPrefix347
import Yulang.GeneralDeclarativeWhereNamedSource346

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32000
set_option maxHeartbeats 27000000
namespace Yulang.GeneralDeclarativeJournalInput347
open GeneralWhereVersionInstall317 (Models)
open GeneralWherePhysicalCommit319 (final newChild step)
open GeneralWherePhysicalReobserve319 (updated)
open GeneralWherePhysicalCurrentRead319 (plan low high)
open GeneralWhereOriginSingleSource318 (oldPlan)
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralWhereOriginTrace318 (rawOf)
open GeneralWhereOriginDelta318 (Cell)
open GeneralDeclarativeWhereEndpoint346 (At)
open GeneralDeclarativeWhereReuse346 (SameAuthor)
open GeneralDeclarativeJournalRelease347 (release read_after_done)
open GeneralDeclarativeJournalFixture347 (lower_observed upper_observed released_both)
open GeneralDeclarativeCurrentOrigins343 (done completed)
open GeneralDeclarativeWhereAttributed346 (literal)
open GeneralDeclarativeSubstitution320 (EquationRead)
open GeneralDeclarativeRawCapture344 (rawCap)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedPlans231 (variables)
open GeneralDeclarativeNamedProjection347 (base ordinary_holds)

/-- Positive fixture: start with an ordinary exact named view of the
very same raw model, then add both literal current inputs with their
own actual observed-at-current commit receipts. The old upper row
retains its *separate* author in the installation history. -/
theorem current_uses_real_receipts (m : Assignment) (fit : Models final m) :
    ∃ (ord : Nat) (kid : GeneralNominalCenters.Site _)
      (lo : At updated final plan low ord kid) (hi : At updated final plan high ord kid),
      let start : Supported (base (rawOf final)) done := ⟨fun _ _ => False,False.elim⟩
      let withLo := GeneralDeclarativeWhereRelease346.attach start lo (release final)
      let withBoth := GeneralDeclarativeWhereRelease346.attach withLo hi (release final)
      EquationRead (restriction withBoth) (rawCap plan) .lower low.row.target low.expression ∧
      EquationRead (restriction withBoth) (rawCap plan) .upper high.row.target high.expression ∧
      GeneralDeclarativeHead320.Models
        (GeneralDeclarativeEntailment320.appendFacts
          (GeneralDeclarativeEntailment320.appendFacts (base (rawOf final)) [literal low]) [literal high]) m ∧
      ∃ prior : Cell oldPlan, updated.versionedWhere[0]? = some oldPlan ∧
        prior.row.target = high.row.target ∧ SameAuthor high prior ∧
        prior.row.Holds (variables oldPlan m) m := by
  obtain ⟨ord,site,_,_,_,_,_,_,lo,hi,_,_⟩ := GeneralDeclarativeWhereBoth346.paired step low m fit
  have doneRoot : done plan.packet.site.occurrence.identity := completed
  let start : Supported (base (rawOf final)) done := ⟨fun _ _ => False,False.elim⟩
  let withLo := GeneralDeclarativeWhereRelease346.attach start lo (release final)
  have past : Models updated m := GeneralDeclarativeJournalPrefix347.previous GeneralWherePhysicalActive319.refines m fit
  have old := GeneralDeclarativeWhereCurrent346.old_upper m past
  obtain ⟨prior,stamp,matched,_,author,typed,_⟩ := old
  refine ⟨ord,site,lo,hi,?_,?_,?_,prior,stamp,matched,author,typed⟩
  · apply EquationRead.whole
    apply (GeneralDeclarativeWhereRelease346.backed withLo hi (release final)).mpr
    apply Or.inl
    exact (GeneralDeclarativeOrigins321.backed_iff withLo _).mp
      ((GeneralDeclarativeWhereRelease346.backed start lo (release final)).mpr (Or.inr
        ⟨rfl,doneRoot,GeneralDeclarativeJournalRelease347.actual_release lo lower_observed⟩))
  · exact read_after_done withLo hi upper_observed doneRoot
  · have x := GeneralDeclarativeObservedSyntax347.structural_sound lower_observed m fit.1.1.1
    have y := GeneralDeclarativeObservedSyntax347.structural_sound upper_observed m fit.1.1.1
    apply (GeneralDeclarativeEntailment320.model_append m).mpr
    refine ⟨(GeneralDeclarativeEntailment320.model_append m).mpr
      ⟨ordinary_holds _ m fit.1.1.1,?_⟩,?_⟩
    · intro row found; cases List.mem_singleton.mp found; exact x
    · intro row found; cases List.mem_singleton.mp found; exact y

end Yulang.GeneralDeclarativeJournalInput347
