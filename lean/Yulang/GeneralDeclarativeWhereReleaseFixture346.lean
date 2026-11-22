import Yulang.GeneralDeclarativeWhereRelease346
import Yulang.GeneralDeclarativeWhereCurrent346

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 17000000
namespace Yulang.GeneralDeclarativeWhereReleaseFixture346
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralWhereOriginSingleSource318 (sourceRegistry oldPlan)
open GeneralWhereOriginSingleModel318 (previousLo)
open GeneralWherePhysicalOldHead319 (before)
open GeneralWherePhysicalOldInstall319 (installed)
open GeneralWherePhysicalReobserve319 (updated)
open GeneralWherePhysicalCurrentRead319 (plan low)
open GeneralWherePhysicalCommit319 (final physical_mixed_run)
open GeneralDeclarativeWhereRelease346 (Released attach archived_excluded with_release)
open GeneralDeclarativeWhereAttributed346 (literal model_exact)
open GeneralDeclarativeWhereEndpoint346 (At)
open GeneralDeclarativeOrigins321 (Supported Backed restriction)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeEntailment320 (Holds)
open GeneralDeclarativeSubstitution320 (EquationRead)
open GeneralDeclarativeRawCapture344 (rawCap)
open GeneralNominalCommonBridge (Assignment)

def blank : State := ⟨⟨[],[]⟩,[]⟩
def origin : Supported blank (fun _ => True) :=
  ⟨fun _ _ => False,False.elim⟩

/-- Test-only release selection: pick the known current fixture event,
not every historical write by its owner. It is not a language policy. -/
def currentOnly : Released roles := fun _ stamp physical _ _ => stamp = 1 ∧ physical = 2

private theorem singleton_index {xs : List α} {x y : α} {i : Nat}
    (shape : xs = [x]) (same : xs[i]? = some y) : i = 0 ∧ y = x := by
  subst xs
  cases i with
  | zero => exact ⟨rfl,(Option.some.inj same).symm⟩
  | succ i => simp at same

theorem same_owner : oldPlan.packet.site.occurrence.identity = plan.packet.site.occurrence.identity := rfl

theorem observed :
    ∃ (m : Assignment) (site : GeneralNominalCenters.Site roles) (liveSite : GeneralNominalCenters.Site roles)
      (old : At before installed oldPlan previousLo 0 site)
      (now : At updated final plan low 0 liveSite),
      Holds m (literal previousLo) ∧ Holds m (literal low) ∧
      literal previousLo ∉ (restriction (attach origin old currentOnly)).equations ∧
      EquationRead (restriction (attach origin now currentOnly)) (rawCap plan) low.side.mode low.row.target low.expression := by
  obtain ⟨s₀,_,s₁,fitOld,_,fitNew,_,_⟩ := physical_mixed_run
  obtain ⟨i,oldSite,old,truthOld⟩ := GeneralDeclarativeWhereEndpoint346.from_step s₀ previousLo _ fitOld
  obtain ⟨j,liveSite,now,truthNew⟩ := GeneralDeclarativeWhereEndpoint346.from_step s₁ low _ fitNew
  have i0 := (singleton_index GeneralWherePhysicalCurrentPick319.old_emitted old.emittedHere).1
  have j0 := (singleton_index GeneralWherePhysicalCommit319.emission now.emittedHere).1
  subst i; subst j
  refine ⟨_,oldSite,liveSite,old,now,(model_exact previousLo _).mpr truthOld,(model_exact low _).mpr truthNew,?_,?_⟩
  · apply archived_excluded origin old
    · rintro ⟨_,notBacked,_⟩; exact notBacked
    · intro outdated; exact Nat.noConfusion outdated.1
  · exact with_release origin now trivial ⟨rfl,by rw [GeneralWherePhysicalCurrentPick319.centers]; rfl⟩

end Yulang.GeneralDeclarativeWhereReleaseFixture346
