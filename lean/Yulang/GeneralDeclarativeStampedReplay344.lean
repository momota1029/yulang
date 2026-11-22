import Yulang.GeneralDeclarativePhysicalReplay344

namespace Yulang.GeneralDeclarativeStampedReplay344
open GeneralNominalCenters (Plan Site)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarations (Registry)
open GeneralWhereVersionInstall317 (Journal Models InstallStep install emitted)
open GeneralWhereVersionCompiler317 (children child)
open GeneralDeclarativeCommitSuffix344 (Receipt from_step child_at)
open GeneralDeclarativeCommitPosition344 (clauses signature current_stamp source_at)
open GeneralDeclarativeLedger344 (Grows stamped site_kept later_model)
open GeneralWhereVersionSemantics317 (Holds)
open GeneralWhereOriginSupport318 (journalSources)

/-- Existence here comes from the true feasible step premise itself,
not by fabricating a new model for a stale plan. -/
theorem feasible {r : Registry} {before after : Journal rs}
    (step : InstallStep r before after) :
    ∃ ctx p m, after = install before ctx p ∧ Models before m ∧ Models after m ∧
      Receipt r before after p m := by
  cases step with
  | whereRow ctx p checked frame selected compatible refined interpretation fit =>
    obtain ⟨m,pre,post⟩ := fit
    have taken : InstallStep r before (install before ctx p) :=
      .whereRow ctx p checked frame selected compatible refined interpretation ⟨m,pre,post⟩
    exact ⟨ctx,p,m,rfl,pre,post,current_stamp r before ctx p taken m post⟩

/-- A previously committed ordinal can be re-read at a later
append-preserving snapshot. The caller must give the ordinal and its
literal site, and the conclusion is historical evidence, not
permission to substitute the old input at a currently queried site. -/
theorem later_position {r : Registry} {before after later : Journal rs}
    {p : Plan rs} {m : Assignment} (taken : Receipt r before after p m)
    (growth : Grows after later) {i : Nat} {site : Site rs}
    (atBirth : (emitted p)[i]? = some site) (n : Assignment) (fit : Models later n) :
    later.versionedWhere[before.versionedWhere.length]? = some p ∧
      later.mixed.core.sites[before.mixed.core.sites.length+i]? = some site ∧
      (children p)[i]? = some site.occurrence ∧
      Holds p n ∧ GeneralNominalVersionedEffects231.ClassEffects later.mixed.core p.packet.site.occurrence p n := by
  have pos := child_at taken atBirth
  exact ⟨stamped growth taken.stamp,site_kept growth pos.1,pos.2,later_model growth taken.stamp n fit⟩

theorem later_from_step {r : Registry} {before after later : Journal rs}
    (step : InstallStep r before after) (growth : Grows after later)
    (n : Assignment) (fit : Models later n) :
    ∃ ctx p, after = install before ctx p ∧
      later.versionedWhere[before.versionedWhere.length]? = some p ∧ Holds p n ∧
      ∀ i site, (emitted p)[i]? = some site →
        later.mixed.core.sites[before.mixed.core.sites.length+i]? = some site ∧
        (children p)[i]? = some site.occurrence := by
  obtain ⟨ctx,p,m,exactAfter,_,_,taken⟩ := feasible step
  refine ⟨ctx,p,exactAfter,stamped growth taken.stamp,
    (later_model growth taken.stamp n fit).1,?_⟩
  intro i site h
  have exported := later_position taken growth h n fit
  exact ⟨exported.2.1,exported.2.2.1⟩

end Yulang.GeneralDeclarativeStampedReplay344
