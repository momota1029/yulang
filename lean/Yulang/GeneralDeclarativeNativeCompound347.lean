import Yulang.GeneralDeclarativeNativeChild347
import Yulang.GeneralLiveCompoundCulprit316

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 30000000
namespace Yulang.GeneralDeclarativeNativeCompound347
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralLiveCompoundRegistry316 (registry initialState)
open GeneralLiveCompoundRoot316 (effect)
open GeneralLiveCompoundInstall316 (installed installable not_committed)
open GeneralLiveCompoundPoint316 (point)
open GeneralLiveCompoundLowerRefresh316 (refreshed)
open GeneralLiveCompoundUpperRefresh316 (upperState)
open GeneralLiveCompoundLeafInstall316 (after after_model reachable)
open GeneralLiveCompoundChildSite316 (childSite child emitted_eq)
open GeneralLiveCompoundLeafProof316 (w)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralStoppedInstallHistory335 (InstalledBetween)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalSaturationState (Generated)
open GeneralNominalVersionedChildren232 (emitted)
open GeneralDeclarativeWhereLegacyCut346 (sideCell)
open GeneralDeclarativeWhereRawAtoms346 (cell)
open GeneralDeclarativeNativeWhere347 (layout)
open GeneralNominalCenters (Site)
open B4Target (Steps)

theorem rest : Steps (Step registry root) installed after := by
  exact .tail (.tail (.tail (.tail .refl GeneralLiveCompoundPoint316.step)
    GeneralLiveCompoundLowerRefresh316.step) GeneralLiveCompoundUpperRefresh316.step)
    GeneralLiveCompoundLeafInstall316.step

theorem owner_install : InstalledBetween registry root initialState after effect :=
  ⟨initialState,.refl,.root,installable,not_committed,rest⟩

theorem exact_birth (m : GeneralNominalCommonBridge.Assignment) (fit : Models after m) :
    ∃ (before : GeneralNominalVersionedJournal232.State roles),
      after.core.sites[before.core.sites.length]? = some childSite ∧
      after.core.erased.current.sites[before.core.erased.current.sites.length]? = some childSite.observed ∧
      Generated after.core.erased.current root child ∧ childSite.Holds m := by
  have atBirth : (emitted effect.plan)[0]? = some childSite := by
    change (emitted GeneralLiveCompoundRoot316.plan)[0]? = _
    rw [emitted_eq]
    rfl
  obtain ⟨before,_,_,_,centered,observed,_,path,typed⟩ :=
    GeneralDeclarativeNativeChild347.current_positions owner_install atBirth m fit
  exact ⟨before,by simpa only [Nat.add_zero] using centered,
    by simpa only [Nat.add_zero] using observed,path,typed⟩

/-- Real native birth/child, still tied to its original ordered indices,
is compatible with *absence* of both currently desired corrected mode
addresses. Finding a current child is not a receipt for changing its
place or version of where input. -/
theorem old_positions_not_current_reads :
    after.core.sites[1]? = some childSite ∧
    after.core.erased.current.sites[1]? = some childSite.observed ∧
    after.core.erased.current.sites[1]?.map (fun s => s.inputs) =
      some [some (.source GeneralMixedCompoundChildEquality307.mid)] ∧
    childSite.Holds w ∧
    cell (layout after).base (sideCell .lower) = none ∧
    cell (layout after).base (sideCell .upper) = none := by
  have c : after.core.sites[1]? = some childSite := by rw [GeneralLiveCompoundPost316.centers_after]; rfl
  have r : after.core.erased.current.sites[1]? = some childSite.observed := by
    rw [GeneralLiveCompoundPost316.raw_sites_after]; rfl
  have loc : GeneralVersionedTraceDomain313.seed after = rootPlan.packet.context.state.seed :=
    congrArg (fun ctx : GeneralNominalCandidates.Context => ctx.state.seed)
      GeneralLiveCompoundPostRootHead316.frame.context_eq.symm
  obtain ⟨_,_,_,_,found⟩ := exact_birth w after_model
  refine ⟨c,r,?_,found,(GeneralDeclarativeNativeWhere347.no_compiled_cell reachable loc (sideCell .lower)).2.1,
    (GeneralDeclarativeNativeWhere347.no_compiled_cell reachable loc (sideCell .upper)).2.1⟩
  rw [r,Option.map_some,GeneralLiveCompoundChildSite316.raw_input]

end Yulang.GeneralDeclarativeNativeCompound347
