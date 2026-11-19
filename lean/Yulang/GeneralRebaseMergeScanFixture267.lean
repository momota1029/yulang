import Yulang.GeneralRebaseMergeScan267
import Yulang.GeneralRebaseMergeRegression264

set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
namespace Yulang.GeneralRebaseMergeScanFixture267
open GeneralNominalCenteredHeadAllocMergeSource (root registry roles)
open GeneralNominalCenteredHeadAllocMergeInstall (installed aSite bSite)
open GeneralNominalCenteredHeadAllocMergeState (installed_sites generated_a not_aliased)
open GeneralRebaseMergeRegression264 (sample merged owners pool projection_changed)
open GeneralRebaseMergeScan267 (scan scan_exact linkedPairs_exact)
open GeneralNominalCenters (Site)

def noProbe (_ _ : Site roles) : Bool := false

theorem listed : (aSite,bSite) ∈ scan sample root noProbe := by
 refine (scan_exact ..).mpr ⟨(linkedPairs_exact ..).mpr ⟨?_,?_,generated_a,not_aliased⟩,Or.inl ?_⟩
 · change aSite ∈ installed.core.sites
   rw [installed_sites]
   simp
 · change bSite ∈ installed.core.sites
   rw [installed_sites]
   simp
 · decide +kernel

/-- No input-equality oracle was needed for this actual strict merge. The
stress journal is explicit and the extra plan's reachability is not claimed. -/
theorem recovered_strict :
 GeneralNominalVersionedMixedKernel234.Step registry root sample merged ∧
 GeneralRebaseLiveProjection264.project owners pool merged ≠ GeneralRebaseLiveProjection264.project owners pool sample :=
 ⟨GeneralRebaseMergeScan267.source_step registry sample root noProbe aSite bSite listed
   (fun h => by cases h),projection_changed⟩

end Yulang.GeneralRebaseMergeScanFixture267
