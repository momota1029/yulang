import Yulang.GeneralDeclarativeCurrentTrace345
import Yulang.GeneralSharedNamedMerge310

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 23000
set_option maxHeartbeats 13000000
namespace Yulang.GeneralDeclarativeCurrentDuplicate345
open GeneralSharedNamedPlan310 (loSite hiSite z)
open GeneralSharedNamedInstall310 (after raw_sites)
open GeneralSharedNamedMerge310 (merged aliases root_not_alias_child)
open GeneralSharedNamedEvidence310 (alias_identity siblings_different)
open GeneralSharedNamedLeaf310 (named_requests)
open GeneralDeclarativeCurrentOrder345 (Row rows outputs)
open GeneralNominalSaturationState (Alias)

abbrev leftRow : Row := ⟨1,0,⟨1,z⟩⟩
abbrev rightRow : Row := ⟨2,0,⟨1,z⟩⟩

private theorem after_sites : merged.core.erased.current.sites = after.core.erased.current.sites := rfl

theorem exact_before : rows after.core loSite.occurrence = [leftRow] := by
  classical
  unfold rows
  rw [raw_sites]
  have yes : Alias after.core.erased.current loSite.occurrence.identity loSite.observed.occurrence.identity := .refl _
  have noPeer : ¬ Alias after.core.erased.current loSite.occurrence.identity hiSite.observed.occurrence.identity :=
    fun h => siblings_different (alias_identity h)
  have noRoot : ¬ Alias after.core.erased.current loSite.occurrence.identity
      (GeneralNominalDemandMerging.pointSite GeneralSharedNamedSource310.root).occurrence.identity :=
    fun h => GeneralSharedNamedLeafFrame310.invocations .low (alias_identity h)
  simp [List.zipIdx_cons,yes,noPeer,noRoot,
    show loSite.observed.occurrence.demand.outputs = [⟨1,z⟩] from named_requests .low]

theorem exact_after : rows merged.core loSite.occurrence = [leftRow,rightRow] := by
  classical
  unfold rows
  rw [after_sites,raw_sites]
  have yes : Alias merged.core.erased.current loSite.occurrence.identity loSite.observed.occurrence.identity := .refl _
  have yesPeer : Alias merged.core.erased.current loSite.occurrence.identity hiSite.observed.occurrence.identity :=
    .edge List.mem_cons_self
  have noRoot : ¬ Alias merged.core.erased.current loSite.occurrence.identity
      (GeneralNominalDemandMerging.pointSite GeneralSharedNamedSource310.root).occurrence.identity :=
    fun h => GeneralSharedNamedLeafFrame310.invocations .low (root_not_alias_child h.symm)
  simp [List.zipIdx_cons,yes,yesPeer,noRoot,
    show loSite.observed.occurrence.demand.outputs = [⟨1,z⟩] from named_requests .low,
    show hiSite.observed.occurrence.demand.outputs = [⟨1,z⟩] from named_requests .high]

theorem no_dedup :
    GeneralNominalCenteredHeadOutputs.requests merged.core loSite.occurrence = [⟨1,z⟩,⟨1,z⟩] := by
  rw [← outputs,exact_after]
  rfl

end Yulang.GeneralDeclarativeCurrentDuplicate345
