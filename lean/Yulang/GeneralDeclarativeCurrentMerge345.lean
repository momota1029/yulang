import Yulang.GeneralDeclarativeCurrentSnapshot345
import Yulang.GeneralRebaseMergeRequests264

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCurrentMerge345
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedAdministrative232 (merge)
open GeneralNominalVersionedMixedKernel234 (Step At)
open GeneralNominalSaturationState (Alias Generated)
open GeneralNominalVersionedMixedGrowth234 (step)
open GeneralNominalCenteredHeadOutputs (requests mem_requests_iff)
open GeneralDeclarativeCurrentOrder345 (Row rows exact_row)

theorem retained {before : State rs} {first last : Site rs} {focus : Occurrence rs} :
    rows before.core focus ⊆ rows (merge before first last).core focus := by
  intro row h
  obtain ⟨site,siteAt,outAt,alias⟩ := exact_row.mp h
  exact exact_row.mpr ⟨site,siteAt,outAt,
    (GeneralRebaseMergeRequests264.alias_merge before first last _ _).mpr (.inl alias)⟩

theorem peer {before : State rs} {first last : Site rs} {row : Row}
    (siteAt : before.core.erased.current.sites[row.physical]? = some last.observed)
    (outAt : last.occurrence.demand.outputs[row.ordinal]? = some row.output) :
    row ∈ rows (merge before first last).core first.occurrence := by
  apply exact_row.mpr
  exact ⟨last.observed,siteAt,outAt,.edge (List.mem_cons_self ..)⟩

/-- A genuine mixed step can enlarge the class, without replacing a
contributing physical row or modifying the original birth descriptor. -/
theorem actual_peer {r : Registry} {before : State rs} {root : Occurrence rs}
    {first last : Site rs} {row : Row}
    (live : Generated before.core.erased.current root first.occurrence)
    (one : first ∈ before.core.sites) (two : last ∈ before.core.sites)
    (same : SameInputs (Models before) first last)
    (new : ¬ Alias before.core.erased.current first.occurrence.identity last.occurrence.identity)
    (siteAt : before.core.erased.current.sites[row.physical]? = some last.observed)
    (outAt : last.occurrence.demand.outputs[row.ordinal]? = some row.output)
    (different : row.output ∉ first.occurrence.demand.outputs) :
    Step r root before (merge before first last) ∧
    row ∈ rows (merge before first last).core first.occurrence ∧
    row ∉ rows before.core first.occurrence ∧
    row.output ∉ first.occurrence.demand.outputs := by
  refine ⟨⟨_,live,.merge first last one two same new⟩,peer siteAt outAt,?_,different⟩
  intro h
  obtain ⟨recorded,sameSite,_,linked⟩ := exact_row.mp h
  rw [siteAt] at sameSite
  have identified : last.observed = recorded := Option.some.inj sameSite
  subst recorded
  exact new linked

end Yulang.GeneralDeclarativeCurrentMerge345
