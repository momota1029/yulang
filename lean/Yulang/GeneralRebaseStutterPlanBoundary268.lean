import Yulang.GeneralRebaseEnumeratePlans267
import Yulang.GeneralRebaseSourceSurvivor267
import Yulang.GeneralRebaseSourceProjection264
import Yulang.GeneralDictionaryVersionLoopSecondStep238

set_option maxRecDepth 8192
namespace Yulang.GeneralRebaseStutterPlanBoundary268
open GeneralDictionaryVersionLoopSource237 (sourceRegistry registry root roles)
open GeneralDictionaryVersionLoopFrame237 (installed)
open GeneralDictionaryVersionLoopRetarget237 (refreshed retargeted revision)
open GeneralDictionaryVersionLoopPacket237 (lo)
open GeneralDictionaryVersionLoopSecondFrame238 (effect)
open GeneralDeclarationPatterns
open GeneralRebaseSourceSurvivor267 (Boundary declChecked)
open GeneralRebaseEnumeratePlans267 (plans plans_exact includes_install)
open GeneralRebaseLiveProjection264 (project)

theorem rootChecked : (Boundary roles).Checked sourceRegistry := ⟨rfl,GeneralDictionaryVersionLoopSource237.checked⟩

theorem retargeted_knows : GeneralNominalState.Known retargeted.core.erased.current.context.state lo :=
 ⟨(4 : Fin 5),rfl,Or.inr ⟨GeneralDictionaryVersionLoopRetarget237.exactFoo,rfl⟩⟩

theorem contexts_differ : installed.core.erased.current.context ≠ retargeted.core.erased.current.context := by
 intro same
 have present := retargeted_knows
 rw [←same] at present
 exact GeneralDictionaryVersionLoopRefresh237.lower_unknown present

theorem same_projection (owners : List Nat) (pool : List GeneralSourceState.Output) :
 project owners pool installed = project owners pool retargeted :=
 (GeneralRebaseSourceProjection264.refresh_stutters owners pool installed
    GeneralDictionaryVersionLoopRefreshBase237.extendedContext).trans
   (GeneralRebaseSourceProjection264.reobserve_stutters owners pool refreshed revision)

theorem discovered_after : effect.plan ∈ plans registry retargeted root (declChecked rootChecked) :=
 includes_install registry retargeted root (declChecked rootChecked) effect .root
   GeneralDictionaryVersionLoopSecondInstall238.installable

theorem not_before : effect.plan ∉ plans registry installed root (declChecked rootChecked) := by
 intro seen
 have old := ((plans_exact ..).mp seen).context_eq
 have freshCtx := ((plans_exact ..).mp discovered_after).context_eq
 exact contexts_differ (old.symm.trans freshCtx)

/-- Even on reachable journals, the strict projection does not determine the
actual structural Plan table. This refutes only factoring this representation
through the projection. Both administrative moves are genuine source Steps. -/
theorem no_exact_factor (owners : List Nat) (pool : List GeneralSourceState.Output)
 (read : GeneralRebaseUniversalObserver263.Current owners pool → GeneralNominalCenters.Plan roles → Prop)
 (claims : ∀ state, B4TargetV8.Reachable (Boundary roles) sourceRegistry root state →
   ∀ plan, read (project owners pool state) plan ↔ plan ∈ plans registry state root (declChecked rootChecked)) : False := by
 have after := (claims retargeted GeneralDictionaryVersionLoopPrefix238.reachable effect.plan).mpr discovered_after
 rw [←same_projection owners pool] at after
 exact not_before ((claims installed GeneralDictionaryVersionLoopInstall238.reachable_installed effect.plan).mp after)

end Yulang.GeneralRebaseStutterPlanBoundary268
