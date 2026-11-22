import Yulang.GeneralDeclarativeHybridRegister345
import Yulang.GeneralDeclarativeCurrentReady345

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeHybridTrace345
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralWhereVersionInstall317 (Journal InstallStep install Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary checked_compiled)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralNominalCenteredHeadMatStepRoles (Invariant)
open GeneralNominalCenters (Plan)
open GeneralNominalCommonBridge (Assignment)

structure SourceTrack (r : Registry) (root : Occurrence rs) (seed : Nat) (j : Journal rs) : Prop where
  registered : GeneralNominalVersionedMixedTrace235.Invariant j.mixed root
  origin : Invariant (Compiled r) seed root j.mixed.core
  coverage : Coverage (Compiled r) j.mixed.core.erased.current.context.interpretation

/-- This is explicitly an accounting relation for the isolated
prototype plus native mixed steps. No scheduler or replacement
for the actual raw solver relation is defined here. -/
inductive Walk (r : Registry) (root : Occurrence rs) : Journal rs → Journal rs → Prop where
  | refl : Walk r root j j
  | native : Walk r root start before →
      GeneralNominalVersionedMixedKernel234.Step (Compiled r) root before.mixed after →
      Walk r root start ⟨after,before.versionedWhere⟩
  | isolated : Walk r root start before → InstallStep r before after →
      Walk r root start after

theorem from_reach {r : Registry} {root : Occurrence rs} {j : Journal rs}
    (checked : (boundary rs).Checked r)
    (reached : B4TargetV8.Reachable (boundary rs) r root j.mixed) :
    SourceTrack r root j.mixed.core.erased.source.state.seed j :=
  ⟨GeneralNominalVersionedMixedTrace235.reachable reached,
    GeneralNominalVersionedMixedRoles235.reachable checked reached,
    GeneralNominalVersionedMixedReady235.coverage reached⟩

theorem along {r : Registry} {root : Occurrence rs} {first final : Journal rs}
    (checked : (boundary rs).Checked r) (start : SourceTrack r root seed first)
    (trace : Walk r root first final) : SourceTrack r root seed final := by
  induction trace with
  | refl => exact start
  | native _ step ih =>
    refine ⟨GeneralNominalVersionedMixedTrace235.step ih.registered step,
      GeneralNominalVersionedMixedRoles235.step (checked_compiled checked).2 ih.registered.1 ih.origin step,?_⟩
    rw [(GeneralNominalVersionedMixedGrowth234.step step).interpretation]
    exact ih.coverage
  | isolated _ step ih =>
    exact ⟨GeneralDeclarativeHybridRegister345.install ih.registered step,
      GeneralDeclarativeCurrentSeed345.after_origin ih.origin step,
      GeneralDeclarativeCurrentSeed345.after_coverage ih.coverage step⟩

theorem replay_next {r : Registry} {root : Occurrence rs} {first before : Journal rs}
    {ctx : GeneralNominalCandidates.Context} {p : Plan rs}
    (checked : (boundary rs).Checked r) (start : SourceTrack r root seed first)
    (trace : Walk r root first before) (step : InstallStep r before (install before ctx p))
    (m : Assignment) (fit : Models (install before ctx p) m) (protect : List Nat) :
    ∃ prep state ports wheres roots n,
      GeneralDeclarativeCommitPackage344.Witness (install before ctx p) p m n protect prep state ports wheres roots := by
  have tracked := along checked start trace
  have ready := GeneralDeclarativeCurrentReady345.after_ready tracked.origin tracked.coverage step (by
    change (before.versionedWhere ++ [p])[before.versionedWhere.length]? = some p
    rw [List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]; rfl)
  exact GeneralDeclarativePackageBoundary344.actual step m fit protect ready.2

end Yulang.GeneralDeclarativeHybridTrace345
