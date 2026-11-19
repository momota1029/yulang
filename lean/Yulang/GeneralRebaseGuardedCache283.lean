import Yulang.GeneralRebaseCanonicalCache283

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralRebaseGuardedCache283
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralRebaseChartStep281 (Chart Strict)
open GeneralRebasePhaseKeys281 (Codec Added)
open GeneralRebasePhaseMachine281 (Step)
open GeneralRebaseCachedDriver283 (Snapshot Move Initial raw)
open GeneralRebaseMixedCounts277 (Actual)
open GeneralRebaseInstallCache283 (Valid)

def Progress (chart : Chart F V) (codec : Codec roles Q) (a b : State roles) : Prop :=
  (b.plans.length = a.plans.length ∨ Strict chart a b) ∨ Added codec a b

def Guarded (chart : Chart F V) (codec : Codec roles Q) (r : Registry) (root : Occurrence roles)
    (p q : Snapshot roles) : Prop :=
  Move r root p q ∧ Progress chart codec p.raw q.raw

variable {r : Registry} {root : Occurrence roles} {chart : Chart F V} {codec : Codec roles Q}
  {p q : Snapshot roles} {s t : State roles}

theorem up (h : Guarded chart codec r root p q) : Step chart codec r root p.raw q.raw :=
  h.2.elim (fun preserving => Or.inl ⟨raw h.1,preserving⟩) (fun phase => Or.inr ⟨raw h.1,phase⟩)

theorem down (seen : Reachable r root p.raw) (cache : Valid p.defs p.raw)
    (h : Step chart codec r root p.raw t) : Guarded chart codec r root p (Initial t) :=
  ⟨(GeneralRebaseCanonicalCache283.raw_next_exact seen cache t).mpr (GeneralRebasePhaseMachine281.raw h),
    h.elim (fun ordinary => Or.inl ordinary.2) (fun phase => Or.inr phase.2)⟩

theorem initial_correct (seen : Reachable r root s) :
    Guarded chart codec r root (Initial s) (Initial t) ↔ Step chart codec r root s t :=
  ⟨up,down (p := Initial s) seen (GeneralRebaseInstallCache283.initial_valid
    (GeneralNominalVersionedMixedSeedLedger237.reachable seen))⟩

theorem paths (seen : Reachable r root s) :
    B4Target.Steps (Guarded chart codec r root) (Initial s) (Initial t) ↔
      B4Target.Steps (Step chart codec r root) s t := by
  constructor
  · intro path
    have all {p q : Snapshot roles} (path : B4Target.Steps (Guarded chart codec r root) p q) :
        B4Target.Steps (Step chart codec r root) p.raw q.raw := by
      induction path with
      | refl => exact .refl
      | tail _ act ih => exact .tail ih (up act)
    exact all path
  · intro path
    induction path with
    | refl => exact .refl
    | @tail before after h step ih =>
      exact .tail ih ((initial_correct (GeneralRebaseCompiledRegressions282.phase_reachable seen h)).mpr step)

theorem accessible (chart : Chart F V) (codec : Codec roles Q)
    (init : (boundary roles).Initial r root s) :
    Acc (fun after before => Guarded chart codec r root before after) (Initial s) :=
  Subrelation.accessible (fun h => up h)
    (InvImage.accessible Snapshot.raw (GeneralRebasePhaseMachine281.accessible chart codec init))

namespace Optional
open GeneralDictionaryOptionalInitial229 (sourceRegistry)
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralDictionaryVersionedInitialFrame233 (before)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralRebaseChartFixtures281 (outputChart)
open GeneralRebasePhaseFixture281 (codec)

theorem retains_three :
    B4Target.Steps (Guarded GeneralRebaseChartFixtures281.outputChart GeneralRebasePhaseFixture281.codec sourceRegistry GeneralDictionaryJournalRefinement228Source.root) (Initial before) (Initial installed) :=
  (paths GeneralRebaseOptionalOverwrite282.before_reached).mpr GeneralRebasePhaseFixture281.all_three

end Optional
end Yulang.GeneralRebaseGuardedCache283
