import Yulang.GeneralRebaseOptionalWatch284

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseCertifiedWatchDriver284
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable reachable_step)
open GeneralNominalVersionedMixedKernel234 (Committed)
open GeneralRebaseMixedCounts277 (Actual)
open GeneralRebaseCompiledStep282 (ExistingNonInstall)
open GeneralRebaseCompiledInstall282 (Setup setup OldInstall add_common)
open GeneralNominalSaturationState (Generated)
open GeneralRebaseWatchValidator284 (Compact Valid update)
open GeneralRebaseWatchValidatorSource284 (candidate candidate_valid candidate_exact)
open GeneralRebaseHistoryOrder282 (history)
open GeneralRebaseSliceJournal283 (journalReads)
open GeneralRebaseActualWatch284 (interpret)

structure Node (roles : Roles.RoleDecls) where
  raw : State roles
  comp : Compact

def Common (s : Node roles) : Prop :=
  ∃ a, Models s.raw (interpret s.comp.kept a)

def CheckedInstall (r : Registry) (root : Occurrence roles) (first last : Node roles) : Prop :=
  ∃ e, Generated first.raw.core.erased.current root e.plan.packet.site.occurrence ∧
    Setup r first.raw e ∧ ¬ Committed first.raw e.plan ∧
    last.raw = install first.raw e ∧ candidate first.comp last.comp.watch e = some last.comp ∧
    journalReads last.raw ⊆ last.comp.watch ∧ Common last

def CheckedQuiet (r : Registry) (root : Occurrence roles) (first last : Node roles) : Prop :=
  ExistingNonInstall r root first.raw last.raw ∧
  update first.comp last.comp.watch [] = some last.comp

def Step (r : Registry) (root : Occurrence roles) (first last : Node roles) : Prop :=
  Reachable r root first.raw ∧ Valid first.comp (history first.raw) ∧
  (CheckedQuiet r root first last ∨ CheckedInstall r root first last)

variable {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles} {first last : Node roles}

theorem sound (checked : Step r root first last) : Actual r root first.raw last.raw := by
  rcases checked.2.2 with quiet|effect
  · exact quiet.1.1
  · obtain ⟨e,generated,fields,novel,rawEq,cacheEq,covers,common⟩ := effect
    have good := (candidate_exact (effect := e) checked.2.1 checked.1 fields.snapshot_eq cacheEq
      (rawEq ▸ covers)).mp (rawEq ▸ common)
    rw [rawEq]
    exact ⟨_,generated,.install e (add_common fields good) novel⟩

theorem valid_after (checked : Step r root first last) :
    Valid last.comp (history last.raw) ∧ last.comp.kept.length ≤ last.comp.watch.length := by
  rcases checked.2.2 with quiet|effect
  · exact GeneralRebaseWatchValidatorSource284.history_unchanged
      (GeneralRebaseCachedDriver283.quiet_plans quiet.1).symm checked.2.1
      (GeneralNominalVersionedMixedSeedLedger237.reachable (reachable_step checked.1 quiet.1.1)) quiet.2
  · obtain ⟨e,_,fields,_,eq,replayed,_,_⟩ := effect
    rw [eq]
    exact candidate_valid checked.2.1 (GeneralNominalVersionedMixedSeedLedger237.reachable checked.1)
      fields.snapshot_eq replayed

theorem quiet_lift (seen : Reachable r root first.raw) (valid : Valid first.comp (history first.raw))
    (work : CheckedQuiet r root first last) : Step r root first last :=
  ⟨seen,valid,Or.inl work⟩

theorem install_lift (seen : Reachable r root first.raw) (valid : Valid first.comp (history first.raw))
    {e : Effect roles}
    (generated : Generated first.raw.core.erased.current root e.plan.packet.site.occurrence)
    (enabled : GeneralNominalVersionedMixedKernel234.Installable
      (GeneralNominalCenteredHeadAllocEncoding.registry r) first.raw e)
    (novel : ¬ Committed first.raw e.plan) (rawEq : last.raw = install first.raw e)
    (cached : candidate first.comp last.comp.watch e = some last.comp)
    (readable : journalReads last.raw ⊆ last.comp.watch) : Step r root first last := by
  have exact := (candidate_exact valid seen enabled.snapshot_eq cached (rawEq ▸ readable)).mpr enabled.common
  have withCache : Common last := by
    unfold Common; rw [rawEq]; assumption
  exact ⟨seen,valid,Or.inr ⟨e,generated,setup enabled,novel,rawEq,cached,readable,withCache⟩⟩

theorem accepted_routes {start finish : Node roles} (path : B4Target.Steps (Step r root) start finish) :
    B4Target.Steps (Actual r root) start.raw finish.raw := by
  induction path with
  | refl => exact .refl
  | tail old edge ih => exact .tail ih (sound edge)

theorem rejected_not_inferred {c : Compact} {watch : List Nat} {e : Effect roles}
    (failed : candidate c watch e = none) :
    ¬ ∃ d, candidate c watch e = some d := by
  rintro ⟨d,got⟩
  rw [failed] at got
  cases got

end Yulang.GeneralRebaseCertifiedWatchDriver284
