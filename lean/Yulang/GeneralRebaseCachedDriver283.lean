import Yulang.GeneralRebaseIncrementalGate283
import Yulang.GeneralRebaseCompiledRegressions282

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseCachedDriver283
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable reachable_step)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedMixedKernel234 (Committed)
open GeneralNominalSaturationState (Generated)
open GeneralRebaseMixedCounts277 (Actual)
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralRebaseInstallCache283 (Valid add interpret forward)
open GeneralRebaseIncrementalGate283 (Gate enabled)
open GeneralRebaseCompiledInstall282 (Setup setup OldInstall)
open GeneralRebaseCompiledStep282 (ExistingNonInstall old_split)
open GeneralNominalVersionedMixedSeedLedger237 (Recorded)

abbrev Cache := List (Entry Nat)

structure Snapshot (roles : Roles.RoleDecls) where
  raw : State roles
  defs : Cache

variable {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles}
  {before after initialRaw finalRaw : State roles} {p q : Snapshot roles}

theorem quiet_plans (made : ExistingNonInstall r root initialRaw finalRaw) : finalRaw.plans = initialRaw.plans := by
  obtain ⟨⟨focus,generated,action⟩,len⟩ := made
  cases action with
  | administrative action => cases action <;> rfl
  | refresh => rfl
  | merge => rfl
  | install e _ _ =>
    change initialRaw.plans.length + 1 = initialRaw.plans.length at len
    omega

def Initial (raw : State roles) : Snapshot roles := ⟨raw,GeneralRebaseInstallCache283.initial raw⟩

def Move (r : Registry) (root : Occurrence roles) (p q : Snapshot roles) : Prop :=
  Reachable r root p.raw ∧ Valid p.defs p.raw ∧
    ((ExistingNonInstall r root p.raw q.raw ∧ q.defs = p.defs) ∨
    ∃ e, Generated p.raw.core.erased.current root e.plan.packet.site.occurrence ∧
      Setup r p.raw e ∧ ¬ Committed p.raw e.plan ∧
      q = ⟨install p.raw e,add p.defs e⟩ ∧ ∃ base, Gate p.raw e p.defs (interpret p.defs base))

theorem raw (move : Move r root p q) : Actual r root p.raw q.raw := by
  rcases move.2.2 with quiet|⟨e,source,setup,novel,rfl,proof⟩
  · exact quiet.1.1
  · exact ⟨_,source,.install e ((enabled move.2.1 move.1 setup).mpr proof) novel⟩

theorem valid_next (move : Move r root p q) : Valid q.defs q.raw := by
  rcases move.2.2 with ⟨quiet,same⟩|⟨e,source,setup,novel,rfl,proof⟩
  · rw [same]
    exact GeneralRebaseInstallCache283.transport (quiet_plans quiet) move.2.1
  · exact GeneralRebaseInstallCache283.add_valid move.2.1
      (GeneralNominalVersionedMixedSeedLedger237.reachable move.1) setup.snapshot_eq

theorem lift_one (seen : Reachable r root p.raw) (cached : Valid p.defs p.raw)
    (made : Actual r root p.raw after) : ∃ q : Snapshot roles, q.raw = after ∧ Move r root p q := by
  rcases old_split made with quiet|⟨e,src,ready,novel,rfl⟩
  · exact ⟨⟨after,p.defs⟩,rfl,seen,cached,Or.inl ⟨quiet,rfl⟩⟩
  · exact ⟨⟨_,add p.defs e⟩,rfl,seen,cached,Or.inr
      ⟨e,src,setup ready,novel,rfl,(enabled cached seen (setup ready)).mp ready⟩⟩

theorem paths_raw (path : B4Target.Steps (Move r root) p q) :
    B4Target.Steps (Actual r root) p.raw q.raw := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (raw step)

theorem paths_lift (seen : Reachable r root p.raw) (cached : Valid p.defs p.raw)
    (path : B4Target.Steps (Actual r root) p.raw after) :
    ∃ q : Snapshot roles, q.raw = after ∧ B4Target.Steps (Move r root) p q ∧ Valid q.defs q.raw := by
  induction path with
  | refl => exact ⟨p,rfl,.refl,cached⟩
  | tail prev step ih =>
    obtain ⟨mid,rfl,trace,valid⟩ := ih
    obtain ⟨q,rfl,edge⟩ := lift_one (B4TargetV5.reachable_steps _ seen prev) valid step
    exact ⟨q,rfl,.tail trace edge,valid_next edge⟩

theorem initial_paths (seen : Reachable r root initialRaw) :
    B4Target.Steps (Actual r root) initialRaw finalRaw ↔
      ∃ q : Snapshot roles, q.raw = finalRaw ∧ B4Target.Steps (Move r root) (Initial initialRaw) q ∧ Valid q.defs q.raw := by
  constructor
  · exact paths_lift (p := Initial initialRaw) seen (GeneralRebaseInstallCache283.initial_valid
      (GeneralNominalVersionedMixedSeedLedger237.reachable seen))
  · rintro ⟨q,rfl,path,_⟩
    exact paths_raw path

theorem reflects_acc (seen : Reachable r root p.raw) (cache : Valid p.defs p.raw)
    (accessible : Acc (fun after before => Move r root before after) p) :
    Acc (fun later earlier => Actual r root earlier later) p.raw := by
  induction accessible with
  | intro state _ smaller =>
    refine .intro state.raw ?_
    intro next edge
    obtain ⟨q,rfl,move⟩ := lift_one seen cache edge
    exact smaller q move (reachable_step seen edge) (valid_next move)

theorem preserves_acc (a : Acc (fun later earlier => Actual r root earlier later) p.raw) :
    Acc (fun later earlier => Move r root earlier later) p :=
  Subrelation.accessible (fun h => raw h) (InvImage.accessible Snapshot.raw a)

end Yulang.GeneralRebaseCachedDriver283
