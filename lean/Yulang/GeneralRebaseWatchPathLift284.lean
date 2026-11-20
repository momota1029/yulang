import Yulang.GeneralRebaseCertifiedWatchDriver284

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseWatchPathLift284
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable reachable_step)
open GeneralRebaseMixedCounts277 (Actual)
open GeneralRebaseCompiledStep282 (old_split)
open GeneralRebaseCertifiedWatchDriver284 (Node Step sound valid_after quiet_lift install_lift)
open GeneralRebaseWatchValidator284 (Compact Valid admits checkRows update)
open GeneralRebaseWatchStep284 (next)
open GeneralRebaseFutureWatch284 (Closed)
open GeneralRebaseHistoryOrder282 (history)
open GeneralRebaseSliceJournal283 (journalReads)
open GeneralNominalAcyclicEquations237 (Coherent)
open GeneralPresenceDefinitionRewrite244 (Entry)

theorem full_pass {c : Compact} {before full delta : List (Entry Nat)} {watch : List Nat}
    (prior : Valid c before) (split : ∀ e, e ∈ full ↔ e ∈ delta ∨ e ∈ before)
    (coherent : Coherent full) (admission : admits c.watermark c.watch watch = true)
    (closed : Closed watch full) : ∃ d, update c watch delta = some d ∧ d.watch = watch := by
  have relevant := GeneralRebaseWatchStep284.advance prior.covers prior.sorted split coherent closed
    (GeneralRebaseWatchValidator284.no_reveal prior.bound admission)
  have safe := (GeneralRebaseWatchValidator284.check_sound watch _).mpr (fun e found =>
    closed e (relevant.1.sound found) (GeneralRebaseWatchStep284.watches_only _ _ _ e found))
  refine ⟨⟨GeneralRebaseWatchValidator284.high c.watermark delta,watch,next watch c.kept delta⟩,?_,rfl⟩
  simp [update,admission,safe]

structure Coverage (raw : State roles) (watch : List Nat) : Prop where
  closed : Closed watch (history raw)
  semantic : journalReads raw ⊆ watch

variable {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles}

theorem step {before : Node roles} {out : State roles} {watch : List Nat}
    (seen : Reachable r root before.raw) (valid : Valid before.comp (history before.raw))
    (raw : Actual r root before.raw out) (watchOK : Coverage out watch)
    (admission : admits before.comp.watermark before.comp.watch watch = true) :
    ∃ next : Node roles, next.raw = out ∧ next.comp.watch = watch ∧ Step r root before next := by
  have after := reachable_step seen raw
  have record := GeneralNominalVersionedMixedSeedLedger237.reachable seen
  have newRecord := GeneralNominalVersionedMixedSeedLedger237.reachable after
  rcases old_split raw with quiet|⟨e,generated,enabled,novel,rfl⟩
  · have same := GeneralRebaseCachedDriver283.quiet_plans quiet
    have h : history out = history before.raw := by
      unfold history GeneralNominalVersionedMixedSeedLedger237.entries; rw [same]
    have split (e : Entry Nat) : e ∈ history out ↔ e ∈ ([] : List (Entry Nat)) ∨ e ∈ history before.raw := by simp [h]
    obtain ⟨next,ready,sameWatch⟩ := full_pass valid split (GeneralRebaseProspectiveDelta283.coherent_history _ newRecord)
      admission watchOK.closed
    exact ⟨⟨out,next⟩,rfl,sameWatch,quiet_lift seen valid ⟨quiet,(sameWatch.symm ▸ ready)⟩⟩
  · have split := GeneralRebaseProspectiveDelta283.ext_history record enabled.snapshot_eq
    obtain ⟨next,ready,sameWatch⟩ := full_pass valid split (GeneralRebaseProspectiveDelta283.coherent_history _ newRecord)
      admission watchOK.closed
    exact ⟨⟨_,next⟩,rfl,sameWatch,install_lift seen valid generated enabled novel rfl
      (sameWatch.symm ▸ ready) (sameWatch.symm ▸ watchOK.semantic)⟩

def Policy (roles : Roles.RoleDecls) := State roles → List Nat

def OnPolicy (plan : Policy roles) (r : Registry) (root : Occurrence roles)
    (before after : Node roles) : Prop :=
  Step r root before after ∧ after.comp.watch = plan after.raw

structure OnPath (plan : Policy roles) (r : Registry) (root : Occurrence roles) : Prop where
  observe : ∀ s, Reachable r root s → Coverage s (plan s)
  allow : ∀ a : Node roles, Reachable r root a.raw → Valid a.comp (history a.raw) →
    a.comp.watch = plan a.raw → ∀ b, Actual r root a.raw b →
    admits a.comp.watermark a.comp.watch (plan b) = true

theorem path {plan : Policy roles} (admissible : OnPath plan r root)
    {start : Node roles} {finish : State roles}
    (seen : Reachable r root start.raw) (valid : Valid start.comp (history start.raw))
    (follows : start.comp.watch = plan start.raw) :
    B4Target.Steps (Actual r root) start.raw finish ↔
    ∃ last : Node roles, last.raw = finish ∧ last.comp.watch = plan finish ∧
      B4Target.Steps (OnPolicy plan r root) start last ∧ Valid last.comp (history last.raw) := by
  constructor
  · intro route
    induction route with
    | refl => exact ⟨start,rfl,follows,.refl,valid⟩
    | @tail prior out h raw ih =>
      obtain ⟨node,rfl,watch,played,covered⟩ := ih
      have reached : Reachable r root node.raw := B4TargetV5.reachable_steps _ seen h
      have endReached := reachable_step reached raw
      obtain ⟨last,rfl,follows,verified⟩ := step reached covered raw
        (admissible.observe out endReached) (admissible.allow node reached covered watch out raw)
      exact ⟨last,rfl,follows,.tail played ⟨verified,follows⟩,(valid_after verified).1⟩
  · rintro ⟨last,rfl,_,path,_⟩
    have projected {a b : Node roles} (whole : B4Target.Steps (OnPolicy plan r root) a b) :
        B4Target.Steps (Actual r root) a.raw b.raw := by
      induction whole with
      | refl => exact .refl
      | tail a b ih => exact .tail ih (sound b.1)
    exact projected path

end Yulang.GeneralRebaseWatchPathLift284
