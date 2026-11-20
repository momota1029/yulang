import Yulang.GeneralRebaseWatchBudgetProbe284

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseWatchValidatorSource284
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedSeedLedger237 (Recorded entries)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralNominalVersionedInstall232 (install InstallationModels)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralRebaseHistoryOrder282 (history decode)
open GeneralRebaseWatchValidator284 (Compact Valid update)
open GeneralRebaseActualWatch284 (Cache interpret preserve_models)
open GeneralRebaseSliceJournal283 (journalReads)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseProspectiveDelta283 (ext_history coherent_history)
open GeneralRebaseProspective282 (recorded_install)
open GeneralRebaseFutureWatch284 (Covers Closed)
open GeneralPresenceDefinitionRewrite244 (Entry)

variable {roles : Roles.RoleDecls} {before : State roles} {effect : Effect roles}
  {r : Registry} {root : Occurrence roles}

def candidate (c : Compact) (watch : List Nat) (e : Effect roles) : Option Compact :=
  update c watch (packetEntries e.plan.packet)

theorem candidate_valid {c d : Compact} {watch : List Nat}
    (prior : Valid c (history before)) (recorded : Recorded before)
    (snap : effect.snapshot = before.core) (checked : candidate c watch effect = some d) :
    Valid d (history (install before effect)) ∧ d.kept.length ≤ watch.length := by
  apply GeneralRebaseWatchValidator284.checked prior (ext_history recorded snap)
    (coherent_history _ (recorded_install recorded snap)) checked

theorem watch_unchanged {c d : Compact} {watch : List Nat}
    (checked : candidate c watch effect = some d) : d.watch = watch := by
  unfold candidate at checked
  simp only [update] at checked
  split at checked
  · cases Option.some.inj checked
    rfl
  · cases checked

theorem candidate_exact {c d : Compact} {watch : List Nat}
    (prior : Valid c (history before)) (seen : Reachable r root before)
    (snap : effect.snapshot = before.core) (checked : candidate c watch effect = some d)
    (reads : journalReads (install before effect) ⊆ watch) :
    (∃ b, Models (install before effect) (interpret d.kept b)) ↔ ∃ a, InstallationModels before effect a := by
  have record := GeneralNominalVersionedMixedSeedLedger237.reachable seen
  have stateNext := candidate_valid prior record snap checked
  have leftEmpty := GeneralNominalVersionedMixedRegistry234.reachable_legacy_empty seen
  have rightEmpty := GeneralRebaseProspective282.empty_install (effect := effect) leftEmpty
  have cache : Cache (install before effect) d.watch d.kept := ⟨stateNext.1.covers,stateNext.1.sorted⟩
  have covered : journalReads (install before effect) ⊆ d.watch := by rw [watch_unchanged checked]; exact reads
  have eq (base : Assignment) :=
    (preserve_models cache (recorded_install record snap) rightEmpty covered base).trans
      (GeneralRebaseProspective282.decoded rightEmpty base).symm
  exact (exists_congr eq).trans (GeneralRebaseProspective282.acceptance_before seen snap)

theorem history_unchanged {s t : State roles} {c d : Compact} {watch : List Nat}
    (same : s.plans = t.plans) (prior : Valid c (history s))
    (recorded : Recorded t) (changed : update c watch [] = some d) :
    Valid d (history t) ∧ d.kept.length ≤ watch.length := by
  have sameHistory : history s = history t := by
    unfold history entries; rw [same]
  apply GeneralRebaseWatchValidator284.checked prior
    (fun e => by rw [sameHistory]; simp) (coherent_history _ recorded) changed


theorem passes {c : Compact} {watch : List Nat} (prior : Valid c (history before))
    (recorded : Recorded before) (snap : effect.snapshot = before.core)
    (acceptable : GeneralRebaseWatchValidator284.admits c.watermark c.watch watch = true)
    (closed : Closed watch (history (install before effect))) :
    ∃ d, candidate c watch effect = some d := by
  have relevant := GeneralRebaseWatchStep284.advance prior.covers prior.sorted (ext_history recorded snap)
    (coherent_history _ (recorded_install recorded snap)) closed
    (GeneralRebaseWatchValidator284.no_reveal prior.bound acceptable)
  have rows := (GeneralRebaseWatchValidator284.check_sound watch _).mpr (fun e found =>
    closed e (relevant.1.sound found) (GeneralRebaseWatchStep284.watches_only _ _ _ e found))
  refine ⟨⟨GeneralRebaseWatchValidator284.high c.watermark (packetEntries effect.plan.packet),watch,
    GeneralRebaseWatchStep284.next watch c.kept (packetEntries effect.plan.packet)⟩,?_⟩
  simp [candidate,update,acceptable,rows]

end Yulang.GeneralRebaseWatchValidatorSource284
