import Yulang.GeneralRebaseWatchStep284

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseActualWatch284
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedSeedLedger237 (Recorded)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralNominalVersionedMixedRegistry234 (LegacyEmpty)
open GeneralNominalVersionedInstall232 (install InstallationModels)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralRebaseHistoryOrder282 (history decode ordered)
open GeneralRebaseProspective282 (recorded_install empty_install decoded)
open GeneralRebaseProspectiveDelta283 (ext_history coherent_history descending_history)
open GeneralRebaseFutureWatch284 (Closed Covers preserves)
open GeneralRebaseWatchStep284 (NoReveal next advance)
open GeneralRebaseSortedCache283 (Ascending safe)
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralPresenceOrderedBlock247 (solve solve_rows)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseJournalView243 (compile compile_exact)
open GeneralRebaseSliceJournal283 (journalReads)
open GeneralRebaseSliceEvidence283 (reads Evidence)
open CommonNominalFullCarrier (model)
open Core.PresenceGeneration (CompTerm)

structure Cache (state : State roles) (watch : List Nat) (defs : List (Entry Nat)) : Prop where
  covers : Covers watch (history state) defs
  sorted : Ascending defs

def bump (watch : List Nat) (defs : List (Entry Nat)) (effect : Effect roles) :=
  next watch defs (packetEntries effect.plan.packet)

variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles}
  {r : Registry} {root : Occurrence roles} {old new : List Nat} {defs : List (Entry Nat)}

theorem install_valid (prior : Cache state old defs) (recorded : Recorded state)
    (snap : effect.snapshot = state.core) (closed : Closed new (history (install state effect)))
    (noReveal : NoReveal old new (history state)) :
    Cache (install state effect) new (bump new defs effect) := by
  obtain ⟨covers,sorted⟩ := advance prior.covers prior.sorted (ext_history recorded snap)
    (coherent_history _ (recorded_install recorded snap)) closed noReveal
  exact ⟨covers,sorted⟩

def interpret (defs : List (Entry Nat)) (base : Assignment) := solve model defs base

theorem preserve_coord {watch : List Nat} (prior : Cache state watch defs) (recorded : Recorded state)
    (base : Assignment) (n : Nat) (queried : n ∈ watch) :
    interpret defs base n = decode state base n :=
  preserves prior.covers (descending_history _ recorded) (ordered _).2.2
    (safe _ prior.sorted (fun row retained => descending_history _ recorded row (prior.covers.sound retained)))
    (fun _ => rfl) (fun _ _ => rfl) n queried

theorem preserve_rows (state : State roles) (defs : List (Entry Nat)) (base : Assignment) (n : Nat) :
    (interpret defs base n).2 = (decode state base n).2 :=
  (solve_rows model _ _ n).trans (solve_rows model _ _ n).symm

theorem preserve_models {watch : List Nat} (prior : Cache state watch defs) (recorded : Recorded state)
    (empty : LegacyEmpty state) (readable : journalReads state ⊆ watch) (base : Assignment) :
    Models state (interpret defs base) ↔ Models state (decode state base) := by
  apply (compile_exact state empty CompTerm.var _).symm.trans
  apply Iff.trans _ (compile_exact state empty CompTerm.var _)
  apply GeneralNominalJournalSupport249.models_iff
  · exact preserve_rows state defs base
  · intro n uses
    exact congrArg Prod.fst (preserve_coord prior recorded base n (readable uses))

theorem preserve_evidence {watch : List Nat} (prior : Cache state watch defs) (recorded : Recorded state)
    (reg : Registry) (family : List (GeneralNominalCenters.Plan roles)) (readable : reads family ⊆ watch)
    (base : Assignment) (focus : Occurrence roles) (payload : GeneralDictionaryReadback.Payload) :
    Evidence family reg state (interpret defs base) focus payload ↔
    Evidence family reg state (decode state base) focus payload :=
  GeneralRebaseSliceEvidence283.evidence_iff family reg state (preserve_rows state defs base)
    (fun n uses => congrArg Prod.fst (preserve_coord prior recorded base n (readable uses))) focus payload

theorem candidate (prior : Cache state old defs) (reach : Reachable r root state)
    (snap : effect.snapshot = state.core) (closed : Closed new (history (install state effect)))
    (noReveal : NoReveal old new (history state)) (reads : journalReads (install state effect) ⊆ new) :
    (∃ base, Models (install state effect) (interpret (bump new defs effect) base)) ↔
      ∃ m, InstallationModels state effect m := by
  have recorded := GeneralNominalVersionedMixedSeedLedger237.reachable reach
  have valid := install_valid prior recorded snap closed noReveal
  have compat (base : Assignment) :=
    (preserve_models valid (recorded_install recorded snap)
      (empty_install (effect := effect) (GeneralNominalVersionedMixedRegistry234.reachable_legacy_empty reach)) reads base).trans
    (decoded (empty_install (effect := effect) (GeneralNominalVersionedMixedRegistry234.reachable_legacy_empty reach)) base).symm
  exact (exists_congr compat).trans (GeneralRebaseProspective282.acceptance_before reach snap)

end Yulang.GeneralRebaseActualWatch284
