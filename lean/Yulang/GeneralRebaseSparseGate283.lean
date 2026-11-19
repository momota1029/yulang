import Yulang.GeneralRebaseCrossProbe283

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseSparseGate283
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralNominalVersionedMixedSeedLedger237 (Recorded)
open GeneralNominalVersionedMixedRegistry234 (LegacyEmpty reachable_legacy_empty)
open GeneralNominalVersionedInstall232 (install install_models)
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (model)
open GeneralRebaseInstallCache283 (Valid add interpret descending coherent)
open GeneralRebaseCrossProbe283 (Sparse refresh)
open GeneralRebaseDirtyHistory283 (select)
open GeneralRebaseIncrementalGate283 (catalog catalog_exact Delta factor_install)
open GeneralRebaseJournalChecks283 (Checks recheck_exact reuse)
open GeneralRebaseSortedCache283 (safe)

variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles}
  {registry : Registry} {root : Occurrence roles} {defs : List (Entry Nat)}

def affected (defs : List (Entry Nat)) (effect : Effect roles) (addresses : List Nat) :=
  addresses ++ (select (defs.map Prod.fst) (add defs effect) addresses).map Prod.fst

def evaluate (defs : List (Entry Nat)) (effect : Effect roles) (addresses : List Nat)
    (cache base : Assignment) := refresh defs (add defs effect) addresses cache base

theorem unchanged (first last : Assignment) (addresses : List Nat) (sparse : Sparse first last addresses)
    (n : Nat) (clean : n ∉ affected defs effect addresses) :
    evaluate defs effect addresses (interpret defs first) last n = interpret defs first n := by
  unfold evaluate refresh
  have noWrite : ∀ e ∈ select (defs.map Prod.fst) (add defs effect) addresses, e.1 ≠ n := by
    intro entry found hit
    exact clean (List.mem_append_right _ (List.mem_map.mpr ⟨entry,found,hit⟩))
  rw [GeneralPresenceOrderedBlock247.solve_outside model _ _ _ noWrite]
  exact GeneralRebaseCrossProbe283.unchanged_on_blend defs sparse n
    (fun member => clean (List.mem_append_left _ member))

theorem same_rows (first last : Assignment) (addresses : List Nat) (sparse : Sparse first last addresses)
    (n : Nat) : (evaluate defs effect addresses (interpret defs first) last n).2 = (interpret defs first n).2 :=
  (GeneralRebaseCrossProbe283.rows defs (add defs effect) addresses sparse n).trans
    ((sparse.1 n).symm.trans (GeneralPresenceOrderedBlock247.solve_rows model defs first n).symm)

theorem exact_cached (valid : Valid defs state) (old : Recorded state) (snap : effect.snapshot = state.core)
    {first last : Assignment} {addresses : List Nat} (sparse : Sparse first last addresses) :
    evaluate defs effect addresses (interpret defs first) last = interpret (add defs effect) last := by
  have good := GeneralRebaseInstallCache283.add_valid valid old snap
  have recs := GeneralRebaseProspective282.recorded_install old snap
  apply GeneralRebaseCrossProbe283.exact_refresh
  · intro entry found
    exact (good.content entry).mpr ((GeneralRebaseProspectiveDelta283.ext_history old snap entry).mpr
      (Or.inr ((valid.content entry).mp found)))
  · exact coherent good recs
  · exact descending good recs
  · exact safe _ valid.increasing (descending valid old)
  · exact safe _ good.increasing (descending good recs)
  · exact sparse

theorem exact_raw (valid : Valid defs state) (seen : Reachable registry root state)
    (snap : effect.snapshot = state.core) {first last : Assignment} {addresses : List Nat}
    (sparse : Sparse first last addresses) :
    evaluate defs effect addresses (interpret defs first) last = GeneralRebaseHistoryOrder282.decode (install state effect) last := by
  have old := GeneralNominalVersionedMixedSeedLedger237.reachable seen
  exact (exact_cached valid old snap sparse).trans
    (GeneralRebaseInstallCache283.interpret_exact
      (GeneralRebaseInstallCache283.add_valid valid old snap) (GeneralRebaseProspective282.recorded_install old snap) last)

def Gate (state : State roles) (effect : Effect roles) (defs : List (Entry Nat)) (addresses : List Nat)
    (old base : Assignment) : Prop :=
  let a := evaluate defs effect addresses old base
  Checks.recheck (catalog state) (affected defs effect addresses) old a ∧ Delta state effect a

theorem gate_exact (empty : LegacyEmpty state) (snap : effect.snapshot = state.core)
    (first last : Assignment) (addresses : List Nat) (sparse : Sparse first last addresses) :
    Gate state effect defs addresses (interpret defs first) last ↔
    Models (install state effect) (evaluate defs effect addresses (interpret defs first) last) := by
  have equiv := (recheck_exact (catalog state) (affected defs effect addresses) (interpret defs first)
    (evaluate defs effect addresses (interpret defs first) last)
    (fun n => (same_rows first last addresses sparse n).symm)
    (fun n clean => (unchanged first last addresses sparse n clean).symm)).trans (catalog_exact empty _)
  exact (and_congr equiv Iff.rfl).trans ((factor_install empty _).symm.trans (install_models snap).symm)

theorem semantic (valid : Valid defs state) (seen : Reachable registry root state)
    (snap : effect.snapshot = state.core) (first last : Assignment) (addresses : List Nat)
    (sparse : Sparse first last addresses) :
    Gate state effect defs addresses (interpret defs first) last ↔
    GeneralRebaseProspective282.Compiled (install state effect) last := by
  rw [gate_exact (reachable_legacy_empty seen) snap first last addresses sparse,
    exact_raw valid seen snap sparse,
    GeneralRebaseProspective282.decoded (GeneralRebaseProspective282.empty_install (reachable_legacy_empty seen))]

end Yulang.GeneralRebaseSparseGate283
