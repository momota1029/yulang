import Yulang.GeneralRebaseSliceExact283

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseSliceJournal283
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedRegistry234 (LegacyEmpty)
open GeneralNominalVersionedMixedSeedLedger237 (Recorded)
open GeneralRebaseInstallCache283 (Valid interpret descending interpret_exact)
open GeneralRebaseSortedCache283 (safe)
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralPresenceOrderedBlock247 (solve solve_rows)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRebaseJournalView243 (compile compile_exact)
open GeneralNominalJournalSupport249 (support models_iff)
open Core.PresenceGeneration (CompTerm)
open CommonNominalFullCarrier (model)
open GeneralRebaseSlice283 (build)

def sliced (cache : List (Entry Nat)) (query : List Nat) (base : Assignment) :=
  solve model (build cache query).keep base

theorem rows_same (cache : List (Entry Nat)) (query : List Nat) (base : Assignment) (n : Nat) :
    (sliced cache query base n).2 = (interpret cache base n).2 :=
  (solve_rows model _ _ n).trans (solve_rows model _ _ n).symm

theorem agrees {cache : List (Entry Nat)} {state : State roles}
    (v : Valid cache state) (r : Recorded state) (query : List Nat)
    (base : Assignment) (n : Nat) (asked : n ∈ query) :
    sliced cache query base n = interpret cache base n :=
  GeneralRebaseSliceExact283.queries cache query (safe _ v.increasing (descending v r)) (descending v r) base n asked

noncomputable def journalReads (state : State roles) := support (compile state CompTerm.var)

theorem journal {cache : List (Entry Nat)} {state : State roles}
    (v : Valid cache state) (r : Recorded state) (empty : LegacyEmpty state)
    {query : List Nat} (contains : journalReads state ⊆ query) (base : Assignment) :
    Models state (sliced cache query base) ↔ Models state (interpret cache base) := by
  exact (compile_exact state empty CompTerm.var _).symm.trans
    ((models_iff (compile state CompTerm.var) _ _ (rows_same cache query base)
      (fun n used => congrArg Prod.fst (agrees v r query base n (contains used)))).trans
      (compile_exact state empty CompTerm.var _))

end Yulang.GeneralRebaseSliceJournal283
