import Yulang.GeneralRebasePrivateStore282
import Yulang.GeneralPresenceOrderedSort247
import Yulang.GeneralPresenceOrderedDedup247
import Yulang.GeneralNominalOrderedSupport248
import Yulang.GeneralNominalOrderedJournalExpansion249
import Yulang.GeneralNominalRebaseJournalProjection243

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseHistoryOrder282
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralNominalVersionedMixedSeedLedger237 (entries)
open GeneralNominalVersionedHistoryEquations237 (descending coherent)
open GeneralPresenceOrderedSort247 (sort Ranked ranked_sorted)
open GeneralPresenceOrderedDedup247 (dedup dedup_subset member_preserved targets_nodup)
open GeneralPresenceDefinitionRewrite244 (Entry block)
open GeneralPresenceOrderedBlock247 (SafeOrder solve solve_rows solve_outside)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (model)
open PresenceNormalForm (All)
open GeneralRebasePrivateStore282 (Joint)

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

def history (state : State roles) : List (Entry Nat) := (sort (dedup (entries state))).getD []

theorem ranked (state : State roles) : Ranked id (dedup (entries state)) := by
  intro row first dep second used
  exact descending state row (dedup_subset _ first) dep.1 (GeneralNominalOrderedSupport248.typed_reads_subset _ used)

theorem ordered (state : State roles) :
    sort (dedup (entries state)) = some (history state) ∧
    (dedup (entries state)).Perm (history state) ∧ SafeOrder (history state) := by
  obtain ⟨list,success,equivalent,safe⟩ := ranked_sorted id _ (ranked state) (targets_nodup _)
  unfold history
  rw [success]
  exact ⟨rfl,equivalent,safe⟩

theorem member_exact (reach : Reachable registry root state) (e : Entry Nat) :
    e ∈ history state ↔ e ∈ entries state := by
  have eq := (ordered state).2.1.mem_iff (a := e)
  have good := GeneralNominalVersionedMixedSeedLedger237.reachable reach
  exact eq.symm.trans ⟨fun h => dedup_subset _ h,member_preserved _ (coherent good) e⟩

theorem models_history (reach : Reachable registry root state) {m : Assignment}
    (valid : Models state m) : All model m (block (history state)) := by
  intro atom listed
  obtain ⟨entry,used,atomUsed⟩ := List.mem_flatMap.mp listed
  exact GeneralNominalVersionedHistoryNormalization238.historical_equations valid entry
    ((member_exact reach entry).mp used) atom atomUsed

def decode (state : State roles) (m : Assignment) := solve model (history state) m

theorem compatible (reach : Reachable registry root state) {m : Assignment} (valid : Models state m) :
    GeneralNominalAssignmentCongruence238.Same (decode state m) m :=
  GeneralPresenceOrderedRecovery247.solve_compatible _ GeneralPresenceCommonLaws245.common_laws _ _
    (models_history reach valid)

theorem preserves_joint (reach : Reachable registry root state) {m : Assignment}
    (valid : Joint state r focus payload m) :
    Joint state r focus payload (decode state m) :=
  ⟨(GeneralNominalVersionedSourceCongruence238.source_models_iff (compatible reach valid.1) reach).mpr valid.1,
   (GeneralNominalRebaseEvidenceProjection243.evidence_congruent r state.core focus payload _ _
     (compatible reach valid.1)).mpr valid.2⟩

end Yulang.GeneralRebaseHistoryOrder282
