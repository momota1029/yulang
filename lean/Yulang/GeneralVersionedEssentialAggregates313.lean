import Yulang.GeneralVersionedEssentialSupport313
import Yulang.GeneralVersionedProtectedName312
import Yulang.GeneralVersionedHarmlessRefresh312

set_option backward.isDefEq.respectTransparency false
/-! The exact residual historical-coverage predicate does not depend on
a chosen derivation of support. Its exceptions are precisely report reads
and coordinates whose single-variable change can affect journal validity. -/
namespace Yulang.GeneralVersionedEssentialAggregates313
open GeneralVersionedEssentialSupport313
open GeneralVersionedSemanticPeer312 (Sufficient reportPool protectedPool)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralNominalVersionedMixedSeedLedger237 (IdCovered)
open GeneralNominalVersionedModelSupport237 (Support Observation)
open GeneralNominalSaturationState (Packet)
open GeneralNominalCommonBridge (Assignment)

def Historical (s : State roles) (id : Nat) : Prop :=
  ∃ past ∈ s.plans, ∃ old ∈ packetEntries past.packet, old.1 = id

def Active (s : State roles) (p : Packet roles) (id : Nat) : Prop :=
  Essential s id ∨ id ∈ reportPool p

def Covers (s : State roles) (p : Packet roles) : Prop :=
  ∀ entry ∈ packetEntries p, Active s p entry.1 → Historical s entry.1

theorem protected_iff {s : State roles} {p : Packet roles} {id : Nat}
    (support : Support s names) :
    id ∈ protectedPool p (trim s names) ↔ Active s p id := by
  rw [protectedPool,List.mem_append,mem_trim]
  exact ⟨Or.imp And.right id_fun,Or.imp (fun active => ⟨must_mem support active,active⟩) id_fun⟩
where id_fun {P : Prop} (h : P) := h

theorem sufficient_iff {s : State roles} {p : Packet roles} (support : Support s names) :
    Sufficient s p ↔ Covers s p := by
  constructor
  · rintro ⟨witness,finite,covered⟩ entry member (important|observed)
    · exact covered entry member (List.mem_append_left _ (must_mem finite important))
    · exact covered entry member (List.mem_append_right _ observed)
  · intro covered
    exact ⟨trim s names,trimmed support,fun entry member h => covered entry member ((protected_iff support).mp h)⟩

theorem from_exclusion {s : State roles} {p : Packet roles}
    (producer : ∀ entry ∈ packetEntries p,
      ¬ Historical s entry.1 → Inert s entry.1 ∧ entry.1 ∉ reportPool p) :
    Sufficient s p := by
  classical
  apply (sufficient_iff (GeneralNominalVersionedModelSupport237.current s)).mpr
  intro entry member active
  apply Classical.byContradiction
  intro absent
  obtain ⟨inert,unread⟩ := producer entry member absent
  exact active.elim (fun other => other inert) unread

theorem harmless_keeps {s : State roles} {ctx : GeneralNominalCandidates.Context} {id : Nat}
    (old : GeneralNominalVersionedMixedObservations233.Refresh s ctx)
    (already : id ∈ GeneralNominalState.sources s.core.erased.current.context.state) :
    Inert (GeneralNominalVersionedRefresh232.refresh s (GeneralVersionedHarmlessRefresh312.add ctx id)) id ↔ Inert s id :=
  by
    have equiv := not_congr (observation (key := id)
      (.refresh s _ (GeneralVersionedHarmlessRefresh312.certificate old already)))
    exact Classical.not_not.symm.trans (equiv.trans Classical.not_not)

/-- A redundant raw mention of a known name needs no ledger record if the
name was inert at the earlier checkpoint and is not an actual report read. -/
theorem harmless_not_protected {s : State roles} {ctx : GeneralNominalCandidates.Context} {id : Nat}
    {p : Packet roles}
    (old : GeneralNominalVersionedMixedObservations233.Refresh s ctx)
    (already : id ∈ GeneralNominalState.sources s.core.erased.current.context.state)
    (inert : Inert s id) (unread : id ∉ reportPool p) :
    ¬ Active (GeneralNominalVersionedRefresh232.refresh s (GeneralVersionedHarmlessRefresh312.add ctx id)) p id :=
  fun active => active.elim (fun essential => essential ((harmless_keeps old already).mpr inert)) unread

end Yulang.GeneralVersionedEssentialAggregates313
