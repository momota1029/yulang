import Yulang.GeneralRebaseSignedObserver297
import Yulang.GeneralRebaseSliceJournal283

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseSignedSupport297
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralRebaseSignedModels297 (Conditions Sign Test)
open GeneralRebaseSliceJournal283 (journalReads)
open GeneralRebaseSourceSurvivor267 (Boundary)
open Core.PresenceGeneration (CompTerm)

noncomputable def candidateReads (s : State roles) (p : Plan roles) : List Nat :=
  GeneralNominalPacketSupport249.support (GeneralNominalRebasePacketView243.compile p CompTerm.var) ++
    GeneralNominalClassSupport249.support
      (GeneralNominalRebaseClassView243.compile s.core p.packet.site.occurrence p CompTerm.var)

def Agree (ids : List Nat) (a b : Assignment) : Prop :=
  (∀ n ∈ ids, (a n).1 = (b n).1) ∧ ∀ n, (a n).2 = (b n).2

theorem restrict {ids watched : List Nat} {a b : Assignment}
    (supports : ids ⊆ watched) (agree : Agree watched a b) : Agree ids a b :=
  ⟨fun n h => agree.1 n (supports h),agree.2⟩

theorem conditions_iff (s : State roles) (p : Plan roles) (a b : Assignment)
    (agree : Agree (candidateReads s p) a b) : Conditions s p a ↔ Conditions s p b := by
  unfold Conditions
  apply and_congr
  · have keep := GeneralNominalPacketSupport249.packet_iff
      (GeneralNominalRebasePacketView243.compile p CompTerm.var) a b agree.2
      (fun n h => agree.1 n (List.mem_append_left _ h))
    exact (GeneralNominalRebasePacketView243.compile_exact p CompTerm.var a).symm.trans
      (keep.trans (GeneralNominalRebasePacketView243.compile_exact p CompTerm.var b))
  · have keep := GeneralNominalClassSupport249.holds_iff
      (GeneralNominalRebaseClassView243.compile s.core p.packet.site.occurrence p CompTerm.var)
      a b agree.2 (fun n h => agree.1 n (List.mem_append_right _ h))
    exact (GeneralNominalRebaseClassView243.compile_exact s.core p.packet.site.occurrence p CompTerm.var a).symm.trans
      (keep.trans (GeneralNominalRebaseClassView243.compile_exact s.core p.packet.site.occurrence p CompTerm.var b))

theorem prior_iff {s : State roles} {r : Registry} {root : Occurrence roles}
    (reach : B4TargetV8.Reachable (Boundary roles) r root s) (a b : Assignment)
    (agree : Agree (journalReads s) a b) : Models s a ↔ Models s b := by
  exact (GeneralNominalRebaseJournalView243.source_exact reach CompTerm.var a).symm.trans
    ((GeneralNominalJournalSupport249.models_iff _ a b agree.2 agree.1).trans
      (GeneralNominalRebaseJournalView243.source_exact reach CompTerm.var b))

/-- When both variants already come with source model proofs, the two
answers need only candidate reads, rather than the full historical journal. -/
theorem on_prior_models (s : State roles) (p : Plan roles) (sign : Sign)
    (a b : Assignment) (oldA : Models s a) (oldB : Models s b)
    (agree : Agree (candidateReads s p) a b) :
    Test s p sign a ↔ Test s p sign b := by
  have h := conditions_iff s p a b agree
  cases sign
  · exact ⟨fun yes => ⟨oldB,h.mp yes.2⟩,fun yes => ⟨oldA,h.mpr yes.2⟩⟩
  · exact ⟨fun no => ⟨oldB,fun yes => no.2 (h.mpr yes)⟩,fun no => ⟨oldA,fun yes => no.2 (h.mp yes)⟩⟩

theorem signed_iff {s : State roles} {r : Registry} {root : Occurrence roles}
    (reach : B4TargetV8.Reachable (Boundary roles) r root s)
    (p : Plan roles) (sign : Sign) (a b : Assignment)
    (agree : Agree (journalReads s ++ candidateReads s p) a b) :
    Test s p sign a ↔ Test s p sign b := by
  have old := prior_iff reach a b (restrict (fun {_} h => List.mem_append_left _ h) agree)
  have cand := conditions_iff s p a b (restrict (fun {_} h => List.mem_append_right _ h) agree)
  cases sign
  · exact and_congr old cand
  · exact and_congr old (not_congr cand)

end Yulang.GeneralRebaseSignedSupport297
