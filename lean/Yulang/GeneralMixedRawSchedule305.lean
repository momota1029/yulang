import Yulang.GeneralMixedRawFanout305
import Yulang.GeneralRebaseDepthPathSharp285

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 17000000
namespace Yulang.GeneralMixedRawSchedule305
open GeneralDictionaryOutputDepth252 (roles registry root)
open GeneralDictionaryOutputDepthInstall252 (installed)
open GeneralRebaseDepthScalar285 (from_source present new_one)
open GeneralRebaseDepthPathSharp285 (halfway cert_both first no_one_half)
open GeneralRebaseDepthPathRank285 (ActualPath all_after_install)
open GeneralMixedReindexOutputFixture305 (wide widened coordinates other_refresh)
open GeneralMixedReindexOutputHalt305 (widened_halted)
open GeneralMixedRawFanout305 (firstTag firstTag_widened bounded_tags)
open GeneralMixedReindexOutputCompiler305 (bits widened_valid actual_run)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralMixedDiagnosticHead304 (boundary8)

noncomputable def lastCert (n : Nat) : Refresh halfway (wide n) := by
  let oldR := cert_both.refines
  refine ⟨⟨oldR.base,oldR.heads,oldR.nominals,oldR.ordinary,
    fun id was => (coordinates n).forward.known id (oldR.known id was),
    oldR.reserved,oldR.allocated,oldR.seed,oldR.constructors⟩,
    cert_both.interpretation,cert_both.support,cert_both.constraints,?_⟩
  intro observation recorded
  exact ⟨[],[],.source,.source,fun m _ supported =>
    GeneralCanonicalObservations.recorded_sound (wide n).state m
      ((GeneralNominalReportContext305.model_iff (coordinates n) m).mp
        (from_source m supported.1)) recorded⟩

theorem early : Step registry root installed halfway :=
  (GeneralRebaseDepthPathRank285.exact GeneralRebaseDepthPathAnchor285.initial
    GeneralRebaseDepthPathKeep285.start).mpr first

theorem from_halfway (n : Nat) : Step registry root halfway (widened n) :=
  ⟨root,.root,.refresh root (wide n) (lastCert n) 1 (present 1 (by decide)) no_one_half
    ((coordinates n).forward.known 1 new_one)⟩

theorem lengths_realized (n : Nat) :
    ActualPath installed (widened n) 1 ∧ ActualPath installed (widened n) 2 :=
  ⟨.more (.empty _) (other_refresh n),.more (.more (.empty _) early) (from_halfway n)⟩

theorem exact_possible_lengths (n len : Nat) :
    ActualPath installed (widened n) len ↔ len = 1 ∨ len = 2 := by
  constructor
  · intro valid
    have bound := (all_after_install valid).1
    have nonzero : len ≠ 0 := by
      intro zero
      subst len
      cases valid
    omega
  · rintro (rfl|rfl)
    · exact (lengths_realized n).1
    · exact (lengths_realized n).2

theorem finite_fanout_fails_after_early (enumerated : List (State roles)) :
    ∃ next, next ∉ enumerated ∧ Step registry root installed next ∧
      Step registry root halfway next ∧ (∀ after, ¬ Step registry root next after) ∧
      GeneralRebaseDiagnosticData268.Valid (boundary8 roles) registry next root bits := by
  let tags := enumerated.map firstTag
  let n := tags.foldr Nat.max 0 + 1
  refine ⟨widened n,?_,other_refresh n,from_halfway n,widened_halted n,widened_valid n⟩
  intro member
  have memory : n ∈ tags := by
    change n ∈ enumerated.map firstTag
    rw [← firstTag_widened n]
    exact List.mem_map_of_mem member
  exact Nat.not_succ_le_self _ (bounded_tags memory)

end Yulang.GeneralMixedRawSchedule305
