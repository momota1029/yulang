import Yulang.GeneralDeclarativeStoppedDepthWitness341
import Yulang.GeneralNominalVersionedJournalFrame236

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 35000
set_option maxHeartbeats 17000000
namespace Yulang.GeneralDeclarativeStoppedDepthProjection341
open GeneralDictionaryOutputDepth252 (sourceRegistry roles root interpretation source_checked coverage)
open GeneralRebaseDepthScalar285 (refreshed)
open GeneralDeclarativeStoppedDepth341 (terminal classification only_root)
open GeneralDeclarativeStoppedDepthView341 (final requested waiting current_model outRow exact_rhs)
open GeneralDeclarativeStoppedDepthWitness341 (compiled current witness declared extra)
open GeneralDeclarativeStoppedLockstep341 (CurrentNodes same_assignment)
open GeneralDeclarativeTaggedDictionary340 (Rule)
open GeneralDeclarativeFootprint321 (stateNames preserves_models)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralDeclarativeHead320 (Equation)
open CommonRoleOutermostResolver (Classify)
open CommonNominalFullCarrier (subtype_refl)

open GeneralNominalVersionedJournalFrame236 (sources models_iff)

def extend (m : Assignment) : Assignment :=
  fun name => if name = 4 ∨ name = 5 then ((m 2).1,(m name).2) else m name

theorem sources_literal :
    sources refreshed =
      GeneralDictionaryDefaultJournalSupport213.journalSources refreshed.legacy ++
      refreshed.plans.flatMap GeneralNominalVersionedPacketFrame236.sources ++
      (GeneralNominalVersionedPacketFrame236.headSources GeneralDictionaryOutputDepth252.plan.packet ++
        [3,3,2] ++ [3,3,2]) := by
  have kept : refreshed.effects = [GeneralDictionaryOutputDepthInstall252.effect] := rfl
  have old : GeneralNominalCenteredHeadOutputs.requests
      GeneralDictionaryOutputDepthInstall252.effect.snapshot root = [⟨0,3⟩] :=
    GeneralDeclarativeStoppedRetarget340.only_site_requests
      (s := GeneralDictionaryOutputDepthInstall252.effect.snapshot)
      (focus := root) (site := GeneralNominalDemandMerging.pointSite root) rfl (.refl _)
  unfold sources
  rw [kept,List.flatMap_cons,List.flatMap_nil,List.append_nil]
  unfold GeneralNominalVersionedJournalFrame236.effectSources
  unfold GeneralDictionaryDefault214ActualBodyFrame.classSources
  have here : GeneralDictionaryOutputDepthInstall252.effect.plan.packet.site.occurrence = root := rfl
  rw [here,old,GeneralDeclarativeStoppedRetarget340.exact_requests]
  with_unfolding_all rfl

theorem fresh4 : 4 ∉ sources refreshed := by
  rw [sources_literal]
  with_unfolding_all decide +kernel
theorem fresh5 : 5 ∉ sources refreshed := by
  rw [sources_literal]
  with_unfolding_all decide +kernel
theorem view_fresh4 : 4 ∉ stateNames final := by decide +kernel
theorem view_fresh5 : 5 ∉ stateNames final := by decide +kernel

theorem source_same (m : Assignment) (n : Nat) (seen : n ∈ sources refreshed) :
    extend m n = m n := by
  have h4 : n ≠ 4 := fun h => fresh4 (h ▸ seen)
  have h5 : n ≠ 5 := fun h => fresh5 (h ▸ seen)
  simp [extend,h4,h5]

theorem preserve_raw (fit : Models refreshed m) : Models refreshed (extend m) :=
  (models_iff refreshed (fun n seen => (source_same m n seen).symm)).mp fit

theorem preserve_view (m : Assignment) (n : Nat) (seen : n ∈ stateNames final) :
    extend m n = m n := by
  have h4 : n ≠ 4 := fun h => view_fresh4 (h ▸ seen)
  have h5 : n ≠ 5 := fun h => view_fresh5 (h ▸ seen)
  simp [extend,h4,h5]

theorem extends_ordinary (fit : Models refreshed m) :
    GeneralDeclarativeHead320.Models compiled (extend m) := by
  have old := (preserves_models final (first := extend m) (last := m)
    (fun n seen => preserve_view m n seen)).mpr (current_model m fit)
  refine ⟨⟨(PresenceNormalForm.all_append _ _ _ _).mpr ⟨old.1.1,?_⟩, old.1.2⟩,old.2⟩
  intro atom found
  simp only [extra,List.mem_cons,List.not_mem_nil,or_false] at found
  rcases found with h|h|h|h|h|h|h|h <;> cases ‹_› <;>
    simpa [PresenceNormalForm.Atom.Holds,Core.PresenceGeneration.TyTerm.eval,CommonNominalFullCarrier.model,extend] using subtype_refl (m 2).1

def placed (_ : GeneralSourceDictionaries.Occurrence roles) := requested

theorem each (done : Nat → Prop) :
    CurrentNodes sourceRegistry refreshed root placed
      (Rule (current done) [] sourceRegistry interpretation waiting) := by
  intro a live key kids pick
  cases only_root live
  have same := GeneralNominalVersionedMixedSourceBoundary234.local_functional pick
    GeneralRebaseDepthHaltSelection285.selected
  cases same
  exact .whole (witness done)

/-- The actual request-bearing stop and modern source judgment
agree on the same dictionary, using one assignment equal on
the entire old raw journal footprint. Actual fixed output target 3
and binder 2 are unchanged. New ordinary names 4/5 are not sources. -/
theorem actual (done : Nat → Prop) (m : Assignment) (fit : Models refreshed m) :
    Classify (Rule (current done) [] sourceRegistry interpretation waiting) requested (.selected (.node 0 [])) ∧
      ∃ n, Models refreshed n ∧ (∀ id ∈ sources refreshed, n id = m id) ∧
        GeneralNominalVersionedEvidence231.Evidence
          (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry) refreshed.core n root (.node 0 []) ∧
        GeneralDeclarativeExactDictionary337.Evidence sourceRegistry interpretation n requested (.node 0 []) ∧
        GeneralDeclarativeEntailment320.Holds n outRow := by
  have raw := preserve_raw fit
  have ordinary := extends_ordinary fit
  obtain ⟨select,both⟩ := same_assignment terminal (each done) classification coverage declared
    raw ⟨ordinary,fun _ z => False.elim (List.not_mem_nil z)⟩
  have output := (current_model _ raw).2 _ (List.mem_append_right _ List.mem_cons_self)
  exact ⟨select,extend m,raw,source_same m,both.1,both.2,output⟩

end Yulang.GeneralDeclarativeStoppedDepthProjection341
