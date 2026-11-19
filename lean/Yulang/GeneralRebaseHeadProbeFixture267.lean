import Yulang.GeneralRebaseSourceClassification267
import Yulang.GeneralRebaseCandidateFixture267

set_option maxRecDepth 12000
set_option maxHeartbeats 2500000
namespace Yulang.GeneralRebaseHeadProbeFixture267
open GeneralNominalCenters (Plan)
open GeneralDictionaryCompoundFrame238 (before)
open GeneralDictionaryCompoundPacket238 (plan packet)
open GeneralDictionaryCompoundSource238 (registry sourceRegistry declaration)
open GeneralDictionaryJournalRefinement228Source (root roles context)
open GeneralRebaseCandidateFixture267 (checked inferred_exact)
open GeneralRebaseHeadProbe267 (atFocus Honest)
open GeneralRebaseSourceClassification267 (verdict)

noncomputable def entries := atFocus registry before root root checked

theorem entry_count : entries.length = 1 := by decide +kernel

theorem actual_ready : plan ∈ entries := by
 have localChecked : (GeneralRebaseSourceSurvivor267.Boundary roles).Checked sourceRegistry :=
   ⟨rfl,GeneralDictionaryCompoundSource238.checked⟩
 obtain ⟨candidate,present,focus,_,_,_⟩ :=
   GeneralRebaseSourceSurvivor267.from_survivor sourceRegistry before root root localChecked
      GeneralDictionaryCompoundStep238.initial_reachable .root GeneralDictionaryCompoundFrame238.survivor
 have planMember : candidate ∈ GeneralRebaseCandidateFixture267.inferred :=
   ((GeneralRebaseCandidatePrepared267.ready_exact ..).mp present).1 |> (GeneralRebaseEnumeratePlans267.plans_exact ..).mpr
 rw [inferred_exact] at planMember
 cases List.mem_singleton.mp planMember
 exact (GeneralRebaseHeadProbe267.atFocus_exact ..).mpr ⟨present,focus⟩

theorem entries_exact : entries = [plan] := by
 have one := entry_count
 cases h : entries with
 | nil => simp [h] at one
 | cons x xs =>
   have empty : xs = [] := by simpa [h] using one
   subst xs
   have equal := List.mem_singleton.mp (h ▸ actual_ready)
   cases equal
   rfl

def certifiedCase (_ : Plan roles) : Option Bool := some true

/-- This fixture uses the existing explicit head-model proof for the sole
discovered plan; it does not implement a general model solver. -/
theorem certifiedCase_honest : Honest certifiedCase entries := by
 constructor
 · intro candidate present _
   rw [entries_exact] at present
   cases List.mem_singleton.mp present
   exact ⟨GeneralDictionaryCompoundVersionedModel238.extended,GeneralDictionaryCompoundVersionedPacket238.head_model⟩
 · intro _ _ result
   cases result

theorem verified_choice :
 verdict certifiedCase entries = .unique (declaration.id,GeneralNominalVersionedFrame231.children packet) := by
 rw [entries_exact]
 rfl

theorem no_model_probe_stays_deferred : verdict (fun _ => none) entries = .deferred := by
 rw [entries_exact]
 rfl

end Yulang.GeneralRebaseHeadProbeFixture267
