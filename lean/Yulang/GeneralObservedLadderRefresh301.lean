import Yulang.GeneralObservedLadderSemanticGap301

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25000
set_option maxHeartbeats 8000000
namespace Yulang.GeneralObservedLadderRefresh301
open GeneralObservedLadderSemanticGap301 (equationOnly same_models)
open GeneralObservedLadderSource301 (snapshot endpoint)
open GeneralObservedLadderInitial301 (context labels ground actual_initial)
open GeneralNominalExamples (registry displayRoot)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRefinements (Refines renameDescriptor renameParameter)
open GeneralNominalGroundAccessibility (GroundRoots)
open GeneralNominalState (Known)
open GeneralNominalVersionedRefresh232 (refresh)

abbrev before (n : Nat) := GeneralNominalVersionedJournal232.initial (equationOnly n) displayRoot

abbrev atomTail (n : Nat) := (equationOnly n).state.ordinary

abbrev refined (n : Nat) : GeneralNominalCandidates.Context :=
  GeneralDictionaryOrdinaryTransport.extend (context n) [] (atomTail n) []

abbrev after (n : Nat) := refresh (before n) (refined n)

theorem initial (n : Nat) : (boundary roles).Initial registry displayRoot (before n) := by
  have semantic : GroundRoots (equationOnly n) displayRoot (labels n) := by
    obtain ⟨arity,held⟩ := ground n
    refine ⟨arity,?_⟩
    intro i
    obtain ⟨t,closed,models⟩ := held i
    exact ⟨t,closed,fun m valid => models m ((same_models n m).mp valid)⟩
  refine ⟨_,⟨equationOnly n,labels n,GeneralNominalPeelingSources.initial_source n,
    (fun _ => rfl),semantic,GeneralNominalCenteredHeadWFFixtures.display_coverage,rfl⟩,rfl⟩

theorem known_target (n a : Nat) (low : a ≤ n+1) : Known (refined n).state a := by
  refine ⟨GeneralObservedLadderReport301.pos n a low,rfl,?_⟩
  by_cases inner : a ≤ n
  · exact .inr ⟨_,GeneralObservedLadderSource301.nominal_at n a inner⟩
  · left
    have last : a = n+1 := by omega
    subst a
    change ((snapshot n).view.heads (endpoint n)).node ≠ .unresolved
    rw [GeneralObservedLadderSource301.scalar_at]
    intro no
    cases no

theorem target_support (n a : Nat) (hit : a ∈ GeneralNominalState.sources (refined n).state) :
    a ∈ GeneralNominalState.sources (equationOnly n).state := by
  exact hit

def refinement (n : Nat) : Refines (equationOnly n).state (refined n).state := by
  refine ⟨⟨id,(fun _ => rfl),(fun _ => rfl),?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,rfl,rfl⟩
  · intro atom none; cases none
  · intro slot no; exact False.elim (no rfl)
  · intro pair none; cases none
  · intro slot term no; cases no
  · intro slot desc seen
    have unchanged : (refined n).state.nominals slot = some desc := seen
    have same : renameDescriptor id desc = desc := by
      have ident : renameParameter (id : Fin (n+2) → Fin (n+2)) = id := by
        funext x
        cases x <;> rfl
      cases desc
      simp [renameDescriptor,ident]
    change (refined n).state.nominals slot = some (renameDescriptor id desc)
    rw [same]
    exact unchanged
  · intro atom hit
    exact hit
  · rintro a ⟨slot,id,_⟩
    apply known_target n a
    have low := slot.isLt
    change slot.val = a at id
    change slot.val < n+2 at low
    omega
  · intro a no; cases no
  · intro key no; cases no

theorem target_models (n : Nat) (m : Assignment) :
    GeneralNominalState.Models (refined n).state m ↔ GeneralNominalState.Models (equationOnly n).state m := by
  constructor
  · exact GeneralNominalRefinements.models (refinement n) m
  · intro good
    exact (GeneralDictionaryOrdinaryTransport.models_extended ..).mpr
      ⟨(same_models n m).mp good,good.2.2⟩

theorem cache (n : Nat) : GeneralNominalVersionedMixedObservations233.CacheSound (before n) (refined n).state := by
  intro observation seen
  refine ⟨[],[],.source,.source,?_⟩
  intro m _ sourceFacts
  have source : GeneralNominalState.Models (equationOnly n).state m := sourceFacts.1
  exact GeneralCanonicalObservations.recorded_sound _ m ((target_models n m).mpr source) seen

def certificate (n : Nat) : Refresh (before n) (refined n) := by
  refine ⟨refinement n,rfl,target_support n,?_,cache n⟩
  intro m only
  have source := ((GeneralNominalVersionedJournal232.initial_models ..).mp only).1
  have valid := (target_models n m).mpr source
  exact ⟨valid.1,valid.2.2⟩

theorem endpoint_unknown (n : Nat) : ¬ Known (equationOnly n).state (n+1) := by
  rintro ⟨slot,located,head|⟨d,seen⟩⟩
  · exact head rfl
  · have same : slot = endpoint n := Fin.ext located
    subst slot
    rw [(GeneralObservedLadderSemanticGap301.unresolved n).1] at seen
    cases seen

theorem actual (n : Nat) : (boundary roles).Step registry displayRoot (before n) (after n) := by
  refine ⟨displayRoot,.root,.refresh displayRoot (refined n) (certificate n) (n+1) ?_ ?_ ?_⟩
  · exact GeneralNominalAllocationSupport.slot_source (equationOnly n).state (endpoint n)
  · exact endpoint_unknown n
  · exact known_target n (n+1) (Nat.le_refl _)

theorem refresh_models (n : Nat) (m : Assignment) : Models (after n) m ↔ Models (before n) m :=
  GeneralNominalVersionedMixedObservations233.refresh_models (certificate n)

theorem receipt_changes (n : Nat) :
    GeneralObservedLadderJournalCompiler301.probe (equationOnly n) [GeneralObservedLadderSemanticGap301.terminalPoint n] = none ∧
      GeneralObservedLadderJournalCompiler301.probe (refined n)
        [GeneralObservedLadderReport301.point n (n+1) (Nat.le_refl _)] = some ⟨3,[]⟩ := by
  refine ⟨GeneralObservedLadderSemanticGap301.no_observation n,?_⟩
  unfold GeneralObservedLadderJournalCompiler301.probe
  rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended,
    GeneralDictionaryOrdinaryTransport.candidate_report_extended,GeneralObservedLadderReport301.int_as_list,
    GeneralObservedLadderReport301.int_report]
  rfl

end Yulang.GeneralObservedLadderRefresh301
