import Yulang.GeneralDeferredLadderAdvance302

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 8000000
namespace Yulang.GeneralDeferredLadderRefresh302
open GeneralDeferredLadderLedger302
open GeneralDeferredLadderReport302 (context)
open GeneralObservedLadderRoute301 (focus)
open GeneralObservedLadderRefresh301 (refined atomTail before)
open GeneralObservedLadderSource301 (endpoint)
open GeneralNominalIdentities (source)
open GeneralNominalRefinements (Refines)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalExamples (registry displayRoot)
open GeneralDeclarationExamples (roles)
open GeneralNominalCommonBridge (Assignment)

abbrev promotedContext (p : Phase n k) :=
  GeneralDictionaryOrdinaryTransport.extend (refined n) (p.keys.map (source (n+1))) p.extraAtoms p.keys

abbrev promoted (p : Phase n k) := refresh p.state (promotedContext p)

def refines (p : Phase n k) : Refines (env p).state (promotedContext p).state := by
  let first := GeneralObservedLadderRefresh301.refinement n
  refine ⟨first.base,first.heads,first.nominals,?_,first.known,?_,?_,rfl,rfl⟩
  · intro atom seen
    exact seen
  · intro id seen
    exact seen
  · intro key seen
    exact seen

theorem same_models (p : Phase n k) (m : Assignment) :
    GeneralNominalState.Models (promotedContext p).state m ↔ GeneralNominalState.Models (env p).state m := by
  change GeneralNominalState.Models (GeneralDictionaryOrdinaryTransport.extendState
    (refined n).state (p.keys.map (source (n+1))) p.extraAtoms p.keys) m ↔
    GeneralNominalState.Models (GeneralDictionaryOrdinaryTransport.extendState
      (context n).state (p.keys.map (source (n+1))) p.extraAtoms p.keys) m
  rw [GeneralDictionaryOrdinaryTransport.models_extended p.keys (p.keys.map (source (n+1))) p.extraAtoms (refined n).state m,
    GeneralDictionaryOrdinaryTransport.models_extended p.keys (p.keys.map (source (n+1))) p.extraAtoms (context n).state m,
    GeneralObservedLadderRefresh301.target_models]

theorem cache (p : Phase n k) :
    GeneralNominalVersionedMixedObservations233.CacheSound p.state (promotedContext p).state := by
  intro observation seen
  refine ⟨[],[],.source,.source,?_⟩
  intro m _ sourceFacts
  have held := sourceFacts.1
  rw [p.source_eq] at held
  have full : GeneralNominalState.Models (promotedContext p).state m :=
    (GeneralDictionaryOrdinaryTransport.models_extended ..).mpr
      ⟨(GeneralObservedLadderRefresh301.target_models n m).mpr held,p.extra_models m⟩
  exact GeneralCanonicalObservations.recorded_sound _ m full seen

def certificate (p : Phase n k) : Refresh p.state (promotedContext p) := by
  refine ⟨p.context_eq.symm ▸ refines p,?_,?_,?_,cache p⟩
  · rw [p.context_eq]
    rfl
  · intro id member
    rw [p.context_eq]
    exact member
  · intro m valid
    have held := valid.1.1
    rw [p.context_eq] at held
    have there := (same_models p m).mpr held
    exact ⟨there.1,there.2.2⟩

theorem tracked_terminal (p : Phase n k) :
    n+1 ∈ GeneralNominalState.sources p.state.core.erased.current.context.state := by
  rw [p.context_eq]
  exact GeneralNominalAllocationSupport.slot_source (env p).state (endpoint n)

theorem unknown (p : Phase n k) :
    ¬ GeneralNominalState.Known p.state.core.erased.current.context.state (n+1) := by
  rw [p.context_eq]
  exact GeneralObservedLadderRefresh301.endpoint_unknown n

theorem strict (p : Phase n k) :
    GeneralNominalState.Known (promotedContext p).state (n+1) :=
  GeneralObservedLadderRefresh301.known_target n _ (Nat.le_refl _)

theorem actual (p : Phase n k) : (boundary roles).Step registry displayRoot p.state (promoted p) :=
  ⟨displayRoot,.root,.refresh displayRoot (promotedContext p) (certificate p) (n+1)
    (tracked_terminal p) (unknown p) (strict p)⟩

theorem retained_models (p : Phase n k) (m : Assignment) : Models (promoted p) m ↔ Models p.state m :=
  GeneralNominalVersionedMixedObservations233.refresh_models (certificate p)

theorem promoted_context_eq (p : Phase n k) :
    (promoted p).core.erased.current.context =
      GeneralDictionaryOrdinaryTransport.extend (GeneralObservedLadderInitial301.context n)
        (p.keys.map (source (n+1))) (atomTail n ++ p.extraAtoms) p.keys := rfl

theorem generated_preserved (p : Phase n k) {root leaf : GeneralSourceDictionaries.Occurrence roles}
    (prior : GeneralNominalSaturationState.Generated p.state.core.erased.current root leaf) :
    GeneralNominalSaturationState.Generated (promoted p).core.erased.current root leaf := by
  have aliases {a b : Nat} (old : GeneralNominalSaturationState.Alias p.state.core.erased.current a b) :
      GeneralNominalSaturationState.Alias (promoted p).core.erased.current a b := by
    induction old with
    | refl => exact .refl _
    | edge seen => exact .edge seen
    | symm _ ih => exact .symm ih
    | trans _ _ i j => exact .trans i j
  induction prior with
  | root => exact .root
  | child _ edge ih => exact .child ih edge
  | alias _ seen other same ih => exact .alias ih seen other (aliases same)

def promotedPhase (p : Phase n k) : GeneralObservedLadderLedger301.Phase n k where
  state := promoted p
  keys := p.keys
  extraAtoms := atomTail n ++ p.extraAtoms
  context_eq := promoted_context_eq p
  centers_eq := p.centers_eq
  raw_eq := p.raw_eq
  edges_eq := p.edges_eq
  old_keys := p.old_keys
  atom_support := by
    intro a seen
    rw [List.flatMap_append] at seen
    rcases List.mem_append.mp seen with sourcePart|extra
    · rw [GeneralObservedLadderRefreshChain301.outer_atoms] at sourcePart
      exact Nat.le_of_eq (by simpa [GeneralNominalState.atomSources,GeneralNominalState.typeSources] using sourcePart)
    · exact p.atom_support a extra
  focus_generated := by
    exact generated_preserved p p.focus_generated
  packets_display := p.packets_display
  legacy_empty := p.legacy_empty
  models := fun m => ((retained_models p m).trans (p.models m)).trans
    (GeneralObservedLadderRefreshChain301.before_models n m)
  reached := by
    obtain ⟨s,ini,path⟩ := p.reached
    exact ⟨s,ini,.tail path (actual p)⟩

end Yulang.GeneralDeferredLadderRefresh302
