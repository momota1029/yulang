import Yulang.GeneralDictionaryRefinedLocations
import Yulang.GeneralNominalKnownBit304

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalTotalLocation304
open GeneralNominalRefinements (Refines)
open GeneralDictionaryBinderLocations (sourceSlot)
open GeneralNominalRecursiveCandidates (Context arguments)
open GeneralNominalKnownBit304 (knownBit known_exact)
open GeneralSourceDictionaries (Occurrence)

variable {before after : GeneralNominalState.State}

theorem roundtrip (forward : Refines before after) (inverse : Refines after before)
    (slot : Fin before.base.slots) : inverse.base.embed (forward.base.embed slot) = slot :=
  before.base.source_injective
    ((inverse.base.source (forward.base.embed slot)).trans (forward.base.source slot))

theorem source_total (forward : Refines before after) (inverse : Refines after before) (id : Nat) :
    sourceSlot after.base id = (sourceSlot before.base id).map forward.base.embed := by
  cases found : sourceSlot before.base id with
  | some slot => exact GeneralDictionaryRefinedLocations.source_slot before.base after.base forward.base id slot found
  | none =>
    cases h : sourceSlot after.base id with
    | none => rfl
    | some slot =>
      have opposite := GeneralDictionaryRefinedLocations.source_slot after.base before.base inverse.base id slot h
      rw [found] at opposite
      cases opposite

theorem arguments_total (before after : Context) (forward : Refines before.state after.state)
    (inverse : Refines after.state before.state) (root : Occurrence roles) :
    arguments after root = (arguments before root).map
      (List.map fun b => (forward.base.embed b.1,forward.base.embed b.2)) := by
  cases found : arguments before root with
  | some bounds => exact GeneralDictionaryRefinedLocations.arguments before after forward root bounds found
  | none =>
    cases h : arguments after root with
    | none => rfl
    | some bounds =>
      have opposite := GeneralDictionaryRefinedLocations.arguments after before inverse root bounds h
      rw [found] at opposite
      cases opposite

theorem known_reindex (forward : Refines before after) (inverse : Refines after before) (id : Nat) :
    knownBit before id = knownBit after id := by
  cases a : knownBit before id <;> cases b : knownBit after id
  · rfl
  · cases a.symm.trans ((known_exact ..).mpr (inverse.known _ ((known_exact ..).mp b)))
  · cases b.symm.trans ((known_exact ..).mpr (forward.known _ ((known_exact ..).mp a)))
  · rfl

inductive SlotStatus where
  | missing
  | unresolved
  | known
  deriving BEq, DecidableEq, Repr

def status (s : GeneralNominalState.State) (id : Nat) : SlotStatus :=
  if (sourceSlot s.base id).isSome then
    if knownBit s id then .known else .unresolved
  else .missing

theorem status_reindex (forward : Refines before after) (inverse : Refines after before) (id : Nat) :
    status before id = status after id := by
  unfold status
  rw [source_total forward inverse,← known_reindex forward inverse]
  cases sourceSlot before.base id <;> rfl

theorem status_missing_iff (s : GeneralNominalState.State) (id : Nat) :
    status s id = .missing ↔ ¬ ∃ slot, s.base.source slot = id := by
  unfold status
  cases h : sourceSlot s.base id with
  | none =>
    refine ⟨?_,fun _ => rfl⟩
    rintro _ ⟨i,source⟩
    have slot := (GeneralDictionaryBinderLocations.sourceSlot_exact s.base id i).mpr source
    rw [h] at slot
    cases slot
  | some slot =>
    constructor
    · simp only [Option.isSome_some,ite_true]
      split <;> intro impossible <;> cases impossible
    · intro missing
      exact False.elim (missing ⟨slot,(GeneralDictionaryBinderLocations.sourceSlot_exact s.base id slot).mp h⟩)

theorem status_known_iff (s : GeneralNominalState.State) (id : Nat) :
    status s id = .known ↔ GeneralNominalState.Known s id := by
  unfold status
  cases h : sourceSlot s.base id with
  | none =>
    constructor
    · intro impossible; simp at impossible
    · rintro ⟨i,source,_⟩
      have slot := (GeneralDictionaryBinderLocations.sourceSlot_exact s.base id i).mpr source
      rw [h] at slot
      cases slot
  | some slot =>
    simp [(known_exact s id).symm]

theorem status_unresolved_iff (s : GeneralNominalState.State) (id : Nat) :
    status s id = .unresolved ↔ (∃ slot, s.base.source slot = id) ∧ ¬ GeneralNominalState.Known s id := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · by_cases found : ∃ slot, s.base.source slot = id
      · exact found
      · have missing := (status_missing_iff s id).mpr found
        rw [h] at missing
        contradiction
    · intro known
      have yes := (status_known_iff s id).mpr known
      rw [h] at yes
      contradiction
  · rintro ⟨slot,unknown⟩
    cases eq : status s id
    · exact False.elim ((status_missing_iff s id).mp eq slot)
    · rfl
    · exact False.elim (unknown ((status_known_iff s id).mp eq))

end Yulang.GeneralNominalTotalLocation304
