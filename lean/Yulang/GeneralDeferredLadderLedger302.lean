import Yulang.GeneralObservedLadderRoute301
import Yulang.GeneralDeferredLadderSemantics302

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderLedger302
open GeneralObservedLadderRefresh301 (before initial atomTail)
open GeneralDeferredLadderReport302 (context snapshot display_report)
open GeneralObservedLadderReport301 (point)
open GeneralDeferredLadderPlan302
open GeneralObservedLadderRoute301
open GeneralDeclarationExamples (roles display)
open GeneralNominalExamples (registry displayRoot)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedPlans231 (Holds)
open GeneralNominalVersionedTransport231 (extendedPlan extendedPacket)
open GeneralNominalVersionedInstallation231 (reserved allocated atoms)
open GeneralNominalIdentities (Origin source)
open PresenceNormalForm (Atom)
open GeneralNominalCommonBridge (Assignment)

structure Phase (n k : Nat) where
  state : State roles
  keys : List Origin
  extraAtoms : List (Atom Nat)
  context_eq : state.core.erased.current.context = GeneralDictionaryOrdinaryTransport.extend
    (context n) (keys.map (source (n+1))) extraAtoms keys
  source_eq : state.core.erased.source = context n
  extra_models : ∀ m, PresenceNormalForm.All CommonNominalFullCarrier.model m extraAtoms
  centers_eq : state.core.sites = sites n k
  raw_eq : state.core.erased.current.sites = (sites n k).map GeneralNominalCenters.Site.observed
  edges_eq : state.core.erased.current.edges = edges n k
  old_keys : ∀ key ∈ keys, ∃ i, i < k ∧ key.1 = invocation n i
  atom_support : ∀ a ∈ extraAtoms.flatMap GeneralNominalState.atomSources, a ≤ n+1
  focus_generated : GeneralNominalSaturationState.Generated state.core.erased.current displayRoot (focus n k)
  packets_display : ∀ prior ∈ state.core.erased.current.packets, prior.declaration.id = 1
  legacy_empty : state.legacy.effects = []
  models : ∀ m, Models state m ↔ Models (before n) m
  reached : B4TargetV8.Reachable (boundary roles) registry displayRoot state

def start (n : Nat) : Phase n 0 where
  state := before n
  keys := []
  extraAtoms := []
  context_eq := rfl
  source_eq := rfl
  extra_models := fun m => PresenceNormalForm.all_nil _ m
  centers_eq := rfl
  raw_eq := rfl
  edges_eq := rfl
  old_keys := by intro _ impossible; cases impossible
  atom_support := by intro _ impossible; cases impossible
  focus_generated := .root
  packets_display := by intro _ impossible; cases impossible
  legacy_empty := rfl
  models := fun _ => Iff.rfl
  reached := ⟨_,initial n,.refl⟩

abbrev env (p : Phase n k) := GeneralDictionaryOrdinaryTransport.extend
    (context n) (p.keys.map (source (n+1))) p.extraAtoms p.keys

abbrev basePlan (n k : Nat) (hi : k ≤ n) := plan n k (invocation n k) hi

abbrev stagePlan (p : Phase n k) (hi : k ≤ n) :=
  extendedPlan (p.keys.map (source (n+1))) p.extraAtoms p.keys (basePlan n k hi)

theorem stage_held (p : Phase n k) (hi : k ≤ n) (m : Assignment) (held : Models p.state m) :
    Holds (stagePlan p hi) m := by
  have whole := held.1.1
  rw [p.context_eq] at whole
  obtain ⟨old,added⟩ := (GeneralDictionaryOrdinaryTransport.models_extended ..).mp whole
  exact (GeneralNominalVersionedTransport231.holds_iff ..).mpr
    ⟨GeneralDeferredLadderSemantics302.holds n k (invocation n k) hi m old,added⟩

theorem stage_bindings (p : Phase n k) (hi : k ≤ n) :
    (stagePlan p hi).packet.bindings = [(0,(k+1,k+1))] :=
  (GeneralNominalVersionedTransport231.packet_bindings ..).trans (bindings n k (invocation n k) hi)

theorem stage_atoms (p : Phase n k) (hi : k ≤ n) :
    atoms (stagePlan p hi).packet =
      [.tyLe (.var (k+1)) (.var (k+1)),.tyLe (.var k) (.var k),
       .tyLe (.var k) (.var k),.tyLe (.var (k+1)) (.var (k+1))] := by
  unfold atoms
  rw [stage_bindings p hi]
  change _ ++ GeneralNominalRecursiveInspection.selfChecks _ (GeneralNominalRecursiveCandidates.report
    (env p) display [point n k (by omega)]) = _
  rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended,
    GeneralDictionaryOrdinaryTransport.selfChecks_report,display_report n k hi]
  rfl

theorem stage_atom_models (p : Phase n k) (hi : k ≤ n) (m : Assignment) :
    PresenceNormalForm.All CommonNominalFullCarrier.model m (atoms (stagePlan p hi).packet) := by
  rw [stage_atoms p hi]
  intro atom member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl <;> exact CommonNominalFullCarrier.subtype_refl _

theorem stage_supported (p : Phase n k) (hi : k ≤ n) (a : Nat)
    (hit : a ∈ (atoms (stagePlan p hi).packet).flatMap GeneralNominalState.atomSources) :
    a ≤ n+1 := by
  rw [stage_atoms p hi] at hit
  have one : a = k ∨ a = k+1 := by
    simpa [GeneralNominalState.atomSources,GeneralNominalState.typeSources,or_assoc,or_comm,or_left_comm] using hit
  rcases one with rfl|rfl <;> omega

theorem support (p : Phase n k) (a : Nat) (hit : a ∈ GeneralNominalState.sources (env p).state) :
    a ≤ n+1 ∨ a ∈ p.keys.map (source (n+1)) := by
  change a ∈ List.ofFn (Fin.val : Fin (n+2) → Nat) ++ List.ofFn (Fin.val : Fin (n+2) → Nat) ++
    ([] ++ p.keys.map (source (n+1))) ++ (atomTail n ++ p.extraAtoms).flatMap GeneralNominalState.atomSources at hit
  simp only [List.nil_append,List.mem_append] at hit
  rcases hit with ((typ|row)|res)|ordinary
  · obtain ⟨slot,eq⟩ := List.mem_ofFn.mp typ
    exact .inl (eq ▸ Nat.le_of_lt_succ slot.isLt)
  · obtain ⟨slot,eq⟩ := List.mem_ofFn.mp row
    exact .inl (eq ▸ Nat.le_of_lt_succ slot.isLt)
  · exact .inr res
  · rw [List.flatMap_append] at ordinary
    rcases List.mem_append.mp ordinary with sourceAtom|new
    · rw [GeneralObservedLadderRefreshChain301.outer_atoms] at sourceAtom
      have atEnd : a = n+1 := by
        simpa [GeneralNominalState.atomSources,GeneralNominalState.typeSources] using sourceAtom
      exact .inl (Nat.le_of_eq atEnd)
    · exact .inl (p.atom_support a new)

theorem fresh (p : Phase n k) (bs) :
    GeneralNominalVersionedAllocation231.Fresh (env p).state compiled (invocation n k) bs := by
  intro key member collides
  rcases support p _ collides with low|old
  · exact False.elim (Nat.not_lt_of_ge low (GeneralNominalIdentities.source_above_seed (n+1) key))
  · obtain ⟨other,inKeys,eq⟩ := List.mem_map.mp old
    obtain ⟨i,before,owner⟩ := p.old_keys other inKeys
    have sameKey := (GeneralNominalIdentities.source_identity (n+1) other key).mp eq
    have allocOwner := GeneralRebaseDisplayChildFresh276.keys_root member
    have eqIds := owner.symm.trans ((congrArg Prod.fst sameKey).trans allocOwner)
    exact False.elim (Nat.ne_of_lt (strictly_monotone n before) eqIds)

end Yulang.GeneralDeferredLadderLedger302
