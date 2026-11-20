import Yulang.GeneralRebaseDepthPathRank285
import Yulang.GeneralNominalVersionedMixedKernelCache234

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralMixedControlAtoms306
open GeneralDictionaryOutputDepth252 (initial registry root roles atoms)
open GeneralDictionaryOutputDepthInstall252 (installed step)
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseDepthPathAnchor285 (Anchor snapshot)
open GeneralRebaseDepthPathKeep285 (Kept)
open GeneralRebaseDepthPathRank285 (ActualPath Hop)
open GeneralNominalVersionedMixedKernelCache234 (Valid step_cache)
open GeneralNominalVersionedMixedObservations233 (legacy_cache)
open GeneralNominalRefinements (Refines)
open GeneralNominalVersionedRefresh232 (refresh)
open PresenceNormalForm (Atom)

def SourceScalar (s : GeneralNominalState.State) (n : Nat) : Prop :=
  ∃ slot : Fin s.base.slots, s.base.source slot = n ∧
    Atom.tyLe (.var slot) (.base .int) ∈ s.base.ordinary ∧
    Atom.tyLe (.base .int) (.var slot) ∈ s.base.ordinary

theorem initial_atoms (which : Fin 2) : SourceScalar (snapshot installed) which.val := by
  have small : which.val = 0 ∨ which.val = 1 := by omega
  rcases small with zero|one
  · rw [zero]
    refine ⟨(0 : Fin 4),rfl,?_,?_⟩ <;>
      change _ ∈ atoms <;> simp [atoms,GeneralSourceState.equationAtoms]
  · rw [one]
    refine ⟨(1 : Fin 4),rfl,?_,?_⟩ <;>
      change _ ∈ atoms <;> simp [atoms,GeneralSourceState.equationAtoms]

theorem atoms_preserved {s t : GeneralNominalState.State} (ref : Refines s t) {n : Nat}
    (given : SourceScalar s n) : SourceScalar t n := by
  obtain ⟨slot,source,first,last⟩ := given
  exact ⟨ref.base.embed slot,(ref.base.source slot).trans source,
    ref.base.ordinary _ first,ref.base.ordinary _ last⟩

theorem install_cache : Valid installed :=
  step_cache step (legacy_cache (GeneralDictionaryDefaultCache208.initial_valid
    GeneralDictionaryOutputDepth252.context root))

structure BasicFacts (s : State roles) : Prop where
  cache : Valid s
  origin : s.core.erased.source.state = GeneralDictionaryOutputDepth252.snapshot
  scalars : ∀ which : Fin 2, SourceScalar (snapshot s) which.val

structure ReachFacts (s : State roles) : Prop where
  anchor : Anchor s
  kept : Kept s
  basic : BasicFacts s

theorem initial_basic : BasicFacts initial :=
  ⟨legacy_cache (GeneralDictionaryDefaultCache208.initial_valid GeneralDictionaryOutputDepth252.context root),
   rfl,initial_atoms⟩

theorem refresh_basic {s : State roles} (v : BasicFacts s)
    {ctx : GeneralNominalCandidates.Context} (cert : GeneralNominalVersionedMixedObservations233.Refresh s ctx) :
    BasicFacts (refresh s ctx) :=
  ⟨GeneralNominalVersionedMixedCache233.refresh_cache cert,v.origin,
    fun q => atoms_preserved cert.refines (v.scalars q)⟩

theorem reach_facts {s : State roles} {len : Nat} (path : ActualPath installed s len) : ReachFacts s := by
  induction path with
  | empty =>
    exact ⟨GeneralRebaseDepthPathAnchor285.initial,GeneralRebaseDepthPathKeep285.start,⟨install_cache,rfl,initial_atoms⟩⟩
  | more _ taken ih =>
    have hop := (GeneralRebaseDepthPathRank285.exact ih.anchor ih.kept).mp taken
    have retained := GeneralRebaseDepthPathRank285.anchored ih.anchor ih.kept hop
    refine ⟨retained.1,retained.2,?_⟩
    cases hop with
    | refresh context cert _ _ _ _ =>
      exact refresh_basic ih.basic cert

end Yulang.GeneralMixedControlAtoms306
