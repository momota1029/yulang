import Yulang.GeneralDictionaryModelEvidence

/-!
# Dictionary equation evidence under source-preserving refinement

Local slots and terms are transported through an arbitrary `Refines` embedding.
The original source-indexed dictionary is retained, with an explicitly lifted
package relation. This preserves stored equation evidence; it does not establish
candidate selection, declaration instantiation, or a complete narrowing step.
-/
namespace Yulang.GeneralDictionaryRefinementEvidence

open Core.PresenceGeneration (TyTerm)
open GeneralSourceState (State Demand Assignment Models Refines)
open GeneralDictionaryStateEquations
open GeneralDictionaryModelEvidence
open GeneralSourceDictionaries GeneralDictionaryReadback

/-- Reindex every local endpoint and term, retaining global source occurrences. -/
def transport (refinement : Refines before after) (located : Located before demand) :
    Located after demand where
  lower := fun index => refinement.embed (located.lower index)
  upper := fun index => refinement.embed (located.upper index)
  head := fun index => (located.head index).rename refinement.embed
  target := fun index => refinement.embed (located.target index)
  output := fun index => (located.output index).rename refinement.embed
  arguments := fun index => by simpa only [refinement.source] using located.arguments index
  targets := fun index => by simpa only [refinement.source] using located.targets index

/-- All four storage families survive by ordinary renamed-atom membership. -/
theorem transport_recorded (refinement : Refines before after)
    (located : Located before demand) (recorded : Recorded located) :
    Recorded (transport refinement located) where
  lower := fun index => refinement.ordinary _ (recorded.lower index)
  upper := fun index => refinement.ordinary _ (recorded.upper index)
  outputForward := fun index => refinement.ordinary _ (recorded.outputForward index)
  outputBackward := fun index => refinement.ordinary _ (recorded.outputBackward index)

/-- Type and row source identities are both needed for arbitrary arrow terms. -/
theorem assignment_comp_embed (refinement : Refines before after) (assignment : Assignment) :
    after.assignment assignment ∘ refinement.embed = before.assignment assignment := by
  funext slot
  simp only [Function.comp_def, State.assignment, refinement.source, refinement.rowSource]

/-- Equality holds at every global assignment, without a state-model premise. -/
theorem liftType_transport_eval (refinement : Refines before after)
    (term : TyTerm (Fin before.slots)) (assignment : Assignment) :
    (liftType after (term.rename refinement.embed)).eval Common.model assignment =
      (liftType before term).eval Common.model assignment := by
  rw [liftType_eval, TyTerm.eval_rename, assignment_comp_embed, liftType_eval]

/-- The transported equations have exactly the same meaning at the same model. -/
theorem transport_holds_iff (refinement : Refines before after)
    (located : Located before demand) (assignment : Assignment) :
    (transport refinement located).equations.Holds assignment ↔
      located.equations.Holds assignment := by
  simp only [GeneralSourceDictionaryEquations.InstanceEquations.Holds,
    Located.equations, transport, liftType_transport_eval]

/-- The new package relation contains precisely images of old packages, not an
assumption that unrelated after-state packages correspond to declarations. -/
def liftPackages (refinement : Refines before after) (packages : Packages roles before) :
    Packages roles after := fun occurrence key children located =>
  ∃ original, packages occurrence key children original ∧
    located = transport refinement original

/-- Occurrence, implementation key, and the exact ordered child list survive. -/
theorem stored_instance_transport (refinement : Refines before after)
    (packages : Packages roles before) (occurrence : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles))
    (stored : StoredInstance packages occurrence key children) :
    StoredInstance (liftPackages refinement packages) occurrence key children := by
  obtain ⟨located, instanceRule, recorded⟩ := stored
  exact ⟨transport refinement located, ⟨located, instanceRule, rfl⟩,
    transport_recorded refinement located recorded⟩

/-- Model-local package meaning is equivalent even outside the model sets. -/
theorem model_instance_transport_iff (refinement : Refines before after)
    (packages : Packages roles before) (assignment : Assignment)
    (occurrence : Occurrence roles) (key : Nat) (children : List (Occurrence roles)) :
    ModelInstance (liftPackages refinement packages) assignment occurrence key children ↔
      ModelInstance packages assignment occurrence key children := by
  constructor
  · rintro ⟨located, ⟨original, instanceRule, rfl⟩, holds⟩
    exact ⟨original, instanceRule, (transport_holds_iff refinement original assignment).mp holds⟩
  · rintro ⟨original, instanceRule, holds⟩
    exact ⟨transport refinement original, ⟨original, instanceRule, rfl⟩,
      (transport_holds_iff refinement original assignment).mpr holds⟩

/-- Whole-tree storage is transported without replacing the source dictionary. -/
theorem indexed_transport (refinement : Refines before after)
    (packages : Packages roles before) (tree : Dictionary roles)
    (stored : Evidence (StoredInstance packages) tree) :
    Evidence (StoredInstance (liftPackages refinement packages)) tree :=
  evidence_mono _ _ (stored_instance_transport refinement packages) stored

/-- One unchanged tree satisfies the transported package equations in each
arbitrary model of the refined state, simultaneously at every node. -/
theorem indexed_transport_all_models (refinement : Refines before after)
    (packages : Packages roles before) (tree : Dictionary roles)
    (stored : Evidence (StoredInstance packages) tree) (assignment : Assignment)
    (model : Models after assignment) :
    Evidence (ModelInstance (liftPackages refinement packages) assignment) tree :=
  indexed_all_models _ tree (indexed_transport refinement packages tree stored) assignment model

/-- The source witness remains outside universal model quantification. -/
theorem erased_transport_uniform_witness (refinement : Refines before after)
    (packages : Packages roles before) (occurrence : Occurrence roles) (payload : Payload)
    (stored : ErasedEvidence (StoredInstance packages) occurrence payload) :
    ∃ tree, Readback occurrence payload tree ∧
      Evidence (StoredInstance (liftPackages refinement packages)) tree ∧
      ∀ assignment, Models after assignment →
        Evidence (ModelInstance (liftPackages refinement packages) assignment) tree := by
  obtain ⟨tree, readback, evidence⟩ := stored
  exact ⟨tree, readback, indexed_transport refinement packages tree evidence,
    indexed_transport_all_models refinement packages tree evidence⟩

end Yulang.GeneralDictionaryRefinementEvidence
