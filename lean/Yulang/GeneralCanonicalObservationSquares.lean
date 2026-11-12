import Yulang.GeneralNominalReobservationSteps

/-! Model-level commuting squares for the maximal observation predicate.
The laws concern actual journal semantics. They do not assert preservation of
Installable, allocation identity, inspection, or transition enablement. -/
namespace Yulang.GeneralCanonicalObservationSquares

open GeneralNominalSaturationState
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalDemandMerging (Site)
open GeneralCanonicalObservations

variable {roles : Roles.RoleDecls} {start left right finalLeft finalRight : State roles}

/-- A fixed information addition, independently of how it was scheduled. -/
def Adds (before after : State roles) (condition : Assignment → Prop) : Prop :=
  ∀ model, Models after model ↔ Models before model ∧ condition model

theorem install_adds (state : State roles) (packet : Packet roles)
    (emission : GeneralNominalFeedbackSites.Emission packet) (same : packet.context = state.context) :
    Adds state (GeneralNominalFeedbackSites.install state packet emission) packet.Holds :=
  GeneralNominalFeedbackSites.install_models state packet emission same

theorem merge_adds (state : State roles) (first last : Site roles) :
    Adds state (merge state first last)
      (fun model => PresenceNormalForm.All CommonNominalFullCarrier.model model
        (GeneralNominalDemandMerging.outputAtoms first last)) := merge_models state first last

/-- Four certified edges suffice for a model square. The second edges are
premises: this theorem does not turn an unavailable transition into one. -/
theorem square_models {one two : Assignment → Prop}
    (first : Adds start left one) (second : Adds start right two)
    (afterFirst : Adds left finalLeft two) (afterSecond : Adds right finalRight one) :
    ∀ model, Models finalLeft model ↔ Models finalRight model := by
  intro model
  rw [afterFirst model,afterSecond model,first model,second model]
  exact ⟨fun h => ⟨⟨h.1.1,h.2⟩,h.1.2⟩,fun h => ⟨⟨h.1.1,h.2⟩,h.1.2⟩⟩

theorem square_observations {one two : Assignment → Prop}
    (first : Adds start left one) (second : Adds start right two)
    (afterFirst : Adds left finalLeft two) (afterSecond : Adds right finalRight one)
    (forward : BasisExtends finalLeft finalRight) (backward : BasisExtends finalRight finalLeft) :
    canonical finalLeft = canonical finalRight :=
  equal_of_same_information forward backward (square_models first second afterFirst afterSecond)

theorem merge_merge_models (state : State roles) (a b c d : Site roles) (model : Assignment) :
    Models (merge (merge state a b) c d) model ↔ Models (merge (merge state c d) a b) model :=
  square_models (merge_adds state a b) (merge_adds state c d)
    (merge_adds (merge state a b) c d) (merge_adds (merge state c d) a b) model

theorem merge_merge_basis (state : State roles) (a b c d : Site roles) :
    BasisExtends (merge (merge state a b) c d) (merge (merge state c d) a b) := by
  refine ⟨?_,rfl⟩
  intro source member
  simpa only [GeneralNominalState.sources,merge,GeneralNominalState.extend,
    List.flatMap_append,List.mem_append,or_assoc,or_left_comm,or_comm] using member

theorem merge_merge_observations (state : State roles) (a b c d : Site roles) :
    canonical (merge (merge state a b) c d) = canonical (merge (merge state c d) a b) :=
  equal_of_same_information (merge_merge_basis state a b c d) (merge_merge_basis state c d a b)
    (merge_merge_models state a b c d)

theorem refresh_observations (state : State roles) (context : GeneralNominalCandidates.Context)
    (certificate : GeneralNominalFeedbackSteps.Refresh state context) :
    canonical (regenerate state context) = canonical state :=
  equal_of_same_information ⟨certificate.support,certificate.refines.constructors.symm⟩
    ⟨GeneralNominalRefinements.sources certificate.refines,certificate.refines.constructors⟩
    (GeneralNominalCycleSteps.refresh_models certificate)

theorem reobservation_reobservation (first last : GeneralNominalReobservationSteps.Revision start)
    (one : GeneralNominalReobservationSteps.Certified first) (two : GeneralNominalReobservationSteps.Certified last) :
    canonical first.result = canonical last.result :=
  (GeneralNominalReobservationSteps.revision_canonical first one).trans
    (GeneralNominalReobservationSteps.revision_canonical last two).symm

/-- Enqueueing a demand has no semantic effect before or after a merge. -/
theorem enqueue_merge_models (state : State roles) (root : GeneralSourceDictionaries.Occurrence roles)
    (first last : Site roles) (model : Assignment) :
    Models (merge (enqueue state root) first last) model ↔ Models (enqueue (merge state first last) root) model := by
  rw [merge_models,enqueue_models,enqueue_models,merge_models]

/-- Reobservation can be moved across a fixed model addition once that addition
is available with the same meaning on both sides. -/
theorem reobservation_add_models (revision : GeneralNominalReobservationSteps.Revision start)
    (certified : GeneralNominalReobservationSteps.Certified revision) {condition : Assignment → Prop}
    (old : Adds start left condition) (new : Adds revision.result right condition) :
    ∀ model, Models left model ↔ Models right model := by
  intro model
  rw [old model,new model,certified.exact model]

end Yulang.GeneralCanonicalObservationSquares
