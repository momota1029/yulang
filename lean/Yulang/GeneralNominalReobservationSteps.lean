import Yulang.GeneralCanonicalObservations
import Yulang.GeneralNominalFeedbackProgress

/-! Additive, certified replacement of nominal interval descriptors. Existing
source/row identities, structural normalization, allocation data and journal
entries are fixed. A new rule can improve descriptor precision after Known has
stabilized. This rule repairs point refinement; it is not yet a consumer of the
entire maximal observation predicate. -/
namespace Yulang.GeneralNominalReobservationSteps

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalCommonBridge (Assignment)

variable {roles : Roles.RoleDecls} {state before after : State roles}

def PointParameter : GeneralNominalState.Parameter slots → Prop
  | .type bounds | .row bounds => bounds.1 = bounds.2

def PointDescriptor (descriptor : GeneralNominalState.Descriptor slots) : Prop :=
  ∀ parameter ∈ descriptor.arguments, PointParameter parameter

def PointAt (snapshot : GeneralNominalState.State) (slot : Fin snapshot.base.slots) : Prop :=
  ∃ descriptor, snapshot.nominals slot = some descriptor ∧ PointDescriptor descriptor

structure Revision (state : State roles) where
  entries : Fin state.context.state.base.slots → Option (GeneralNominalState.Descriptor state.context.state.base.slots)
  catalogue : ∀ slot descriptor, entries slot = some descriptor →
    state.context.state.constructors descriptor.constructor = some descriptor.declaration
  opaqueHeads : ∀ slot descriptor, entries slot = some descriptor →
    state.context.state.view.heads slot = .deferred .unresolved
  domain : ∀ slot, entries slot = none ↔ state.context.state.nominals slot = none

def Revision.snapshot (revision : Revision state) : GeneralNominalState.State :=
  { state.context.state with nominals := revision.entries, catalogue := revision.catalogue, bodies_opaque := revision.opaqueHeads }

def Revision.result (revision : Revision state) : State roles :=
  regenerate state ⟨revision.snapshot,state.context.interpretation⟩

structure Certified (revision : Revision state) : Prop where
  raw : ∀ model, GeneralNominalState.Models revision.snapshot model → GeneralNominalState.Models state.context.state model
  exact : ∀ model, Models revision.result model ↔ Models state model

def Improves (revision : Revision state) : Prop :=
  (∀ slot, PointAt state.context.state slot → PointAt revision.snapshot slot) ∧
    ∃ slot, ¬ PointAt state.context.state slot ∧ PointAt revision.snapshot slot

theorem revision_known (revision : Revision state) (source : Nat) :
    GeneralNominalState.Known revision.snapshot source ↔ GeneralNominalState.Known state.context.state source := by
  constructor
  · rintro ⟨slot,same,head | ⟨descriptor,recorded⟩⟩
    · exact ⟨slot,same,Or.inl head⟩
    · have existsOld : ∃ prior, state.context.state.nominals slot = some prior := by
        cases old : state.context.state.nominals slot with
        | none => have missing := (revision.domain slot).mpr old; change revision.entries slot = some descriptor at recorded; rw [missing] at recorded; cases recorded
        | some prior => exact ⟨prior,rfl⟩
      exact ⟨slot,same,Or.inr existsOld⟩
  · rintro ⟨slot,same,head | ⟨descriptor,recorded⟩⟩
    · exact ⟨slot,same,Or.inl head⟩
    · have existsNew : ∃ next, revision.entries slot = some next := by
        cases next : revision.entries slot with
        | none => have missing := (revision.domain slot).mp next; rw [missing] at recorded; cases recorded
        | some descriptor => exact ⟨descriptor,rfl⟩
      exact ⟨slot,same,Or.inr existsNew⟩

theorem revision_basis (revision : Revision state) :
    GeneralCanonicalObservations.BasisExtends state revision.result ∧
      GeneralCanonicalObservations.BasisExtends revision.result state :=
  ⟨⟨fun _ member => member,rfl⟩,⟨fun _ member => member,rfl⟩⟩

theorem revision_canonical (revision : Revision state) (certificate : Certified revision) :
    GeneralCanonicalObservations.canonical revision.result = GeneralCanonicalObservations.canonical state :=
  GeneralCanonicalObservations.equal_of_same_information (revision_basis revision).2 (revision_basis revision).1 certificate.exact

/-- If every existing nominal descriptor is already point-valued, this limited
precision rule has no update. This does not assert full canonicality. -/
def PointClosed (snapshot : GeneralNominalState.State) : Prop :=
  ∀ slot descriptor, snapshot.nominals slot = some descriptor → PointDescriptor descriptor

theorem pointClosed_no_revision (closed : PointClosed state.context.state) (revision : Revision state) :
    ¬ Improves revision := by
  rintro ⟨_,slot,notPoint,descriptor,recorded,point⟩
  cases old : state.context.state.nominals slot with
  | none =>
    have missing := (revision.domain slot).mpr old
    change revision.entries slot = some descriptor at recorded
    rw [missing] at recorded; cases recorded
  | some prior => exact notPoint ⟨prior,old,closed slot prior old⟩

inductive At (registry : Registry) (state : State roles) : Occurrence roles → State roles → Prop
  | ordinary (focus : Occurrence roles) {after} :
      GeneralNominalFeedbackSteps.At registry state focus after → At registry state focus after
  | reobserve (focus : Occurrence roles) (revision : Revision state) :
      Certified revision → Improves revision → At registry state focus revision.result

def Step (registry : Registry) (root : Occurrence roles) (before after : State roles) : Prop :=
  ∃ focus, Generated before root focus ∧ At registry before focus after

def Stable (registry : Registry) (state : State roles) (root : Occurrence roles) : Prop :=
  ∀ focus, Generated state root focus → ∀ after, ¬ At registry state focus after

theorem old_step (update : GeneralNominalFeedbackSteps.Step registry root before after) : Step registry root before after := by
  obtain ⟨focus,reached,action⟩ := update
  exact ⟨focus,reached,.ordinary focus action⟩

theorem at_models (update : At registry before focus after) (model : Assignment)
    (valid : Models after model) : Models before model := by
  cases update with
  | ordinary action => exact GeneralNominalFeedbackSteps.at_models action model valid
  | reobserve _ certificate _ => exact (certificate.exact model).mp valid

theorem stepModels (update : Step registry root before after) (model : Assignment)
    (valid : Models after model) : Models before model := at_models update.choose_spec.2 model valid

theorem steps_models (path : B4Target.Steps (Step registry root) before after) (model : Assignment)
    (valid : Models after model) : Models before model := by
  induction path with
  | refl => exact valid
  | tail _ update ih => exact ih (stepModels update model valid)

theorem at_known (update : At registry before focus after) (source : Nat)
    (known : GeneralNominalState.Known before.context.state source) : GeneralNominalState.Known after.context.state source := by
  cases update with
  | ordinary action => exact (GeneralNominalFeedbackProgress.at_extends action).journal.known source known
  | reobserve revision _ _ => exact (revision_known revision source).mpr known

theorem at_extends (update : At registry before focus after) :
    GeneralNominalFeedbackProgress.Extends before after := by
  cases update with
  | ordinary action => exact GeneralNominalFeedbackProgress.at_extends action
  | reobserve revision certificate improved =>
    exact ⟨⟨fun model valid => (certificate.exact model).mp valid,
      fun _ member => member,fun _ member => member,fun _ member => member,
      fun source known => (revision_known revision source).mpr known⟩,certificate.raw⟩

theorem generated_monotone (update : Step registry root before after) (reached : Generated before root child) :
    Generated after root child :=
  GeneralNominalSaturationSteps.generated_monotone (at_extends update.choose_spec.2).journal reached

theorem basis_of_refines (refines : GeneralNominalRefinements.Refines before.context.state after.context.state) :
    GeneralCanonicalObservations.BasisExtends before after :=
  ⟨GeneralNominalRefinements.sources refines,refines.constructors⟩

theorem at_basis (update : At registry before focus after) :
    GeneralCanonicalObservations.BasisExtends before after := by
  cases update with
  | reobserve revision _ _ => exact (revision_basis revision).1
  | ordinary action =>
    cases action with
    | enqueue => exact ⟨fun _ member => member,rfl⟩
    | install packet enabled _ =>
      apply basis_of_refines
      change GeneralNominalRefinements.Refines before.context.state packet.privateContext.state
      rw [← enabled.1.2.1]
      exact GeneralNominalRefinements.installed packet.registry packet.context packet.site.occurrence
        packet.declaration packet.bounds
    | merge first last _ _ _ _ =>
      exact basis_of_refines (GeneralNominalRefinements.extended before.context.state [] _)
    | refresh _ _ certificate _ _ _ _ => exact basis_of_refines certificate.refines
    | equate => exact basis_of_refines (GeneralNominalRefinements.extended before.context.state [] _)

theorem canonical_monotone (update : Step registry root before after) :
    ∀ observation, GeneralCanonicalObservations.canonical before observation →
      GeneralCanonicalObservations.canonical after observation :=
  GeneralCanonicalObservations.monotone (at_basis update.choose_spec.2) (stepModels update)

theorem canonical_trace (path : B4Target.Steps (Step registry root) before after) :
    ∀ observation, GeneralCanonicalObservations.canonical before observation →
      GeneralCanonicalObservations.canonical after observation := by
  intro observation seen
  induction path with
  | refl => exact seen
  | tail _ update ih => exact canonical_monotone update observation ih

theorem stable_iff (registry : Registry) (state : State roles) (root : Occurrence roles) :
    Stable registry state root ↔ GeneralNominalFeedbackSteps.Stable registry state root ∧
      ∀ revision : Revision state, Certified revision → ¬ Improves revision := by
  constructor
  · intro stopped
    exact ⟨fun focus reached after action => stopped focus reached after (.ordinary focus action),
      fun revision certificate improved => stopped root .root _ (.reobserve root revision certificate improved)⟩
  · rintro ⟨stopped,closed⟩ focus reached after action
    cases action with
    | ordinary action => exact stopped focus reached after action
    | reobserve revision certificate improved => exact closed revision certificate improved

theorem stable_of_pointClosed (stable : GeneralNominalFeedbackSteps.Stable registry state root)
    (closed : PointClosed state.context.state) : Stable registry state root :=
  (stable_iff registry state root).mpr ⟨stable,fun revision _ => pointClosed_no_revision closed revision⟩

theorem halted_stable (halted : ∀ after, ¬ Step registry root state after) : Stable registry state root :=
  fun focus reached after update => halted after ⟨focus,reached,update⟩

theorem stable_halted (stable : Stable registry state root) : ∀ after, ¬ Step registry root state after := by
  rintro after ⟨focus,reached,update⟩
  exact stable focus reached after update

theorem stable_generated (stable : Stable registry state root) (generated : Generated state root child) :
    Stable registry state child := fun focus reached => stable focus (generated_trans generated reached)

theorem closure (halted : ∀ after, ¬ Step registry root state after) :
    Stable registry state root ∧ ∀ child, Generated state root child → Stable registry state child :=
  ⟨halted_stable halted,fun _ reached => stable_generated (halted_stable halted) reached⟩

/-- Full stability imposes more than observation completion when a new view
enables an installation whose constraints were not already entailed. -/
theorem stable_committed (stable : Stable registry state root) (packet : Packet roles)
    (generated : Generated state root packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state packet) :
    GeneralNominalFeedbackSteps.Committed state packet :=
  GeneralNominalFeedbackSteps.stable_committed ((stable_iff registry state root).mp stable).1 packet generated enabled

theorem committed_trace (path : B4Target.Steps (Step registry root) before after)
    (committed : GeneralNominalFeedbackSteps.Committed before packet) :
    GeneralNominalFeedbackSteps.Committed after packet := by
  induction path with
  | refl => exact committed
  | tail _ update ih =>
    exact ⟨fun model valid => ih.1 model (stepModels update model valid),
      fun child member => (at_extends update.choose_spec.2).journal.edges _ (ih.2 child member)⟩

theorem same_models_stable_requires_constraints (stable : Stable registry after root)
    (same : ∀ model, Models before model ↔ Models after model) (packet : Packet roles)
    (generated : Generated after root packet.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry after packet) :
    ∀ model, Models before model → packet.Holds model :=
  fun model valid => (stable_committed stable packet generated enabled).1 model ((same model).mp valid)

end Yulang.GeneralNominalReobservationSteps
