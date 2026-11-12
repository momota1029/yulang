import Yulang.GeneralNominalFeedbackSteps

/-! A maximal set of source-indexed, independently certified observations.
The set retains every compatible normalized head and nominal interval
descriptor entailed by the whole journal. It is not a finite presentation or
a new candidate classifier; consuming all its facts remains a separate bridge. -/
namespace Yulang.GeneralCanonicalObservations

open GeneralNominalSaturationState
open GeneralNominalCommonBridge (Assignment)
open Core.PresenceGeneration (TyTerm)

inductive Observation where
  | normalized (base : GeneralSourceState.State) (slot : Fin base.slots) (term : TyTerm (Fin base.slots))
  | nominal (base : GeneralSourceState.State) (slot : Fin base.slots) (descriptor : GeneralNominalState.Descriptor base.slots)

def Observation.source : Observation → Nat
  | .normalized base slot _ | .nominal base slot _ => base.source slot

def Observation.support : Observation → List Nat
  | .normalized base _ _ | .nominal base _ _ => List.ofFn base.source ++ List.ofFn base.rowSource

def Observation.Holds : Observation → Assignment → Prop
  | .normalized base slot term, model => CommonNominalFullCarrier.Equivalent (model (base.source slot)).1
      (term.eval CommonNominalFullCarrier.model (GeneralNominalCommonBridge.assignment base model))
  | .nominal base slot descriptor, model => GeneralNominalState.Denotes base model slot descriptor

/-- Only actual certified scalar/complete structural heads and catalogue-checked
nominal descriptors enter. Deferred terms do not become head observations. -/
inductive Recorded (snapshot : GeneralNominalState.State) : Observation → Prop
  | scalar (slot : Fin snapshot.base.slots) (scalar : Inference.Base) :
      snapshot.view.heads slot = .scalar scalar → Recorded snapshot (.normalized snapshot.base slot (.base scalar))
  | structural (slot : Fin snapshot.base.slots) (kind : Fin snapshot.view.kinds)
      (children : Fin (snapshot.view.shapes kind).arity → Fin snapshot.base.slots) :
      snapshot.view.heads slot = .structural kind children →
      Recorded snapshot (.normalized snapshot.base slot ((snapshot.view.shapes kind).term children))
  | nominal (slot : Fin snapshot.base.slots) (descriptor : GeneralNominalState.Descriptor snapshot.base.slots) :
      snapshot.nominals slot = some descriptor → Recorded snapshot (.nominal snapshot.base slot descriptor)

def Certified (observation : Observation) : Prop := ∃ snapshot, Recorded snapshot observation

def Compatible (state : State roles) (observation : Observation) : Prop :=
  (∀ source ∈ observation.support, source ∈ GeneralNominalState.sources state.context.state) ∧
    match observation with
    | .normalized _ _ _ => True
    | .nominal _ _ descriptor => state.context.state.constructors descriptor.constructor = some descriptor.declaration

def Entails (state : State roles) (observation : Observation) : Prop :=
  ∀ model, Models state model → observation.Holds model

/-- This predicate is the entire view, not a choice of a single descriptor. -/
def canonical (state : State roles) (observation : Observation) : Prop :=
  Certified observation ∧ Compatible state observation ∧ Entails state observation

theorem recorded_sound (snapshot : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models snapshot model) (seen : Recorded snapshot observation) : observation.Holds model := by
  cases seen with
  | scalar slot scalar recorded =>
    exact GeneralNominalState.normalized_models snapshot model valid slot (.base scalar)
      (by simp [recorded,GeneralNormalizedObservation.Head.term])
  | structural slot kind children recorded =>
    exact GeneralNominalState.normalized_models snapshot model valid slot ((snapshot.view.shapes kind).term children)
      (by simp [recorded,GeneralNormalizedObservation.Head.term])
  | nominal slot descriptor recorded => exact valid.2.1 slot descriptor recorded

theorem recorded_compatible (state : State roles) (seen : Recorded state.context.state observation) :
    Compatible state observation := by
  have support : ∀ source ∈ List.ofFn state.context.state.base.source ++ List.ofFn state.context.state.base.rowSource,
      source ∈ GeneralNominalState.sources state.context.state := by
    intro source member
    exact List.mem_append_left _ (List.mem_append_left _ member)
  cases seen with
  | scalar => exact ⟨support,True.intro⟩
  | structural => exact ⟨support,True.intro⟩
  | nominal slot descriptor recorded => exact ⟨support,state.context.state.catalogue slot descriptor recorded⟩

theorem recorded_in_canonical (state : State roles) (seen : Recorded state.context.state observation) :
    canonical state observation :=
  ⟨⟨state.context.state,seen⟩,recorded_compatible state seen,fun model valid => recorded_sound _ model valid.1 seen⟩

theorem canonical_sound (state : State roles) (seen : canonical state observation)
    (model : Assignment) (valid : Models state model) : observation.Holds model := seen.2.2 model valid

theorem canonical_complete (state : State roles) (certified : Certified observation)
    (compatible : Compatible state observation) (entailed : Entails state observation) : canonical state observation :=
  ⟨certified,compatible,entailed⟩

theorem maximal (state : State roles) (view : Observation → Prop)
    (certified : ∀ observation, view observation → Certified observation)
    (compatible : ∀ observation, view observation → Compatible state observation)
    (sound : ∀ observation, view observation → Entails state observation) :
    ∀ observation, view observation → canonical state observation :=
  fun observation present => ⟨certified observation present,compatible observation present,sound observation present⟩

def ViewModels (state : State roles) (model : Assignment) : Prop :=
  Models state model ∧ ∀ observation, canonical state observation → observation.Holds model

theorem models_exact (state : State roles) (model : Assignment) : ViewModels state model ↔ Models state model :=
  ⟨And.left,fun valid => ⟨valid,fun _ seen => canonical_sound state seen model valid⟩⟩

structure BasisExtends (before after : State roles) : Prop where
  sources : ∀ source ∈ GeneralNominalState.sources before.context.state,
    source ∈ GeneralNominalState.sources after.context.state
  constructors : after.context.state.constructors = before.context.state.constructors

theorem compatible_mono (basis : BasisExtends before after) (given : Compatible before observation) :
    Compatible after observation := by
  refine ⟨fun source member => basis.sources source (given.1 source member),?_⟩
  cases observation with
  | normalized => trivial
  | nominal base slot descriptor => exact basis.constructors ▸ given.2

theorem monotone (basis : BasisExtends before after)
    (models : ∀ model, Models after model → Models before model) :
    ∀ observation, canonical before observation → canonical after observation :=
  fun _ seen => ⟨seen.1,compatible_mono basis seen.2.1,fun model valid => seen.2.2 model (models model valid)⟩

theorem equal_of_same_information (forward : BasisExtends first last) (backward : BasisExtends last first)
    (models : ∀ model, Models first model ↔ Models last model) : canonical first = canonical last := by
  funext observation
  exact propext ⟨monotone forward (fun model => (models model).mpr) observation,
    monotone backward (fun model => (models model).mp) observation⟩

/-- A cache can be incomplete without changing source meaning. -/
structure Cache (state : State roles) where
  contains : Observation → Prop
  justified : ∀ observation, contains observation → canonical state observation

def complete (state : State roles) : Cache state := ⟨canonical state,fun _ seen => seen⟩
def Canonical (cache : Cache state) : Prop := ∀ observation, canonical state observation → cache.contains observation

theorem complete_canonical (state : State roles) : Canonical (complete state) := fun _ seen => seen

theorem canonical_cache_unique (first last : Cache state) (one : Canonical first) (two : Canonical last) :
    first.contains = last.contains := by
  funext observation
  exact propext ⟨fun seen => two _ (first.justified _ seen),fun seen => one _ (last.justified _ seen)⟩

/-- Completion changes only the cache. It is not full role saturation. -/
inductive Completion (state : State roles) : Cache state → Cache state → Prop
  | finish (cache : Cache state) : ¬ Canonical cache → Completion state cache (complete state)

theorem completion_models (_step : Completion state first last) (model : Assignment) :
    (Models state model ∧ ∀ observation, last.contains observation → observation.Holds model) ↔
      (Models state model ∧ ∀ observation, first.contains observation → observation.Holds model) := by
  have sound (cache : Cache state) (valid : Models state model) :
      ∀ observation, cache.contains observation → observation.Holds model :=
    fun _ seen => canonical_sound state (cache.justified _ seen) model valid
  exact ⟨fun valid => ⟨valid.1,sound first valid.1⟩,fun valid => ⟨valid.1,sound last valid.1⟩⟩

theorem completion_exists (cache : Cache state) :
    ∃ final, B4Target.Steps (Completion state) cache final ∧ Canonical final := by
  classical
  by_cases done : Canonical cache
  · exact ⟨cache,.refl,done⟩
  · exact ⟨complete state,.tail .refl (.finish cache done),complete_canonical state⟩

theorem completion_halted_iff (cache : Cache state) :
    (∀ next, ¬ Completion state cache next) ↔ Canonical cache := by
  classical
  constructor
  · intro halted
    exact Classical.byContradiction (fun unfinished => halted _ (.finish cache unfinished))
  · intro canonical next step
    cases step with | finish unfinished => exact unfinished canonical

end Yulang.GeneralCanonicalObservations
