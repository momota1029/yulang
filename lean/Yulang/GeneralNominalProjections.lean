import Yulang.GeneralNominalIntervalLaws

/-! Source identities for actual nominal occurrences. A projection is an
observation path, not a fresh type variable or a selected interval centre.
Its value is unique up to the existing carrier equivalence. Extra constraints
on these paths preserve the original shared model and its normalization. -/
namespace Yulang.GeneralNominalProjections

open CommonNominalFullCarrier

inductive Ref where
  | source (identity : Nat)
  | argument (parent : Ref) (name index : Nat)
  deriving DecidableEq

inductive Observes (model : GeneralNominalCommonBridge.Assignment) : Ref → Argument → Prop
  | source (identity) : Observes model (.source identity) (.inl (model identity).1)
  | argument : Observes model parent (.inl value) →
      Equivalent value (nominal name arguments) → arguments[index]? = some actual →
      Observes model (.argument parent name index) actual

theorem observation_unique (model : GeneralNominalCommonBridge.Assignment)
    (ref : Ref) (first last : Argument)
    (one : Observes model ref first) (two : Observes model ref last) :
    ArgumentEquivalent first last := by
  induction ref generalizing first last with
  | source identity => cases one; cases two; exact ⟨subtype_refl _, subtype_refl _⟩
  | argument parent name index ih =>
      cases one with
      | argument p pe pi =>
          cases two with
          | argument q qe qi =>
              have same := ih _ _ p q
              have endpoints := subtype_trans pe.2 (subtype_trans same.1 qe.1)
              exact (nominal_regular_invariant_exact _ _ _ _).mp endpoints |>.2.2 index _ _ pi qi

def Equal (model : GeneralNominalCommonBridge.Assignment) (first last : Ref) : Prop :=
  ∃ a b, Observes model first a ∧ Observes model last b ∧ ArgumentEquivalent a b

private theorem argument_trans (a b c : Argument)
    (first : ArgumentEquivalent a b) (last : ArgumentEquivalent b c) : ArgumentEquivalent a c := by
  cases a <;> cases b <;> cases c <;> simp only [ArgumentEquivalent] at *
  all_goals try exact False.elim first
  all_goals try exact False.elim last
  · exact ⟨subtype_trans first.1 last.1, subtype_trans last.2 first.2⟩
  · exact first.trans last

theorem equal_all_observations (model : GeneralNominalCommonBridge.Assignment)
    (first last : Ref) (equal : Equal model first last)
    (a b : Argument) (one : Observes model first a) (two : Observes model last b) :
    ArgumentEquivalent a b := by
  obtain ⟨x,y,hx,hy,same⟩ := equal
  exact argument_trans _ _ _ (observation_unique model first a x one hx)
    (argument_trans _ _ _ same (observation_unique model last y b hy two))

structure Binding (state : GeneralNominalState.State) where
  name : Nat
  bounds : GeneralNominalState.Parameter state.base.slots
  origin : Ref

def Binding.Valid (state : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) (binding : Binding state) : Prop :=
  ∃ value, Observes model binding.origin value ∧
    GeneralNominalState.Fits state.base model binding.bounds value

def Compatible (state : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) (bindings : List (Binding state)) : Prop :=
  (∀ binding ∈ bindings, binding.Valid state model) ∧
    ∀ first ∈ bindings, ∀ last ∈ bindings, first.name = last.name → Equal model first.origin last.origin

theorem compatible_cross (state : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) (bindings : List (Binding state))
    (compatible : Compatible state model bindings)
    (first last : Binding state) (one : first ∈ bindings) (two : last ∈ bindings)
    (same : first.name = last.name) :
    GeneralNominalIntervalLaws.ParameterChecks state.base model first.bounds last.bounds := by
  obtain ⟨x,hx,fx⟩ := compatible.1 first one
  obtain ⟨y,hy,fy⟩ := compatible.1 last two
  have equal := equal_all_observations model _ _ (compatible.2 first one last two same) x y hx hy
  exact GeneralNominalIntervalLaws.fits_checks _ _ _ _ y
    ((GeneralNominalIntervalLaws.fits_equivalent _ _ _ _ _ equal).mp fx) fy

/-- The descriptor's interval is retained even when its endpoints differ.
The origin records which actual argument this interval constrains. -/
def parameterBinding (state : GeneralNominalState.State) (slot : Fin state.base.slots)
    (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (index name : Nat) (bounds : GeneralNominalState.Parameter state.base.slots) : Binding state :=
  ⟨name, bounds, .argument (.source (state.base.source slot)) descriptor.declaration.name index⟩

theorem parameter_binding_valid (state : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) (models : GeneralNominalState.Models state model)
    (slot : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor)
    (index name : Nat) (bounds : GeneralNominalState.Parameter state.base.slots)
    (found : descriptor.arguments[index]? = some bounds) :
    (parameterBinding state slot descriptor index name bounds).Valid state model := by
  obtain ⟨values,fits,equal⟩ := models.2.1 slot descriptor recorded
  obtain ⟨value,atIndex,valid⟩ := GeneralNominalIntervalLaws.fitsAll_at _ _ _ _ fits index bounds found
  exact ⟨value, .argument (.source _) equal atIndex, valid⟩

/-- A branch extension adds actual-occurrence equalities, without changing
source allocation, ordinary atoms, or the checked observation snapshot. -/
structure State where
  source : GeneralNominalState.State
  bindings : List (Binding source)

def Models (state : State) (model : GeneralNominalCommonBridge.Assignment) : Prop :=
  GeneralNominalState.Models state.source model ∧ Compatible state.source model state.bindings

theorem models_source (state : State) (model : GeneralNominalCommonBridge.Assignment)
    (models : Models state model) : GeneralNominalState.Models state.source model := models.1

theorem models_normalized (state : State) (model : GeneralNominalCommonBridge.Assignment)
    (models : Models state model) : GeneralNominalCommonBridge.ObservationModels state.source.view model :=
  GeneralNominalState.normalized_models _ _ models.1

theorem models_cross (state : State) (model : GeneralNominalCommonBridge.Assignment)
    (models : Models state model) (first last : Binding state.source)
    (one : first ∈ state.bindings) (two : last ∈ state.bindings) (same : first.name = last.name) :
    GeneralNominalIntervalLaws.ParameterChecks state.source.base model first.bounds last.bounds :=
  compatible_cross _ _ _ models.2 first last one two same

theorem empty_extension (source : GeneralNominalState.State)
    (model : GeneralNominalCommonBridge.Assignment) :
    Models ⟨source,[]⟩ model ↔ GeneralNominalState.Models source model := by
  simp [Models, Compatible]

/-- A conflict at actual nominal occurrences cannot be hidden by widening
their descriptor bounds. This holds for arbitrary full-carrier assignments. -/
theorem incompatible_occurrences_excluded (state : State)
    (model : GeneralNominalCommonBridge.Assignment) (first last : Binding state.source)
    (one : first ∈ state.bindings) (two : last ∈ state.bindings) (same : first.name = last.name)
    (a b : Argument) (ha : Observes model first.origin a) (hb : Observes model last.origin b)
    (different : ¬ ArgumentEquivalent a b) : ¬ Models state model := by
  intro models
  exact different (equal_all_observations model _ _ (models.2.2 first one last two same) a b ha hb)

end Yulang.GeneralNominalProjections
