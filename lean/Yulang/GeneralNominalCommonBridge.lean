import Yulang.CommonNominalFullModelMap
import Yulang.CommonNominalFullConstructors
import Yulang.GeneralNormalizedObservation

/-! Full nominal interpretations of the existing shared equations. Old source
identities, row identities, atoms and normalization derivations are retained.
Recorded head and interval equations are explicit in the extended interpretation:
the old Common-only certificates are not applied to arbitrary nominal values. -/
namespace Yulang.GeneralNominalCommonBridge

open Core.PresenceGeneration (Comp TyTerm RowTerm)
open PresenceNormalForm (Atom All)

abbrev Assignment := Nat → Comp CommonNominalFullCarrier.model

def lift (assignment : α → Comp Common.model) : α → Comp CommonNominalFullCarrier.model :=
  fun slot => (CommonNominalFullModelMap.value (assignment slot).1, (assignment slot).2)

@[simp] theorem row_eval (assignment : α → Comp Common.model) (term : RowTerm α) :
    term.eval CommonNominalFullCarrier.model (lift assignment) = term.eval Common.model assignment := by
  induction term <;> simp_all [RowTerm.eval, lift, CommonNominalFullCarrier.model, Common.model]

@[simp] theorem type_eval (assignment : α → Comp Common.model) (term : TyTerm α) :
    term.eval CommonNominalFullCarrier.model (lift assignment) = CommonNominalFullModelMap.value (term.eval Common.model assignment) := by
  induction term <;> simp only [TyTerm.eval, * , row_eval] <;> rfl

@[simp] theorem atom_exact (assignment : α → Comp Common.model) (atom : Atom α) :
    atom.Holds CommonNominalFullCarrier.model (lift assignment) ↔ atom.Holds Common.model assignment := by
  cases atom with
  | tyLe first last =>
      change CommonNominalFullCarrier.Subtype _ _ ↔ Common.Subtype _ _
      rw [type_eval, type_eval]
      exact CommonNominalFullModelMap.subtype_exact _ _
  | rowLe first last =>
      change Common.rowLe _ _ ↔ Common.rowLe _ _
      rw [row_eval, row_eval]

@[simp] theorem atoms_exact (assignment : α → Comp Common.model) (atoms : List (Atom α)) :
    All CommonNominalFullCarrier.model (lift assignment) atoms ↔ All Common.model assignment atoms := by
  simp only [All, atom_exact]

def assignment (state : GeneralSourceState.State) (model : Assignment) : Fin state.slots → Comp CommonNominalFullCarrier.model :=
  fun slot => ((model (state.source slot)).1, (model (state.rowSource slot)).2)

/-- The existing recorded equations are retained with their full-carrier meaning. -/
def Models (state : GeneralSourceState.State) (model : Assignment) : Prop :=
  All CommonNominalFullCarrier.model (assignment state model) state.ordinary ∧
  (∀ slot term, (state.heads slot).equation = some term →
    CommonNominalFullCarrier.Equivalent (model (state.source slot)).1 (term.eval CommonNominalFullCarrier.model (assignment state model))) ∧
  ∀ pair ∈ state.intervals,
    CommonNominalFullCarrier.Subtype (model (state.source pair.1)).1 (model (state.source pair.2)).1

@[simp] theorem assignment_lift (state : GeneralSourceState.State) (model : GeneralSourceState.Assignment) :
    assignment state (lift model) = lift (state.assignment model) := rfl

theorem models_exact (state : GeneralSourceState.State) (model : GeneralSourceState.Assignment) :
    Models state (lift model) ↔ GeneralSourceState.Models state model := by
  constructor
  · rintro ⟨ordinary, heads, intervals⟩
    refine ⟨(atoms_exact _ _).mp ordinary, ?_, ?_⟩
    · intro slot term recorded
      have same := heads slot term recorded
      change CommonNominalFullCarrier.Equivalent (CommonNominalFullModelMap.value _)
        (term.eval CommonNominalFullCarrier.model (lift (state.assignment model))) at same
      rw [type_eval] at same
      exact ⟨(CommonNominalFullModelMap.subtype_exact _ _).mp same.1,
        (CommonNominalFullModelMap.subtype_exact _ _).mp same.2⟩
    · intro pair member
      exact (CommonNominalFullModelMap.subtype_exact _ _).mp (intervals pair member)
  · rintro ⟨ordinary, heads, intervals⟩
    refine ⟨(atoms_exact _ _).mpr ordinary, ?_, ?_⟩
    · intro slot term recorded
      change CommonNominalFullCarrier.Equivalent (CommonNominalFullModelMap.value _)
        (term.eval CommonNominalFullCarrier.model (lift (state.assignment model)))
      rw [type_eval]
      have same := heads slot term recorded
      exact ⟨(CommonNominalFullModelMap.subtype_exact _ _).mpr same.1,
        (CommonNominalFullModelMap.subtype_exact _ _).mpr same.2⟩
    · intro pair member
      exact (CommonNominalFullModelMap.subtype_exact _ _).mpr (intervals pair member)


theorem finite_shadow (label : Nat) (a b tail : CommonNominalFullDemand.Ty CommonNominalFullCarrier.Row) :
    CommonNominalFullDemand.ProducerEq Common.rowLe
      (.record label a (.record label b tail)) (.record label a tail) := by
  apply (CommonNominalFullDemand.producerEq_iff_probe _ _).mpr
  intro rank env obs
  cases rank <;> cases obs <;> simp [CommonNominalFullDemand.ProbeAt,
    CommonNominalFullDemand.ProbeStep, CommonNominalFullDemand.MaskedProbeStep]
  all_goals split <;> simp_all

theorem finite_swap (first last : Nat) (different : first ≠ last)
    (a b tail : CommonNominalFullDemand.Ty CommonNominalFullCarrier.Row) :
    CommonNominalFullDemand.ProducerEq Common.rowLe (.record first a (.record last b tail))
      (.record last b (.record first a tail)) := by
  have observed (rank : Nat) (env : CommonNominalFullDemand.Environment CommonNominalFullCarrier.Row)
      (obs : CommonNominalFullDemand.Observation CommonNominalFullCarrier.Row) :
      CommonNominalFullDemand.ProbeAt Common.rowLe rank env (.record first a (.record last b tail)) obs ↔
        CommonNominalFullDemand.ProbeAt Common.rowLe rank env (.record last b (.record first a tail)) obs := by
    cases rank <;> cases obs <;> simp only [CommonNominalFullDemand.ProbeAt,
      CommonNominalFullDemand.ProbeStep, CommonNominalFullDemand.MaskedProbeStep]
    all_goals try rfl
    all_goals rename_i query payload
    all_goals by_cases left : query = first <;> by_cases right : query = last <;>
      simp_all [CommonNominalFullDemand.maskedProbeStep_or_trivial]
  exact (CommonNominalFullDemand.producerEq_iff_probe _ _).mpr observed

theorem shadow (label : Nat) (a b tail : CommonNominalFullCarrier.Ty) :
    CommonNominalFullCarrier.Equivalent (CommonNominalFullCarrier.record label a (CommonNominalFullCarrier.record label b tail)) (CommonNominalFullCarrier.record label a tail) :=
  ⟨fun _ => (finite_shadow label _ _ _).1, fun _ => (finite_shadow label _ _ _).2⟩

theorem swap (first last : Nat) (different : first ≠ last) (a b tail : CommonNominalFullCarrier.Ty) :
    CommonNominalFullCarrier.Equivalent (CommonNominalFullCarrier.record first a (CommonNominalFullCarrier.record last b tail))
      (CommonNominalFullCarrier.record last b (CommonNominalFullCarrier.record first a tail)) :=
  ⟨fun _ => (finite_swap first last different _ _ _).1,
    fun _ => (finite_swap first last different _ _ _).2⟩

theorem variant_merge (tag : Nat) (a b : CommonNominalFullCarrier.Ty) :
    CommonNominalFullCarrier.Equivalent (.union (CommonNominalFullCarrier.variant tag a) (CommonNominalFullCarrier.variant tag b)) (CommonNominalFullCarrier.variant tag (.union a b)) := by
  constructor <;> intro depth <;> cases depth with
  | zero =>
      simp only [CommonNominalFullCarrier.observeTy, CommonNominalFullCarrier.variant, CommonNominalSyntax.Layer.evalAt, CommonNominalSyntax.observe]
      first
      | exact (CommonNominalFullDemand.producerEq_union_absorb (CommonNominalFullDemand.producerLe_refl _)).1
      | exact (CommonNominalFullDemand.producerEq_union_absorb (CommonNominalFullDemand.producerLe_refl _)).2
  | succ depth =>
      first
      | exact (CommonNominalFullDemand.variant_union tag _ _).2
      | exact (CommonNominalFullDemand.variant_union tag _ _).1

theorem rewrites_sound (derivation : GeneralNormalizedObservation.Rewrites state first last) (model : Assignment)
    (models : Models state model) :
    CommonNominalFullCarrier.Equivalent (first.eval CommonNominalFullCarrier.model (assignment state model))
      (last.eval CommonNominalFullCarrier.model (assignment state model)) := by
  induction derivation with
  | refl => exact ⟨CommonNominalFullCarrier.subtype_refl _, CommonNominalFullCarrier.subtype_refl _⟩
  | trans _ _ left right => exact ⟨CommonNominalFullCarrier.subtype_trans left.1 right.1, CommonNominalFullCarrier.subtype_trans right.2 left.2⟩
  | head recorded => exact models.2.1 _ _ recorded
  | ordinary forward backward => exact ⟨models.1 _ forward, models.1 _ backward⟩
  | pair _ _ left right => exact ⟨(CommonNominalFullCarrier.common_pair_iff ..).mpr ⟨left.1,right.1⟩,
      (CommonNominalFullCarrier.common_pair_iff ..).mpr ⟨left.2,right.2⟩⟩
  | record _ _ payload tail => exact ⟨CommonNominalFullCarrier.common_record_mono _ payload.1 tail.1,
      CommonNominalFullCarrier.common_record_mono _ payload.2 tail.2⟩
  | variant _ payload => exact ⟨(CommonNominalFullCarrier.common_variant_iff ..).mpr payload.1, (CommonNominalFullCarrier.common_variant_iff ..).mpr payload.2⟩
  | union _ _ left right => exact ⟨CommonNominalFullCarrier.common_union_mono left.1 right.1, CommonNominalFullCarrier.common_union_mono left.2 right.2⟩
  | required => exact ⟨CommonNominalFullCarrier.subtype_refl _, CommonNominalFullCarrier.subtype_refl _⟩
  | shadow => exact shadow ..
  | swap different => exact swap _ _ different _ _ _
  | merge => exact variant_merge ..
  | idempotent => exact ⟨(CommonNominalFullCarrier.common_union_is_join ..).mpr ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩,
      fun _ => CommonNominalFullDemand.producerLe_union_left _ _⟩

def ObservationModels (view : GeneralNormalizedObservation.Snapshot state) (model : Assignment) : Prop :=
  ∀ slot term, (view.heads slot).term = some term →
    CommonNominalFullCarrier.Equivalent (model (state.source slot)).1 (term.eval CommonNominalFullCarrier.model (assignment state model))

theorem observation_models (view : GeneralNormalizedObservation.Snapshot state) (model : Assignment)
    (models : Models state model) : ObservationModels view model :=
  fun slot term recorded => rewrites_sound (view.checked slot term recorded) model models

theorem normalization_preserves (view : GeneralNormalizedObservation.Snapshot state) (model : Assignment) :
    Models state model ∧ ObservationModels view model ↔ Models state model :=
  ⟨And.left, fun models => ⟨models, observation_models view model models⟩⟩

end Yulang.GeneralNominalCommonBridge
