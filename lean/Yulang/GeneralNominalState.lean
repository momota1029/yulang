import Yulang.GeneralNominalIdentities
import Yulang.GeneralNominalCommonBridge
import Yulang.GeneralSourceK2
import Yulang.GeneralDeclarationDemands

/-! A conservative nominal extension of the shared source snapshot. Nominal
bodies have no edges. Explicit argument intervals point into the same source
slots as ordinary atoms. Reserved identities are unknown ordinary variables;
reservation never asserts that distinct identities have distinct denotations. -/
namespace Yulang.GeneralNominalState

open Core.PresenceGeneration (Comp)
open PresenceNormalForm (Atom All)

inductive Parameter (slots : Nat) where
  | type (bounds : Fin slots × Fin slots)
  | row (bounds : Fin slots × Fin slots)
  deriving DecidableEq

def Parameter.kind : Parameter slots → GeneralDeclarationPatterns.ParameterKind
  | .type _ => .type
  | .row _ => .row

structure Descriptor (slots : Nat) where
  constructor : Nat
  declaration : GeneralDeclarationPatterns.Constructor
  arguments : List (Parameter slots)
  layout : arguments.map Parameter.kind = declaration.parameters

/-- Mathematical values of invariant parameters lie inside source intervals.
These values are model witnesses, not source slots or search substitutions. -/
def Fits (state : GeneralSourceState.State) (model : GeneralNominalCommonBridge.Assignment) : Parameter state.slots → CommonNominalFullCarrier.Argument → Prop
  | .type bounds, .inl value =>
      CommonNominalFullCarrier.Subtype (model (state.source bounds.1)).1 value ∧
      CommonNominalFullCarrier.Subtype value (model (state.source bounds.2)).1
  | .row bounds, .inr value =>
      Common.rowLe (model (state.rowSource bounds.1)).2 value ∧
      Common.rowLe value (model (state.rowSource bounds.2)).2
  | _, _ => False

inductive FitsAll (state : GeneralSourceState.State) (model : GeneralNominalCommonBridge.Assignment) :
    List (Parameter state.slots) → List CommonNominalFullCarrier.Argument → Prop
  | nil : FitsAll state model [] []
  | cons : Fits state model parameter value → FitsAll state model parameters values →
      FitsAll state model (parameter :: parameters) (value :: values)

def Denotes (state : GeneralSourceState.State) (model : GeneralNominalCommonBridge.Assignment) (slot : Fin state.slots)
    (descriptor : Descriptor state.slots) : Prop :=
  ∃ arguments : List CommonNominalFullCarrier.Argument,
    FitsAll state model descriptor.arguments arguments ∧
    CommonNominalFullCarrier.Equivalent (model (state.source slot)).1 (CommonNominalFullCarrier.nominal descriptor.declaration.name arguments)

structure State where
  base : GeneralSourceState.State
  view : GeneralNormalizedObservation.Snapshot base
  constructors : GeneralDeclarationPatterns.Constructors
  nominals : Fin base.slots → Option (Descriptor base.slots)
  catalogue : ∀ slot descriptor, nominals slot = some descriptor →
    constructors descriptor.constructor = some descriptor.declaration
  bodies_opaque : ∀ slot descriptor, nominals slot = some descriptor →
    view.heads slot = .deferred .unresolved
  seed : Nat := ((List.ofFn base.source) ++ (List.ofFn base.rowSource)).foldr max 0
  allocated : List GeneralNominalIdentities.Origin := []
  reserved : List Nat := []
  ordinary : List (Atom Nat) := []

def Models (state : State) (model : GeneralNominalCommonBridge.Assignment) : Prop :=
  GeneralNominalCommonBridge.Models state.base model ∧
    (∀ slot descriptor, state.nominals slot = some descriptor → Denotes state.base model slot descriptor) ∧
    All CommonNominalFullCarrier.model model state.ordinary

abbrev embed (base : GeneralSourceState.State) (view : GeneralNormalizedObservation.Snapshot base) (constructors : GeneralDeclarationPatterns.Constructors) : State where
  base := base
  view := view
  constructors := constructors
  nominals := fun _ => none
  catalogue := by intro _ _ impossible; cases impossible
  bodies_opaque := by intro _ _ impossible; cases impossible

theorem embed_models (base : GeneralSourceState.State) (view : GeneralNormalizedObservation.Snapshot base) (constructors : GeneralDeclarationPatterns.Constructors)
    (model : GeneralSourceState.Assignment) :
    Models (embed base view constructors) (GeneralNominalCommonBridge.lift model) ↔ GeneralSourceState.Models base model := by
  simp [Models, embed, GeneralNominalCommonBridge.models_exact]

theorem normalized_models (state : State) (model : GeneralNominalCommonBridge.Assignment) (models : Models state model) :
    GeneralNominalCommonBridge.ObservationModels state.view model := GeneralNominalCommonBridge.observation_models state.view model models.1

theorem nominal_models (state : State) (model : GeneralNominalCommonBridge.Assignment) (models : Models state model)
    (slot : Fin state.base.slots) (descriptor : Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor) : Denotes state.base model slot descriptor :=
  models.2.1 slot descriptor recorded

def rowSources : Core.PresenceGeneration.RowTerm Nat → List Nat
  | .var name => [name]
  | .empty => []
  | .join first last => rowSources first ++ rowSources last

def typeSources : Core.PresenceGeneration.TyTerm Nat → List Nat
  | .var name => [name]
  | .union first last | .inter first last | .pair first last | .record _ first last |
      .recordDefault _ first last => typeSources first ++ typeSources last
  | .required _ child | .variant _ child => typeSources child
  | .arrow first incoming last outgoing =>
      typeSources first ++ rowSources incoming ++ typeSources last ++ rowSources outgoing
  | _ => []

def atomSources : Atom Nat → List Nat
  | .tyLe first last => typeSources first ++ typeSources last
  | .rowLe first last => rowSources first ++ rowSources last

def sources (state : State) : List Nat :=
  List.ofFn state.base.source ++ List.ofFn state.base.rowSource ++ state.reserved ++
    state.ordinary.flatMap atomSources

def Linked (state : State) (demand : GeneralSourceState.Demand roles) : Prop :=
  (∀ index, (demand.arguments index).1 ∈ sources state ∧ (demand.arguments index).2 ∈ sources state) ∧
  ∀ output ∈ demand.outputs, output.target ∈ sources state

def Known (state : State) (source : Nat) : Prop :=
  ∃ slot, state.base.source slot = source ∧
    (state.view.graph slot ≠ .unresolved ∨ ∃ descriptor, state.nominals slot = some descriptor)

def RootPending (state : State) (demand : GeneralSourceState.Demand roles) : Prop :=
  ∃ index, ¬ Known state (demand.arguments index).1

/-- Recurrence is certified only in the existing normalized structural graph.
An edge through a nominal descriptor stays unknown in this graph. Inspection
may enter an explicit nominal argument separately; no nominal body is entered. -/
def AtK2 (state : State) (slot : Fin state.base.slots) : Prop :=
  GeneralSourceK2.Complete state.view slot ∧ GeneralSourceBoundary.GraphK2 state.view.graph slot

def RootK2 (state : State) (demand : GeneralSourceState.Demand roles) : Prop :=
  Linked state demand ∧ ¬ RootPending state demand ∧
    ∃ index slot, state.base.source slot = (demand.arguments index).1 ∧ AtK2 state slot

theorem atK2_recurrence (state : State) (slot : Fin state.base.slots) (cycle : AtK2 state slot) :
    GeneralSourceK2.RecursAt state.view slot := GeneralSourceK2.graphK2_sound state.view slot cycle.2

theorem pending_excludes_K2 (state : State) (demand : GeneralSourceState.Demand roles)
    (pending : RootPending state demand) : ¬ RootK2 state demand := fun cycle => cycle.2.1 pending

theorem linked_embed (base : GeneralSourceState.State) (view : GeneralNormalizedObservation.Snapshot base)
    (constructors : GeneralDeclarationPatterns.Constructors) (demand : GeneralSourceState.Demand roles)
    (linked : GeneralSourceState.Linked base demand) : Linked (embed base view constructors) demand := by
  constructor
  · intro index
    obtain ⟨pair, _, equal⟩ := linked.1 index
    rw [← equal]
    constructor
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_ofFn.mpr ⟨pair.1,rfl⟩)))
    · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_ofFn.mpr ⟨pair.2,rfl⟩)))
  · intro output member
    obtain ⟨slot,equal⟩ := linked.2 output member
    rw [← equal]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_ofFn.mpr ⟨slot,rfl⟩)))

theorem embed_pending (base : GeneralSourceState.State) (view : GeneralNormalizedObservation.Snapshot base) (constructors : GeneralDeclarationPatterns.Constructors)
    (demand : GeneralSourceState.Demand roles) :
    RootPending (embed base view constructors) demand ↔
      GeneralSourceK2.RootPending view demand (GeneralDeclarationDemands.needed roles demand) := by
  simp only [RootPending, Known, embed, reduceCtorEq, exists_false, or_false,
    GeneralSourceK2.RootPending, GeneralSourceK2.Known]
  constructor
  · rintro ⟨index, pending⟩
    exact ⟨index, GeneralDeclarationDemands.every_input_needed demand index, pending⟩
  · rintro ⟨index, _, pending⟩
    exact ⟨index, pending⟩

theorem embed_K2 (base : GeneralSourceState.State) (view : GeneralNormalizedObservation.Snapshot base) (constructors : GeneralDeclarationPatterns.Constructors)
    (slot : Fin base.slots) :
    AtK2 (embed base view constructors) slot ↔
      GeneralSourceK2.Complete view slot ∧ GeneralSourceBoundary.GraphK2 view.graph slot := Iff.rfl

/-- Extending ordinary equations and reserving identities is candidate private.
It neither commits a selected implementation nor resolves a where child. -/
def extend (state : State) (reserved : List Nat) (atoms : List (Atom Nat)) : State :=
  { state with reserved := state.reserved ++ reserved, ordinary := state.ordinary ++ atoms }

theorem extend_models (state : State) (reserved : List Nat) (atoms : List (Atom Nat))
    (model : GeneralNominalCommonBridge.Assignment) :
    Models (extend state reserved atoms) model ↔ Models state model ∧ All CommonNominalFullCarrier.model model atoms := by
  simp only [Models, extend, PresenceNormalForm.all_append]
  simp only [and_assoc]

theorem extend_pending (state : State) (reserved : List Nat) (atoms : List (Atom Nat))
    (demand : GeneralSourceState.Demand roles) :
    RootPending (extend state reserved atoms) demand ↔ RootPending state demand := Iff.rfl

/-- Equality to an existing endpoint is proved from both interval directions;
no fresh centre is introduced. -/
theorem fits_existing_endpoint (state : GeneralSourceState.State)
    (model : GeneralNominalCommonBridge.Assignment) (slot : Fin state.slots)
    (value : CommonNominalFullCarrier.Ty)
    (fits : Fits state model (.type (slot,slot)) (.inl value)) :
    CommonNominalFullCarrier.Equivalent value (model (state.source slot)).1 := ⟨fits.2,fits.1⟩

theorem singleton_nominal_congr (name : Nat) (first last : CommonNominalFullCarrier.Ty)
    (same : CommonNominalFullCarrier.Equivalent first last) :
    CommonNominalFullCarrier.Equivalent
      (CommonNominalFullCarrier.nominal name [.inl first])
      (CommonNominalFullCarrier.nominal name [.inl last]) := by
  have arguments : CommonNominalFullCarrier.ArgumentsEquivalent [.inl first] [.inl last] := by
    intro index a b left right
    cases index with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at left right
        subst a; subst b
        exact same
    | succ index => simp at left
  have reverse : CommonNominalFullCarrier.ArgumentsEquivalent [.inl last] [.inl first] := by
    intro index a b left right
    cases index with
    | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at left right
        subst a; subst b
        exact ⟨same.2,same.1⟩
    | succ index => simp at left
  exact ⟨(CommonNominalFullCarrier.nominal_regular_invariant_exact ..).mpr ⟨rfl,rfl,arguments⟩,
    (CommonNominalFullCarrier.nominal_regular_invariant_exact ..).mpr ⟨rfl,rfl,reverse⟩⟩

theorem denotes_singleton_exact (state : GeneralSourceState.State)
    (model : GeneralNominalCommonBridge.Assignment) (root endpoint : Fin state.slots)
    (descriptor : Descriptor state.slots) (arguments : descriptor.arguments = [.type (endpoint,endpoint)]) :
    Denotes state model root descriptor ↔ CommonNominalFullCarrier.Equivalent
      (model (state.source root)).1
      (CommonNominalFullCarrier.nominal descriptor.declaration.name [.inl (model (state.source endpoint)).1]) := by
  constructor
  · rintro ⟨actual, fits, rootSame⟩
    rw [arguments] at fits
    cases fits with
    | cons head tail =>
        cases tail
        rename_i value
        cases value with
        | inr row => exact False.elim head
        | inl value =>
            have same := singleton_nominal_congr descriptor.declaration.name value _
              (fits_existing_endpoint state model endpoint value head)
            exact ⟨CommonNominalFullCarrier.subtype_trans rootSame.1 same.1,
              CommonNominalFullCarrier.subtype_trans same.2 rootSame.2⟩
  · intro same
    refine ⟨[.inl (model (state.source endpoint)).1], ?_, same⟩
    rw [arguments]
    exact .cons ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩ .nil

end Yulang.GeneralNominalState
