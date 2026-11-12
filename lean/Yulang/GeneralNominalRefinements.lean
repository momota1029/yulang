import Yulang.GeneralNominalRecursiveCandidates

/-! Checked source-preserving refinement on the full nominal carrier. Old
normalized equations are transported by source identities; explicit nominal
arguments and the global ordinary constraints are retained. -/
namespace Yulang.GeneralNominalRefinements

open GeneralNominalState (State Parameter Descriptor)
open GeneralNominalCommonBridge (Assignment)
open Core.PresenceGeneration (TyTerm)

def renameParameter (embed : Fin first → Fin last) : Parameter first → Parameter last
  | .type bounds => .type (embed bounds.1,embed bounds.2)
  | .row bounds => .row (embed bounds.1,embed bounds.2)

theorem rename_kind (embed : Fin first → Fin last) (parameter : Parameter first) :
    (renameParameter embed parameter).kind = parameter.kind := by cases parameter <;> rfl

def renameDescriptor (embed : Fin first → Fin last) (descriptor : Descriptor first) : Descriptor last where
  constructor := descriptor.constructor
  declaration := descriptor.declaration
  arguments := descriptor.arguments.map (renameParameter embed)
  layout := by simpa only [List.map_map,Function.comp_def,rename_kind] using descriptor.layout

structure Refines (before after : State) where
  base : GeneralSourceState.Refines before.base after.base
  heads : ∀ slot term, (before.base.heads slot).equation = some term →
    GeneralNormalizedObservation.Rewrites after.base (.var (base.embed slot)) (term.rename base.embed)
  nominals : ∀ slot descriptor, before.nominals slot = some descriptor →
    after.nominals (base.embed slot) = some (renameDescriptor base.embed descriptor)
  ordinary : ∀ atom ∈ before.ordinary, atom ∈ after.ordinary
  known : ∀ source, GeneralNominalState.Known before source → GeneralNominalState.Known after source
  reserved : ∀ source ∈ before.reserved, source ∈ after.reserved
  allocated : ∀ key ∈ before.allocated, key ∈ after.allocated
  seed : after.seed = before.seed
  constructors : after.constructors = before.constructors

theorem assignment_transport (refinement : Refines before after) (model : Assignment) :
    GeneralNominalCommonBridge.assignment after.base model ∘ refinement.base.embed =
      GeneralNominalCommonBridge.assignment before.base model := by
  funext slot
  simp only [Function.comp_def,GeneralNominalCommonBridge.assignment,
    refinement.base.source,refinement.base.rowSource]

theorem fits_transport (refinement : Refines before after) (model : Assignment)
    (parameter : Parameter before.base.slots) (value : CommonNominalFullCarrier.Argument) :
    GeneralNominalState.Fits after.base model (renameParameter refinement.base.embed parameter) value ↔
      GeneralNominalState.Fits before.base model parameter value := by
  cases parameter <;> cases value <;>
    simp [renameParameter,GeneralNominalState.Fits,refinement.base.source,refinement.base.rowSource]

theorem fitsAll_transport (refinement : Refines before after) (model : Assignment)
    (parameters : List (Parameter before.base.slots)) (values : List CommonNominalFullCarrier.Argument)
    (valid : GeneralNominalState.FitsAll after.base model
      (parameters.map (renameParameter refinement.base.embed)) values) :
    GeneralNominalState.FitsAll before.base model parameters values := by
  induction parameters generalizing values with
  | nil => cases valid; exact .nil
  | cons parameter rest ih =>
      cases valid with
      | cons head tail => exact .cons ((fits_transport refinement model parameter _).mp head) (ih _ tail)

theorem models (refinement : Refines before after) (model : Assignment)
    (valid : GeneralNominalState.Models after model) : GeneralNominalState.Models before model := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_⟩
  · intro atom member
    have transported := (PresenceNormalForm.Atom.holds_rename _ _ refinement.base.embed atom).mp
      (valid.1.1 _ (refinement.base.ordinary atom member))
    rw [assignment_transport refinement model] at transported
    exact transported
  · intro slot term recorded
    have head := GeneralNominalCommonBridge.rewrites_sound (refinement.heads slot term recorded) model valid.1
    change CommonNominalFullCarrier.Equivalent (model (after.base.source (refinement.base.embed slot))).1
      ((term.rename refinement.base.embed).eval CommonNominalFullCarrier.model
        (GeneralNominalCommonBridge.assignment after.base model)) at head
    simpa only [TyTerm.eval_rename,refinement.base.source,assignment_transport refinement model] using head
  · intro bounds member
    have bounded := valid.1.2.2 _ (refinement.base.intervals bounds member)
    simpa only [refinement.base.source] using bounded
  · intro slot descriptor recorded
    obtain ⟨values,fits,equal⟩ := valid.2.1 _ _ (refinement.nominals slot descriptor recorded)
    refine ⟨values,fitsAll_transport refinement model descriptor.arguments values fits,?_⟩
    simpa only [refinement.base.source,renameDescriptor] using equal
  · exact fun atom member => valid.2.2 atom (refinement.ordinary atom member)

theorem pending_backwards (refinement : Refines before after)
    (demand : GeneralSourceState.Demand roles) (pending : GeneralNominalState.RootPending after demand) :
    GeneralNominalState.RootPending before demand := by
  obtain ⟨index,unknown⟩ := pending
  exact ⟨index,fun known => unknown (refinement.known _ known)⟩

theorem sources (refinement : Refines before after) (source : Nat)
    (member : source ∈ GeneralNominalState.sources before) : source ∈ GeneralNominalState.sources after := by
  simp only [GeneralNominalState.sources,List.mem_append] at member ⊢
  rcases member with ((type | row) | reserved) | ordinary
  · obtain ⟨slot,equal⟩ := List.mem_ofFn.mp type
    exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨refinement.base.embed slot,(refinement.base.source slot).trans equal⟩)))
  · obtain ⟨slot,equal⟩ := List.mem_ofFn.mp row
    exact Or.inl (Or.inl (Or.inr (List.mem_ofFn.mpr ⟨refinement.base.embed slot,(refinement.base.rowSource slot).trans equal⟩)))
  · exact Or.inl (Or.inr (refinement.reserved source reserved))
  · obtain ⟨atom,present,within⟩ := List.mem_flatMap.mp ordinary
    exact Or.inr (List.mem_flatMap.mpr ⟨atom,refinement.ordinary atom present,within⟩)

theorem linked (refinement : Refines before after) (demand : GeneralSourceState.Demand roles)
    (valid : GeneralNominalState.Linked before demand) : GeneralNominalState.Linked after demand :=
  ⟨fun index => ⟨sources refinement _ (valid.1 index).1,sources refinement _ (valid.1 index).2⟩,
    fun output member => sources refinement _ (valid.2 output member)⟩

private theorem row_identity (term : Core.PresenceGeneration.RowTerm α) : term.rename id = term := by
  induction term <;> simp_all [Core.PresenceGeneration.RowTerm.rename]

private theorem type_identity (term : TyTerm α) : term.rename id = term := by
  induction term <;> simp_all [TyTerm.rename,row_identity]

private theorem atom_identity (atom : PresenceNormalForm.Atom α) : atom.rename id = atom := by
  cases atom <;> simp [PresenceNormalForm.Atom.rename,type_identity,row_identity]

def refl (state : State) : Refines state state where
  base := ⟨id,fun _ => rfl,fun _ => rfl,by intro atom member; simpa only [atom_identity] using member,
    fun _ known => known,fun _ member => member⟩
  heads := by intro slot term recorded; simpa only [type_identity,id_eq] using GeneralNormalizedObservation.Rewrites.head recorded
  nominals := by
    intro slot descriptor recorded
    have identity : renameParameter (id : Fin state.base.slots → Fin state.base.slots) = id := by
      funext parameter; cases parameter <;> rfl
    have renamed : renameDescriptor id descriptor = descriptor := by
      cases descriptor
      simp [renameDescriptor,identity]
    simpa only [renamed,id_eq] using recorded
  ordinary := fun _ member => member
  known := fun _ known => known
  reserved := fun _ member => member
  allocated := fun _ member => member
  seed := rfl
  constructors := rfl

def installed (registry : GeneralDeclarations.Registry) (context : GeneralNominalCandidates.Context)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : GeneralDeclarations.Declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) :
    Refines context.state (GeneralNominalRecursiveCandidates.privateState registry context root declaration bounds) where
  base := (refl context.state).base
  heads := (refl context.state).heads
  nominals := (refl context.state).nominals
  ordinary := fun _ member => List.mem_append_left _ (List.mem_append_left _ member)
  known := fun _ known => known
  reserved := fun _ member => List.mem_append_left _ (List.mem_append_left _ member)
  allocated := fun _ member => List.mem_append_left _ member
  seed := rfl
  constructors := rfl

def extended (state : State) (reserved : List Nat) (atoms : List (PresenceNormalForm.Atom Nat)) :
    Refines state (GeneralNominalState.extend state reserved atoms) where
  base := (refl state).base
  heads := (refl state).heads
  nominals := (refl state).nominals
  ordinary := fun _ member => List.mem_append_left _ member
  known := fun _ known => known
  reserved := fun _ member => List.mem_append_left _ member
  allocated := fun _ member => member
  seed := rfl
  constructors := rfl

end Yulang.GeneralNominalRefinements
