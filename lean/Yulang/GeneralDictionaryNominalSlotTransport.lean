import Yulang.GeneralNominalState

/-!
# Exact syntactic transport of nominal snapshots for dictionary localization

The target snapshot and its separate type/row maps are supplied. This certificate
checks renamed storage, rather than assuming model preservation. It does not
construct slots, choose row identities, or implement a language update. Fresh
slots carry no extra head, descriptor or interval constraint. Readiness and
normalization graph equivalence are not consequences claimed in this module.
-/
namespace Yulang.GeneralDictionaryNominalSlotTransport
open Core.PresenceGeneration (TyTerm)
open PresenceNormalForm (Atom All)
open GeneralNominalState (Parameter Descriptor Fits FitsAll Denotes)
open GeneralNominalCommonBridge (Assignment assignment)

/-- Type and row bounds both retain their own kind under reindexing. -/
def parameter (embed : Fin n → Fin m) : Parameter n → Parameter m
  | .type bounds => .type (embed bounds.1, embed bounds.2)
  | .row bounds => .row (embed bounds.1, embed bounds.2)

@[simp] theorem parameter_kind (embed : Fin n → Fin m) (value : Parameter n) :
    (parameter embed value).kind = value.kind := by cases value <;> rfl

def descriptor (embed : Fin n → Fin m) (value : Descriptor n) : Descriptor m where
  constructor := value.constructor
  declaration := value.declaration
  arguments := value.arguments.map (parameter embed)
  layout := by simpa only [List.map_map, Function.comp_def, parameter_kind] using value.layout

/-- Exact images forbid extra constraints on newly represented identities.
There are no semantic Models premises in this certificate. -/
structure Transport (before after : GeneralNominalState.State) where
  embed : Fin before.base.slots → Fin after.base.slots
  source : ∀ slot, after.base.source (embed slot) = before.base.source slot
  rowSource : ∀ slot, after.base.rowSource (embed slot) = before.base.rowSource slot
  atoms : after.base.ordinary = before.base.ordinary.map (Atom.rename embed)
  heads : ∀ slot term, (after.base.heads slot).equation = some term ↔
    ∃ old original, (before.base.heads old).equation = some original ∧
      slot = embed old ∧ term = original.rename embed
  intervals : after.base.intervals = before.base.intervals.map (fun pair => (embed pair.1, embed pair.2))
  nominals : ∀ slot value, after.nominals slot = some value ↔
    ∃ old original, before.nominals old = some original ∧
      slot = embed old ∧ value = descriptor embed original
  constructors : after.constructors = before.constructors
  seed : after.seed = before.seed
  allocated : after.allocated = before.allocated
  reserved : after.reserved = before.reserved
  ordinary : after.ordinary = before.ordinary

variable {before after : GeneralNominalState.State}

theorem embed_injective (transport : Transport before after) : Function.Injective transport.embed := by
  intro first last same
  apply before.base.source_injective
  rw [← transport.source first, ← transport.source last, same]

theorem assignment_embed (transport : Transport before after) (model : Assignment) :
    assignment after.base model ∘ transport.embed = assignment before.base model := by
  funext slot
  simp only [Function.comp_def, assignment, transport.source, transport.rowSource]

/-- Arbitrary nominal assignments, including values outside the old Common image. -/
theorem term_eval (transport : Transport before after) (model : Assignment)
    (term : TyTerm (Fin before.base.slots)) :
    (term.rename transport.embed).eval CommonNominalFullCarrier.model (assignment after.base model) =
      term.eval CommonNominalFullCarrier.model (assignment before.base model) := by
  rw [TyTerm.eval_rename, assignment_embed]

theorem fits_parameter (transport : Transport before after) (model : Assignment)
    (bounds : Parameter before.base.slots) (value : CommonNominalFullCarrier.Argument) :
    Fits after.base model (parameter transport.embed bounds) value ↔ Fits before.base model bounds value := by
  cases bounds <;> cases value <;> simp only [parameter, Fits, transport.source, transport.rowSource]

theorem fitsAll_parameters (transport : Transport before after) (model : Assignment)
    (bounds : List (Parameter before.base.slots)) (values : List CommonNominalFullCarrier.Argument) :
    FitsAll after.base model (bounds.map (parameter transport.embed)) values ↔
      FitsAll before.base model bounds values := by
  induction bounds generalizing values with
  | nil =>
      constructor <;> intro h <;> cases h <;> exact .nil
  | cons first rest ih =>
      constructor
      · intro h
        cases h with
        | cons head tail => exact .cons ((fits_parameter transport model first _).mp head) ((ih _).mp tail)
      · intro h
        cases h with
        | cons head tail => exact .cons ((fits_parameter transport model first _).mpr head) ((ih _).mpr tail)

theorem denotes_descriptor (transport : Transport before after) (model : Assignment)
    (slot : Fin before.base.slots) (value : Descriptor before.base.slots) :
    Denotes after.base model (transport.embed slot) (descriptor transport.embed value) ↔
      Denotes before.base model slot value := by
  simp only [Denotes, descriptor, transport.source, fitsAll_parameters]

/-- No constraints are lost and no new model restrictions are introduced by the
certified change of slot representation, including recorded heads and intervals. -/
theorem base_models (transport : Transport before after) (model : Assignment) :
    GeneralNominalCommonBridge.Models after.base model ↔
      GeneralNominalCommonBridge.Models before.base model := by
  have atoms : All CommonNominalFullCarrier.model (assignment after.base model) after.base.ordinary ↔
      All CommonNominalFullCarrier.model (assignment before.base model) before.base.ordinary := by
    rw [transport.atoms]
    simp only [All, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      Atom.holds_rename, assignment_embed]
  constructor
  · rintro ⟨ordinary, heads, intervals⟩
    refine ⟨atoms.mp ordinary, ?_, ?_⟩
    · intro slot term recorded
      have valid := heads (transport.embed slot) (term.rename transport.embed)
        ((transport.heads _ _).mpr ⟨slot, term, recorded, rfl, rfl⟩)
      simpa only [transport.source, term_eval] using valid
    · intro pair member
      have valid := intervals (transport.embed pair.1, transport.embed pair.2)
        (transport.intervals ▸ List.mem_map.mpr ⟨pair, member, rfl⟩)
      simpa only [transport.source] using valid
  · rintro ⟨ordinary, heads, intervals⟩
    refine ⟨atoms.mpr ordinary, ?_, ?_⟩
    · intro slot term recorded
      obtain ⟨old, original, wasRecorded, rfl, rfl⟩ := (transport.heads _ _).mp recorded
      simpa only [transport.source, term_eval] using heads old original wasRecorded
    · intro pair member
      rw [transport.intervals] at member
      obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
      simpa only [transport.source] using intervals old oldMember

/-- The same global assignment is preserved in both directions, with nominal
parameter witnesses and global equations retained. The target is not computed. -/
theorem models (transport : Transport before after) (model : Assignment) :
    GeneralNominalState.Models after model ↔ GeneralNominalState.Models before model := by
  have descriptors :
      (∀ slot value, after.nominals slot = some value → Denotes after.base model slot value) ↔
      (∀ slot value, before.nominals slot = some value → Denotes before.base model slot value) := by
    constructor
    · intro valid slot value recorded
      exact (denotes_descriptor transport model slot value).mp
        (valid (transport.embed slot) (descriptor transport.embed value)
          ((transport.nominals _ _).mpr ⟨slot, value, recorded, rfl, rfl⟩))
    · intro valid slot value recorded
      obtain ⟨old, original, wasRecorded, rfl, rfl⟩ := (transport.nominals _ _).mp recorded
      exact (denotes_descriptor transport model old original).mpr (valid old original wasRecorded)
  simp only [GeneralNominalState.Models, base_models transport, descriptors, transport.ordinary]

/-- No former source slot can be merged with another during this transport. -/
theorem source_identity (transport : Transport before after) (first last : Fin before.base.slots) :
    after.base.source (transport.embed first) = after.base.source (transport.embed last) ↔ first = last := by
  rw [transport.source, transport.source]
  exact ⟨fun equal => before.base.source_injective equal, congrArg before.base.source⟩

end Yulang.GeneralDictionaryNominalSlotTransport
