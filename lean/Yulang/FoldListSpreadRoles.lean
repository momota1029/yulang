import Yulang.FoldListSpread

/-!
# Accepted rigid Fold slots in the resolved spread typing rule

`foldGoal` is the supplied resolved encoding of the container/item role demand.
This module does not choose a source role identifier or an associated-type
encoding. Each slot contains actual success of the checked rigid resolver.
The resolver's exact selected plan indexes a supplied, locally typed protocol
body; both traversal consumers can retain that same driver and effect row.

The protocol registry is a method-elaboration contract, not an inferred source
implementation. In particular the source `Fold.fold` method is higher order:
the current `for_in` passes a Unit accumulator. Replacing that with a list
accumulator would require a separate proof for arbitrary method bodies. A
future source/protocol correspondence must account for callback observations
and accumulator behaviour; no new source law is postulated here.
-/

namespace Yulang.FoldListSpreadRoles

open Directed SignatureRequests FoldListSpread

structure Slot (visible : List Roles.Impl) (foldGoal : Roles.Term → Roles.Term → Roles.Goal) where
  container : Roles.Term
  item : Roles.Term
  accepted : CheckedRoles.resolve visible (foldGoal container item) = .answer .resolved

structure Body (n : Nat) (signature : Signature Key) (Value Cursor : Type)
    (container item : Value → Prop) where
  driver : FoldTraversal.Driver n signature Value Value Cursor
  row : Occurrence n Key → Prop
  valid : Cursor → Prop
  start_typed : ∀ value, container value → valid (driver.start value)
  safe : FoldTraversal.Safe driver.observe valid item row

abbrev Registry (n : Nat) (signature : Signature Key) (Value Cursor : Type)
    (denote : Roles.Term → Value → Prop) :=
  (container item : Roles.Term) → RoleDictionaries.Plan → Body n signature Value Cursor (denote container) (denote item)

variable {Key Value Cursor Source Conversion SourceState : Type} {n : Nat} {signature : Signature Key}
variable {visible : List Roles.Impl} {foldGoal : Roles.Term → Roles.Term → Roles.Goal}
variable {denote : Roles.Term → Value → Prop}

def selected (registry : Registry n signature Value Cursor denote) (slot : Slot visible foldGoal) :
    Body n signature Value Cursor (denote slot.container) (denote slot.item) :=
  registry slot.container slot.item
    (FoldTraversal.acceptedDictionary visible (foldGoal slot.container slot.item) slot.accepted).erase

theorem selected_exact (registry : Registry n signature Value Cursor denote) (slot : Slot visible foldGoal)
    (dictionary : RoleDictionaries.Dictionary visible (foldGoal slot.container slot.item)) :
    selected registry slot = registry slot.container slot.item dictionary.erase := by
  unfold selected
  rw [FoldTraversal.accepted_plan_unique visible _ slot.accepted dictionary]

/-- Source syntax judgments remain independent of the machine observation.
Only local preservation/progress contracts connect their evaluation states. -/
structure SourceLayer (n : Nat) (signature : Signature Key) (Source Conversion Value State : Type) where
  start : Source → State
  observe : Process n signature Value State
  convert : Conversion → Value → Value
  Typed : Source → (Value → Prop) → (Occurrence n Key → Prop) → Prop
  ConversionTyped : Conversion → (Value → Prop) → (Value → Prop) → Prop
  valid : State → (Value → Prop) → (Occurrence n Key → Prop) → Prop
  start_typed : ∀ code input row, Typed code input row → valid (start code) input row
  safe : ∀ input row, Safe observe (fun state => valid state input row) input row
  conversion_safe : ∀ conversion input output, ConversionTyped conversion input output →
    ∀ value, input value → output (convert conversion value)

def engine (sources : SourceLayer n signature Source Conversion Value SourceState)
    (registry : Registry n signature Value Cursor denote) :
    Engine n signature Source Conversion (Slot visible foldGoal) Value SourceState Cursor where
  startSource := sources.start
  source := sources.observe
  convert := sources.convert
  fold slot := (selected registry slot).driver

def FoldTyped (registry : Registry n signature Value Cursor denote)
    (slot : Slot visible foldGoal) (container item : Value → Prop) (row : Occurrence n Key → Prop) : Prop :=
  container = denote slot.container ∧ item = denote slot.item ∧ row = (selected registry slot).row

def FoldValid (registry : Registry n signature Value Cursor denote)
    (slot : Slot visible foldGoal) (cursor : Cursor) (item : Value → Prop) (row : Occurrence n Key → Prop) : Prop :=
  item = denote slot.item ∧ row = (selected registry slot).row ∧ (selected registry slot).valid cursor

def contracts (sources : SourceLayer n signature Source Conversion Value SourceState)
    (registry : Registry n signature Value Cursor denote) :
    Contracts (engine (visible := visible) (foldGoal := foldGoal) sources registry) where
  SourceTyped := sources.Typed
  ConversionTyped := sources.ConversionTyped
  FoldTyped := FoldTyped registry
  SourceValid := sources.valid
  FoldValid := FoldValid registry
  source_start := sources.start_typed
  source_safe := sources.safe
  conversion_safe := sources.conversion_safe
  fold_start := by
    intro slot container item row typed value valueTyped
    rcases typed with ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, (selected registry slot).start_typed value valueTyped⟩
  fold_safe := by
    intro slot item row
    constructor
    · intro cursor next valid observed
      rcases valid with ⟨rfl, rfl, cursorTyped⟩
      exact ⟨rfl, rfl, (selected registry slot).safe.tick _ _ cursorTyped observed⟩
    · intro cursor value next valid observed
      rcases valid with ⟨rfl, rfl, cursorTyped⟩
      obtain ⟨valueTyped, nextTyped⟩ := (selected registry slot).safe.yield _ _ _ cursorTyped observed
      exact ⟨valueTyped, rfl, rfl, nextTyped⟩
    · intro cursor occurrence payload resume valid observed
      rcases valid with ⟨rfl, rfl, cursorTyped⟩
      obtain ⟨allowed, resumes⟩ := (selected registry slot).safe.request _ _ _ _ cursorTyped observed
      exact ⟨allowed, fun response => ⟨rfl, rfl, resumes response⟩⟩

theorem spread_typing (sources : SourceLayer n signature Source Conversion Value SourceState)
    (registry : Registry n signature Value Cursor denote) (slot : Slot visible foldGoal)
    (sourceTyped : sources.Typed code (denote slot.container) sourceRow) :
    PartTyping (contracts sources registry) (.spread code slot) (denote slot.item)
      (fun occurrence => sourceRow occurrence ∨ (selected registry slot).row occurrence) :=
  .spread sourceTyped ⟨rfl, rfl, rfl⟩

theorem spread_role_constraint (registry : Registry n signature Value Cursor denote)
    (slot : Slot visible foldGoal) (typed : FoldTyped registry slot container item row) :
    Roles.WellFormed visible ∧ RoleConstraints.Resolves visible (foldGoal slot.container slot.item) ∧
      container = denote slot.container ∧ item = denote slot.item ∧ row = (selected registry slot).row := by
  obtain ⟨wellFormed, resolved⟩ := (CheckedRoles.resolve_exact visible _).mp slot.accepted
  exact ⟨wellFormed, resolved, typed⟩

/-- The spread engine uses precisely the accepted declaration plan and its
protocol's declared effects. This is not a claim about lookup performance. -/
theorem engine_uses_selected_dictionary
    (sources : SourceLayer n signature Source Conversion Value SourceState)
    (registry : Registry n signature Value Cursor denote) (slot : Slot visible foldGoal)
    (dictionary : RoleDictionaries.Dictionary visible (foldGoal slot.container slot.item)) :
    (engine sources registry).fold slot = (registry slot.container slot.item dictionary.erase).driver ∧
      (selected registry slot).row = (registry slot.container slot.item dictionary.erase).row := by
  have exactBody := selected_exact registry slot dictionary
  exact ⟨congrArg Body.driver exactBody, congrArg Body.row exactBody⟩

end Yulang.FoldListSpreadRoles
