import Yulang.GeneralSourceBoundary
import Yulang.CommonRoleScalarSourceInspection
import Yulang.RolesAssoc

/-!
# Shared source snapshots and multiargument demands

Source identities index both ordinary computations and inspection nodes. A
recorded constructor is justified in every ordinary model; recording it cannot
discard an ordinary model. Unknown observations retain their source slot.

This is a checked snapshot carrier, not an automatic materializer. The ordinary
syntax is unrestricted. The concrete inspection vocabulary below covers selected Common
constructor views; nominal views and complete source normalization remain open.
Raw graph cycles are observations only: hidden record tails can erase a cycle.
There is deliberately no source-level `RootK2` definition in this module.
In particular, the demand representation represents endpoints by source IDs,
not arbitrary source type expressions. No candidate classification is defined.
-/
namespace Yulang.GeneralSourceState

open Core.PresenceGeneration (Comp TyTerm RowTerm)
open PresenceNormalForm (Atom All)
open CommonRoleRegularGraph (Graph Node)

abbrev Assignment := Nat → Comp Common.model
abbrev Interval := Nat × Nat

def equationAtoms (slot : Fin slots) (term : TyTerm (Fin slots)) : List (Atom (Fin slots)) :=
  [.tyLe (.var slot) term, .tyLe term (.var slot)]

theorem equationAtoms_exact (slot : Fin slots) (term : TyTerm (Fin slots))
    (assignment : Fin slots → Comp Common.model) :
    All Common.model assignment (equationAtoms slot term) ↔
      Common.Equivalent (assignment slot).1 (term.eval Common.model assignment) := by
  simp [equationAtoms, All, Atom.Holds, TyTerm.eval, Common.model, Common.Equivalent]

/-- Constructor signatures retain arrow rows as well as type children. A
signature's finite table index is the inspection tag, so tags cannot collide. -/
inductive Shape (slots : Nat) where
  | pair
  | required (label : Nat)
  | record (label : Nat)
  | variant (tag : Nat)
  | arrow (incoming outgoing : RowTerm (Fin slots))
  | emptyRecord
  | exactEmpty

def Shape.arity : Shape slots → Nat
  | .pair | .record _ | .arrow _ _ => 2
  | .required _ | .variant _ => 1
  | .emptyRecord | .exactEmpty => 0

def Shape.term (shape : Shape slots) (children : Fin shape.arity → Fin slots) :
    TyTerm (Fin slots) :=
  match shape with
  | .pair => .pair (.var (children ⟨0, by simp [Shape.arity]⟩)) (.var (children ⟨1, by simp [Shape.arity]⟩))
  | .required label => .required label (.var (children ⟨0, by simp [Shape.arity]⟩))
  | .record label => .record label (.var (children ⟨0, by simp [Shape.arity]⟩)) (.var (children ⟨1, by simp [Shape.arity]⟩))
  | .variant tag => .variant tag (.var (children ⟨0, by simp [Shape.arity]⟩))
  | .arrow incoming outgoing =>
      .arrow (.var (children ⟨0, by simp [Shape.arity]⟩)) incoming (.var (children ⟨1, by simp [Shape.arity]⟩)) outgoing
  | .emptyRecord => .emptyRecord
  | .exactEmpty => .exactEmpty

/-- No arbitrary graph tags or untyped child lists enter a snapshot. -/
inductive Head (shapes : Fin kinds → Shape slots) where
  | unresolved
  | scalar (base : Inference.Base)
  | structural (kind : Fin kinds) (children : Fin (shapes kind).arity → Fin slots)

def Head.node {shapes : Fin kinds → Shape slots} : Head shapes → Node slots
  | .unresolved => .unresolved
  | .scalar base => .scalar (CommonRoleScalarSourceInspection.code base)
  | .structural kind children => .structural kind.val (List.ofFn children)

def Head.equation {shapes : Fin kinds → Shape slots} : Head shapes → Option (TyTerm (Fin slots))
  | .unresolved => none
  | .scalar base => some (.base base)
  | .structural kind children => some ((shapes kind).term children)

/-- Independent meaning of each recorded head at its original ordinary slot.
No equation is asserted for an observation that has not yet been made. -/
def HeadModels (shapes : Fin kinds → Shape slots) (heads : Fin slots → Head shapes)
    (assignment : Fin slots → Comp Common.model) : Prop :=
  ∀ slot term, (heads slot).equation = some term →
    Common.Equivalent (assignment slot).1 (term.eval Common.model assignment)

structure State where
  slots : Nat
  source : Fin slots → Nat
  source_injective : Function.Injective source
  /-- Row identities are independent of the type-node identities. -/
  rowSource : Fin slots → Nat
  ordinary : List (Atom (Fin slots))
  kinds : Nat
  shapes : Fin kinds → Shape slots
  shapes_injective : Function.Injective shapes
  heads : Fin slots → Head shapes
  /-- Both endpoints are existing nodes. There is no central type slot. -/
  intervals : List (Fin slots × Fin slots)
  /-- Observations follow from the ordinary constraints, never the reverse. -/
  heads_sound : ∀ assignment, All Common.model assignment ordinary →
    HeadModels shapes heads assignment
  intervals_sound : ∀ assignment, All Common.model assignment ordinary →
    ∀ pair ∈ intervals, Common.Subtype (assignment pair.1).1 (assignment pair.2).1

def State.graph (state : State) : Graph state.slots := fun slot => (state.heads slot).node
def State.assignment (state : State) (model : Assignment) : Fin state.slots → Comp Common.model :=
  fun slot => ((model (state.source slot)).1, (model (state.rowSource slot)).2)

def State.OrdinaryModels (state : State) (model : Assignment) : Prop :=
  GeneralSourceBoundary.Models state.ordinary (state.assignment model)

def State.GraphModels (state : State) (model : Assignment) : Prop :=
  HeadModels state.shapes state.heads (state.assignment model)

/-- Full snapshot meaning includes the inspection equations and intervals, but
the checked invariants prove that it does not narrow the ordinary model set. -/
def Models (state : State) (model : Assignment) : Prop :=
  state.OrdinaryModels model ∧ state.GraphModels model ∧
    ∀ pair ∈ state.intervals,
      Common.Subtype (model (state.source pair.1)).1 (model (state.source pair.2)).1

theorem models_ordinary (state : State) (model : Assignment) :
    Models state model ↔ state.OrdinaryModels model := by
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, state.heads_sound _ h, state.intervals_sound _ h⟩

theorem models_compiled (state : State) (model : Assignment) :
    Models state model ↔
      ∃ values : Fin (CommonPresenceConstraintGraph.compile state.ordinary).size → Common.Ty,
        (CommonPresenceConstraintGraph.compile state.ordinary).Models
          (fun slot => (state.assignment model slot).2) values ∧
        (CommonPresenceConstraintGraph.compile state.ordinary).readback
          (fun slot => (state.assignment model slot).2) values = state.assignment model :=
  (models_ordinary state model).trans
    (CommonPresenceConstraintGraph.compile_atoms_exact state.ordinary (state.assignment model))

theorem recorded_head_sound (state : State) (model : Assignment) (models : Models state model)
    (slot : Fin state.slots) (term : TyTerm (Fin state.slots))
    (recorded : (state.heads slot).equation = some term) :
    Common.Equivalent (model (state.source slot)).1
      (term.eval Common.model (state.assignment model)) :=
  models.2.1 slot term recorded

theorem shared_source_node (state : State) (left right : Fin state.slots)
    (same : state.source left = state.source right) :
    left = right ∧ state.graph left = state.graph right := by
  have equal := state.source_injective same
  exact ⟨equal, congrArg state.graph equal⟩

/-- A named associated output is an ordinary source variable. Its equality to
an implementation's RHS is not imposed before candidate selection. -/
structure Output where
  name : Nat
  target : Nat

/-- Arity and output names use the existing role declarations. Repeated output
obligations are retained; no uniqueness or default-selection policy is added. -/
structure Demand (roles : Roles.RoleDecls) where
  role : Nat
  arguments : Fin (roles role).arity → Interval
  outputs : List Output
  declared : ∀ output ∈ outputs, ∃ body, (roles role).assoc output.name = some body

def Linked (state : State) (demand : Demand roles) : Prop :=
  (∀ argument, ∃ pair ∈ state.intervals,
    (state.source pair.1, state.source pair.2) = demand.arguments argument) ∧
  ∀ output ∈ demand.outputs, ∃ slot, state.source slot = output.target

/-- Supplied by the future applicability layer. It is fixed across the
refinement theorems and does not inspect a returned candidate or dictionary. -/
abbrev Needed (demand : Demand roles) := Fin (roles demand.role).arity → Prop

def Known (state : State) (source : Nat) : Prop :=
  ∃ slot, state.source slot = source ∧ state.graph slot ≠ .unresolved

def RootPending (state : State) (demand : Demand roles) (needed : Needed demand) : Prop :=
  ∃ argument, needed argument ∧ ¬ Known state (demand.arguments argument).1

/-- Raw cycle evidence is retained even while another argument is pending. -/
def RootCycleObserved (state : State) (demand : Demand roles) : Prop :=
  ∃ argument slot, state.source slot = (demand.arguments argument).1 ∧
    GeneralSourceBoundary.GraphK2 state.graph slot

/-- Addendum 3 delays the whole demand. This is a gated graph observation,
not source K2: canonical source inspection is a separate missing prerequisite. -/
def ObservedRootK2 (state : State) (demand : Demand roles) (needed : Needed demand) : Prop :=
  ¬ RootPending state demand needed ∧ RootCycleObserved state demand

theorem pending_graph_iff (state : State) (demand : Demand roles) (linked : Linked state demand)
    (needed : Needed demand) :
    RootPending state demand needed ↔
      ∃ argument slot, needed argument ∧ state.source slot = (demand.arguments argument).1 ∧
        GeneralSourceBoundary.GraphUnresolved state.graph slot := by
  constructor
  · rintro ⟨argument, required, unknown⟩
    obtain ⟨pair, _, same⟩ := linked.1 argument
    have source := congrArg Prod.fst same
    refine ⟨argument, pair.1, required, source, ?_⟩
    by_cases resolved : state.graph pair.1 = .unresolved
    · exact resolved
    · exact False.elim (unknown ⟨pair.1, source, resolved⟩)
  · rintro ⟨argument, slot, required, source, unresolved⟩
    refine ⟨argument, required, ?_⟩
    rintro ⟨other, same, known⟩
    have equal := state.source_injective (same.trans source.symm)
    subst other
    exact known unresolved

theorem pending_excludes_observedK2 (state : State) (demand : Demand roles) (needed : Needed demand)
    (pending : RootPending state demand needed) : ¬ ObservedRootK2 state demand needed :=
  fun rejected => rejected.1 pending

theorem observedK2_graph_iff (state : State) (demand : Demand roles) (needed : Needed demand) :
    ObservedRootK2 state demand needed ↔
      ¬ RootPending state demand needed ∧
        ∃ argument slot, state.source slot = (demand.arguments argument).1 ∧
          GeneralSourceBoundary.GraphK2 state.graph slot := Iff.rfl

/-- A contract for future updates, not a definition of the language step.
Fresh nodes are allowed; old ordinary atoms and known observations are retained
under an explicit source-preserving embedding. Constructor equality is not
required: narrowing may legitimately refine an already known head. -/
structure Refines (before after : State) where
  embed : Fin before.slots → Fin after.slots
  source : ∀ slot, after.source (embed slot) = before.source slot
  rowSource : ∀ slot, after.rowSource (embed slot) = before.rowSource slot
  ordinary : ∀ atom ∈ before.ordinary, atom.rename embed ∈ after.ordinary
  known : ∀ slot, before.graph slot ≠ .unresolved → after.graph (embed slot) ≠ .unresolved
  intervals : ∀ pair ∈ before.intervals, (embed pair.1, embed pair.2) ∈ after.intervals

theorem refinement_models (refinement : Refines before after) (model : Assignment)
    (models : Models after model) : Models before model := by
  apply (models_ordinary before model).mpr
  intro atom member
  have h := models.1 (atom.rename refinement.embed) (refinement.ordinary atom member)
  have transported := (Atom.holds_rename Common.model (after.assignment model)
    refinement.embed atom).mp h
  have same : after.assignment model ∘ refinement.embed = before.assignment model := by
    funext slot
    simp only [Function.comp_def, State.assignment, refinement.source, refinement.rowSource]
  rw [same] at transported
  exact transported

theorem refinement_linked (refinement : Refines before after) (demand : Demand roles)
    (linked : Linked before demand) : Linked after demand := by
  constructor
  · intro argument
    obtain ⟨pair, member, same⟩ := linked.1 argument
    exact ⟨(refinement.embed pair.1, refinement.embed pair.2),
      refinement.intervals pair member, by simpa only [refinement.source] using same⟩
  · intro output member
    obtain ⟨slot, same⟩ := linked.2 output member
    exact ⟨refinement.embed slot, (refinement.source slot).trans same⟩

theorem refinement_known (refinement : Refines before after) (source : Nat)
    (known : Known before source) : Known after source := by
  obtain ⟨slot, same, observed⟩ := known
  exact ⟨refinement.embed slot, (refinement.source slot).trans same,
    refinement.known slot observed⟩

/-- Pending can disappear under this update contract; it cannot appear anew. -/
theorem refinement_pending (refinement : Refines before after) (demand : Demand roles)
    (needed : Needed demand) (pending : RootPending after demand needed) :
    RootPending before demand needed := by
  obtain ⟨argument, required, unknown⟩ := pending
  exact ⟨argument, required, fun known => unknown (refinement_known refinement _ known)⟩

/-- Only the empty-candidate reason is represented here; applicability belongs
to item 3. The readiness gate follows addendum 1. -/
def ResolvedEmpty (state : State) (demand : Demand roles) (needed : Needed demand)
    (survivor : Nat → Prop) : Prop :=
  ¬ RootPending state demand needed ∧ ∀ key, ¬ survivor key

/-- The two readiness-gated observations cannot be read back at this pending
snapshot. A newly ready snapshot may legitimately expose a cycle. This does
not identify an unnormalized graph cycle with a source rejection reason. -/
theorem pending_defers_decisions (state : State) (demand : Demand roles) (needed : Needed demand)
    (pending : RootPending state demand needed) (survivor : Nat → Prop) :
    ¬ ObservedRootK2 state demand needed ∧ ¬ ResolvedEmpty state demand needed survivor :=
  ⟨pending_excludes_observedK2 state demand needed pending, fun empty => empty.1 pending⟩

end Yulang.GeneralSourceState
