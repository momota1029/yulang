import Yulang.GeneralNormalizedObservation

/-!
# Root recurrence in checked normalized source observations

K2 concerns the reached root, not every recursive descendant. The independent
judgment below uses source-child paths and equality of every finite normalized
observation. It does not mention the graph cycle detector or an executor.

The Common correspondence is observational: every stored normalized equation
holds in every ordinary model. No equivalence between root recurrence and
nonexistence of a finite Common denotation is claimed. Open normalization and
alias cases defer; complete observation cones are required before rejection.
-/
namespace Yulang.GeneralSourceK2

open GeneralSourceState (State Demand Needed Linked)
open GeneralNormalizedObservation (Snapshot Head)
open CommonRoleRegularGraph (Node Graph StructuralCycleAt successors)
open CommonRoleGraphBisimulation (View RegularAt)

/-- Payload descent through complete normalized heads. Record tails do not
occur here: their fields must first have been collected into one signature. -/
def Child (view : Snapshot state) (source target : Fin state.slots) : Prop :=
  ∃ kind children, view.heads source = .structural kind children ∧
    ∃ index, children index = target

inductive Path (view : Snapshot state) : Fin state.slots → Fin state.slots → Prop
  | nil (slot) : Path view slot slot
  | cons : Child view first middle → Path view middle last → Path view first last

def Cycle (view : Snapshot state) (root : Fin state.slots) : Prop :=
  ∃ child, Child view root child ∧ Path view child root

/-- Signature indices refer to the injective canonical table of this snapshot.
Unknown leaves deliberately do not assert equality between source identities. -/
def read (view : Snapshot state) : Nat → Fin state.slots → View
  | 0, _ => .cut
  | depth + 1, slot =>
      match view.heads slot with
      | .deferred _ => .unresolved
      | .scalar base => .scalar (CommonRoleScalarSourceInspection.code base)
      | .structural kind children => .structural kind.val ((List.ofFn children).map (read view depth))

/-- A root is on a nonempty visible cycle or has the same finite observations
as a root on such a cycle. This does not classify an arbitrary ancestor of it. -/
def RecursAt (view : Snapshot state) (root : Fin state.slots) : Prop :=
  Cycle view root ∨
    ∃ kind children, view.heads root = .structural kind children ∧
      ∃ cyclic, Cycle view cyclic ∧ ∀ depth, read view depth root = read view depth cyclic

theorem child_graph_iff (view : Snapshot state) (source target : Fin state.slots) :
    Child view source target ↔ target ∈ successors view.graph source := by
  constructor
  · rintro ⟨kind, children, observed, index, rfl⟩
    simp only [successors, Snapshot.graph, observed, Head.node]
    exact List.mem_ofFn.mpr ⟨index, rfl⟩
  · intro member
    cases observed : view.heads source with
    | deferred reason => simp [successors, Snapshot.graph, observed, Head.node] at member
    | scalar base => simp [successors, Snapshot.graph, observed, Head.node] at member
    | structural kind children =>
        refine ⟨kind, children, observed, ?_⟩
        simpa [successors, Snapshot.graph, observed, Head.node, List.mem_ofFn] using member

theorem path_graph_iff (view : Snapshot state) (first last : Fin state.slots) :
    Path view first last ↔ FiniteWorklist.Path (successors view.graph) first last := by
  constructor
  · intro path
    induction path with
    | nil => exact .nil _
    | cons edge _ ih => exact .cons ((child_graph_iff ..).mp edge) ih
  · intro path
    induction path with
    | nil => exact .nil _
    | cons edge _ ih => exact .cons ((child_graph_iff ..).mpr edge) ih

theorem cycle_graph_iff (view : Snapshot state) (root : Fin state.slots) :
    Cycle view root ↔ StructuralCycleAt view.graph root := by
  constructor
  · rintro ⟨child, ⟨kind, children, observed, index, rfl⟩, path⟩
    refine ⟨kind.val, List.ofFn children, ?_, children index, List.mem_ofFn.mpr ⟨index, rfl⟩,
      (path_graph_iff ..).mp path⟩
    simp [Snapshot.graph, observed, Head.node]
  · rintro ⟨kind, children, observed, child, member, path⟩
    refine ⟨child, (child_graph_iff ..).mpr ?_, (path_graph_iff ..).mpr path⟩
    simpa [successors, observed] using member

theorem read_graph (view : Snapshot state) (depth : Nat) (slot : Fin state.slots) :
    read view depth slot = CommonRoleGraphBisimulation.observe view.graph depth slot := by
  induction depth generalizing slot with
  | zero => rfl
  | succ depth ih =>
      have equal := funext ih
      cases observed : view.heads slot <;>
        simp [read, CommonRoleGraphBisimulation.observe, Snapshot.graph, observed, Head.node, equal]

theorem graphK2_sound (view : Snapshot state) (root : Fin state.slots)
    (recursive : GeneralSourceBoundary.GraphK2 view.graph root) : RecursAt view root := by
  rcases recursive with cycle | ⟨⟨tag, children, observed⟩, cyclic, cycle, related⟩
  · exact Or.inl ((cycle_graph_iff ..).mpr cycle)
  · cases head : view.heads root with
    | deferred reason => simp [Snapshot.graph, head, Head.node] at observed
    | scalar base => simp [Snapshot.graph, head, Head.node] at observed
    | structural kind args =>
        refine Or.inr ⟨kind, args, head, cyclic, (cycle_graph_iff ..).mpr cycle, ?_⟩
        intro depth
        rw [read_graph, read_graph]
        exact CommonRoleGraphBisimulation.bisimilar_observations view.graph root cyclic
          ((CommonRoleGraphBisimulation.bisimilar_exact ..).mpr related) depth

/-- Completeness here needs a fully determined view; unknown aliases are not
equated just because their finite observation contains the same unknown token. -/
theorem graphK2_exact (view : Snapshot state)
    (closed : ∀ slot, view.graph slot ≠ .unresolved) (root : Fin state.slots) :
    GeneralSourceBoundary.GraphK2 view.graph root ↔ RecursAt view root := by
  refine ⟨graphK2_sound view root, ?_⟩
  rintro (cycle | ⟨kind, children, observed, cyclic, cycle, equal⟩)
  · exact Or.inl ((cycle_graph_iff ..).mp cycle)
  · refine Or.inr ⟨⟨kind.val, List.ofFn children, ?_⟩, cyclic,
      (cycle_graph_iff ..).mp cycle, ?_⟩
    · simp [Snapshot.graph, observed, Head.node]
    · apply CommonRoleGraphBisimulation.observations_bisimilar view.graph closed
      intro depth
      simpa only [← read_graph] using equal depth

/-- Only the cone reachable from this root must be normalized. Unrelated
associated-output slots do not make an otherwise complete cone unknown. -/
def Complete (view : Snapshot state) (root : Fin state.slots) : Prop :=
  ∀ slot, Path view root slot → view.graph slot ≠ .unresolved

def Known (view : Snapshot state) (source : Nat) : Prop :=
  ∃ slot, state.source slot = source ∧ view.graph slot ≠ .unresolved

def RootPending (view : Snapshot state) (demand : Demand roles) (needed : Needed demand) : Prop :=
  ∃ argument, needed argument ∧ ¬ Known view (demand.arguments argument).1

/-- A partial normalizer has not finished inspecting at least one argument's
cone. This is a handoff condition, not the complete candidate-pending field. -/
def RootInspectionUnknown (view : Snapshot state) (demand : Demand roles) : Prop :=
  ∃ argument slot, state.source slot = (demand.arguments argument).1 ∧ ¬ Complete view slot

def RootK2 (view : Snapshot state) (demand : Demand roles) (needed : Needed demand) : Prop :=
  Linked state demand ∧ ¬ RootPending view demand needed ∧ ¬ RootInspectionUnknown view demand ∧
    ∃ argument slot, state.source slot = (demand.arguments argument).1 ∧
      Complete view slot ∧ GeneralSourceBoundary.GraphK2 view.graph slot

theorem pending_graph_iff (view : Snapshot state) (demand : Demand roles)
    (linked : Linked state demand) (needed : Needed demand) :
    RootPending view demand needed ↔ ∃ argument slot, needed argument ∧
      state.source slot = (demand.arguments argument).1 ∧
      GeneralSourceBoundary.GraphUnresolved view.graph slot := by
  constructor
  · rintro ⟨argument, required, unknown⟩
    obtain ⟨pair, _, same⟩ := linked.1 argument
    have lower := congrArg Prod.fst same
    refine ⟨argument, pair.1, required, lower, ?_⟩
    by_cases unresolved : view.graph pair.1 = .unresolved
    · exact unresolved
    · exact False.elim (unknown ⟨pair.1, lower, unresolved⟩)
  · rintro ⟨argument, slot, required, same, unresolved⟩
    refine ⟨argument, required, ?_⟩
    rintro ⟨other, source, observed⟩
    have equal := state.source_injective (source.trans same.symm)
    subst other
    exact observed unresolved

theorem pending_excludes_rootK2 (view : Snapshot state) (demand : Demand roles)
    (needed : Needed demand) (pending : RootPending view demand needed) :
    ¬ RootK2 view demand needed := fun rejected => rejected.2.1 pending

theorem unknown_excludes_rootK2 (view : Snapshot state) (demand : Demand roles)
    (needed : Needed demand) (unknown : RootInspectionUnknown view demand) :
    ¬ RootK2 view demand needed := fun rejected => rejected.2.2.1 unknown

theorem incomplete_defers (view : Snapshot state) (root slot : Fin state.slots)
    (path : Path view root slot) (unknown : view.graph slot = .unresolved) :
    ¬ Complete view root := fun complete => complete slot path unknown

theorem unknown_path_defers_rootK2 (view : Snapshot state) (demand : Demand roles)
    (needed : Needed demand) (argument : Fin (roles demand.role).arity)
    (root slot : Fin state.slots) (source : state.source root = (demand.arguments argument).1)
    (path : Path view root slot) (unknown : view.graph slot = .unresolved) :
    ¬ RootK2 view demand needed :=
  unknown_excludes_rootK2 view demand needed
    ⟨argument, root, source, incomplete_defers view root slot path unknown⟩

/-- Soundness against the independent visible-root recurrence judgment, with
the linked demand, readiness gate, and complete observation cone retained. -/
theorem rootK2_sound (view : Snapshot state) (demand : Demand roles) (needed : Needed demand)
    (rejected : RootK2 view demand needed) :
    Linked state demand ∧ ¬ RootPending view demand needed ∧ ¬ RootInspectionUnknown view demand ∧
      ∃ argument slot, state.source slot = (demand.arguments argument).1 ∧
        Complete view slot ∧ RecursAt view slot := by
  obtain ⟨linked, ready, inspected, argument, slot, source, complete, recursive⟩ := rejected
  exact ⟨linked, ready, inspected, argument, slot, source, complete, graphK2_sound view slot recursive⟩

theorem rootK2_exact (view : Snapshot state) (demand : Demand roles) (needed : Needed demand)
    (linked : Linked state demand) (ready : ¬ RootPending view demand needed)
    (closed : ∀ slot, view.graph slot ≠ .unresolved) :
    RootK2 view demand needed ↔
      ∃ argument slot, state.source slot = (demand.arguments argument).1 ∧ RecursAt view slot := by
  constructor
  · intro rejected
    obtain ⟨_, _, _, argument, slot, source, _, recursive⟩ := rootK2_sound view demand needed rejected
    exact ⟨argument, slot, source, recursive⟩
  · rintro ⟨argument, slot, source, recursive⟩
    refine ⟨linked, ready, ?_, argument, slot, source, fun node _ => closed node,
      (graphK2_exact view closed slot).mpr recursive⟩
    rintro ⟨_, node, _, incomplete⟩
    exact incomplete (fun child _ => closed child)

/-- The rejected lower endpoint has both independent normalized recurrence
and a recorded term equivalent to that endpoint in every original model.
This does not assert that all equivalent Common presentations recur. -/
theorem rootK2_observation_sound (view : Snapshot state) (demand : Demand roles) (needed : Needed demand)
    (rejected : RootK2 view demand needed) :
    ∃ argument slot term, state.source slot = (demand.arguments argument).1 ∧
      (view.heads slot).term = some term ∧ RecursAt view slot ∧
      ∀ model, GeneralSourceState.Models state model →
        Common.Equivalent (model (demand.arguments argument).1).1
          (term.eval Common.model (state.assignment model)) := by
  obtain ⟨_, _, _, argument, slot, source, _, recursive⟩ := rejected
  have recurrence := graphK2_sound view slot recursive
  cases observed : view.heads slot with
  | deferred reason =>
      simp [GeneralSourceBoundary.GraphK2, RegularAt, StructuralCycleAt,
        Snapshot.graph, observed, Head.node] at recursive
  | scalar base =>
      simp [GeneralSourceBoundary.GraphK2, RegularAt, StructuralCycleAt,
        Snapshot.graph, observed, Head.node] at recursive
  | structural kind children =>
      have termRead : (view.heads slot).term = some ((view.shapes kind).term children) := by
        simp [observed, Head.term]
      refine ⟨argument, slot, _, source, termRead, recurrence, ?_⟩
      intro model models
      rw [← source]
      exact GeneralNormalizedObservation.observation_models view model models slot _ termRead

end Yulang.GeneralSourceK2
