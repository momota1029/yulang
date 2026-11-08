import Yulang.CommonRoleGraphBisimulation
import Yulang.CommonRoleSharedPayloadCapture

/-!
# Structural head inspection over finite type graphs

This is a lower-head inspection component, not a candidate resolver. The
graph node being inspected is the actual lower bound. A variable or a list
of merged plain variables captures the whole node without inspecting it.
Other patterns report a cyclic anonymous node before attempting to unfold
it, including a finite unrolling bisimilar to a cyclic node. `cycle` records
an encounter, not a final source rejection: another
ordinary constraint might still eliminate the candidate. The caller must
propagate constraints and establish applicability before classification.

The finite capture table retains graph identities, including repeated names.
An unresolved descendant can later close a cycle, so even a `matched` result
must be revalidated after graph updates. Sibling observations are left-biased
and do not establish order-independent candidate applicability. Upper bounds,
ordinary constraints, and where-child construction remain separate
obligations.
-/
namespace Yulang.CommonRoleGraphInspection

open CommonRoleRegularGraph
open CommonRoleGraphBisimulation

inductive Pattern where
  | variable (name : Nat)
  | shared (names : List Nat)
  | scalar (name : Nat)
  | structural (constructor : Nat) (children : List Pattern)
  | nominal (name : Nat) (arguments : List Pattern)
  deriving Repr

abbrev Captures (n : Nat) := List (Nat × Fin n)

inductive Observation (n : Nat) where
  | matched (captures : Captures n)
  | mismatch
  | unresolved
  | cycle (node : Fin n)
  deriving DecidableEq, Repr

def combine (first last : Observation n) : Observation n :=
  match first, last with
  | .matched before, .matched after => .matched (before ++ after)
  | .matched _, other => other
  | other, _ => other

mutual
  def inspect (graph : Graph n) (pattern : Pattern) (node : Fin n) : Observation n :=
    match pattern with
    | .variable name => .matched [(name, node)]
    | .shared names => .matched (names.map fun name => (name, node))
    | .scalar expected =>
        if regularAt graph node then .cycle node else
          match graph node with
          | .unresolved => .unresolved
          | .scalar actual => if expected = actual then .matched [] else .mismatch
          | _ => .mismatch
    | .structural expected patterns =>
        if regularAt graph node then .cycle node else
          match graph node with
          | .unresolved => .unresolved
          | .structural actual children =>
              if expected = actual then inspectChildren graph patterns children else .mismatch
          | _ => .mismatch
    | .nominal expected patterns =>
        if regularAt graph node then .cycle node else
          match graph node with
          | .unresolved => .unresolved
          | .nominal actual arguments =>
              if expected = actual then inspectChildren graph patterns arguments else .mismatch
          | _ => .mismatch
  termination_by sizeOf pattern

  def inspectChildren (graph : Graph n) : List Pattern → List (Fin n) → Observation n
    | [], [] => .matched []
    | pattern :: patterns, node :: nodes =>
        combine (inspect graph pattern node) (inspectChildren graph patterns nodes)
    | _, _ => .mismatch
  termination_by patterns _ => sizeOf patterns
end

/-- A source head together with its role and declaration identity. Where
clauses are not yet represented by this inspection component. -/
structure VisibleHead where
  role : Nat
  key : Nat
  pattern : Pattern
  deriving Repr

/-- Inspect every visible head for the requested role, retaining duplicates
and source order. This is a snapshot of lower-head observations, not a
classification into source-level resolution outcomes. -/
def inspectVisible (graph : Graph n) (role : Nat) (node : Fin n)
    (visible : List VisibleHead) : List (Nat × Observation n) :=
  visible.filterMap fun declaration =>
    if declaration.role = role then some (declaration.key, inspect graph declaration.pattern node) else none

theorem inspect_visible_exact (graph : Graph n) (role : Nat) (node : Fin n)
    (visible : List VisibleHead) (key : Nat) (observation : Observation n) :
    (key, observation) ∈ inspectVisible graph role node visible ↔
      ∃ declaration ∈ visible, declaration.role = role ∧ declaration.key = key ∧
        inspect graph declaration.pattern node = observation := by
  simp only [inspectVisible, List.mem_filterMap]
  constructor
  · rintro ⟨declaration, member, selected⟩
    split at selected
    · rename_i sameRole
      have equal := Option.some.inj selected
      exact ⟨declaration, member, sameRole, (Prod.mk.inj equal).1, (Prod.mk.inj equal).2⟩
    · cases selected
  · rintro ⟨declaration, member, sameRole, sameKey, sameObservation⟩
    refine ⟨declaration, member, ?_⟩
    simp [sameRole, sameKey, sameObservation]

theorem inspect_visible_append (graph : Graph n) (role : Nat) (node : Fin n)
    (first last : List VisibleHead) :
    inspectVisible graph role node (first ++ last) =
      inspectVisible graph role node first ++ inspectVisible graph role node last := by
  simp [inspectVisible, List.filterMap_append]

/- The earlier single `Observation` is intentionally left-biased. This
alternative retains every child observation so that the later propagation
pass can determine applicability before assigning K2 priority. -/
mutual
  def inspectAll (graph : Graph n) (pattern : Pattern) (node : Fin n) : List (Observation n) :=
    match pattern with
    | .variable name => [.matched [(name, node)]]
    | .shared names => [.matched (names.map fun name => (name, node))]
    | .scalar expected =>
        if regularAt graph node then [.cycle node] else
          match graph node with
          | .unresolved => [.unresolved]
          | .scalar actual => if expected = actual then [.matched []] else [.mismatch]
          | _ => [.mismatch]
    | .structural expected patterns =>
        if regularAt graph node then [.cycle node] else
          match graph node with
          | .unresolved => [.unresolved]
          | .structural actual children =>
              if expected = actual then inspectAllChildren graph patterns children else [.mismatch]
          | _ => [.mismatch]
    | .nominal expected patterns =>
        if regularAt graph node then [.cycle node] else
          match graph node with
          | .unresolved => [.unresolved]
          | .nominal actual arguments =>
              if expected = actual then inspectAllChildren graph patterns arguments else [.mismatch]
          | _ => [.mismatch]
  termination_by sizeOf pattern

  def inspectAllChildren (graph : Graph n) : List Pattern → List (Fin n) → List (Observation n)
    | [], [] => []
    | pattern :: patterns, node :: nodes =>
        inspectAll graph pattern node ++ inspectAllChildren graph patterns nodes
    | _, _ => [.mismatch]
  termination_by patterns _ => sizeOf patterns
end

theorem inspect_all_children_cons (graph : Graph n) (pattern : Pattern) (patterns : List Pattern)
    (node : Fin n) (nodes : List (Fin n)) :
    inspectAllChildren graph (pattern :: patterns) (node :: nodes) =
      inspectAll graph pattern node ++ inspectAllChildren graph patterns nodes := by
  simp [inspectAllChildren]

/-- Every visible head is inspected independently; its entire observation
list is preserved, including later siblings after an earlier mismatch. -/
def inspectAllVisible (graph : Graph n) (role : Nat) (node : Fin n)
    (visible : List VisibleHead) : List (Nat × List (Observation n)) :=
  visible.filterMap fun declaration =>
    if declaration.role = role then some (declaration.key, inspectAll graph declaration.pattern node) else none

theorem inspect_all_visible_exact (graph : Graph n) (role : Nat) (node : Fin n)
    (visible : List VisibleHead) (key : Nat) (observations : List (Observation n)) :
    (key, observations) ∈ inspectAllVisible graph role node visible ↔
      ∃ declaration ∈ visible, declaration.role = role ∧ declaration.key = key ∧
        inspectAll graph declaration.pattern node = observations := by
  simp only [inspectAllVisible, List.mem_filterMap]
  constructor
  · rintro ⟨declaration, member, selected⟩
    split at selected
    · rename_i sameRole
      have equal := Option.some.inj selected
      exact ⟨declaration, member, sameRole, (Prod.mk.inj equal).1, (Prod.mk.inj equal).2⟩
    · cases selected
  · rintro ⟨declaration, member, sameRole, sameKey, sameObservations⟩
    exact ⟨declaration, member, by simp [sameRole, sameKey, sameObservations]⟩

mutual
  /-- Every retained cycle observation is backed by the graph regularity
  judgment, independently of observations at other positions. -/
  theorem inspect_all_cycle_sound (graph : Graph n) (pattern : Pattern) (node reached : Fin n)
      (observed : .cycle reached ∈ inspectAll graph pattern node) : RegularAt graph reached := by
    cases pattern with
    | «variable» name => simp [inspectAll] at observed
    | shared names => simp [inspectAll] at observed
    | scalar expected =>
        simp only [inspectAll] at observed
        split at observed
        · rename_i cyclic
          simp only [List.mem_singleton, Observation.cycle.injEq] at observed
          subst reached
          exact (regular_at_exact graph node).mp cyclic
        · cases current : graph node <;> simp_all
          split at observed <;> simp_all
    | structural expected patterns =>
        simp only [inspectAll] at observed
        split at observed
        · rename_i cyclic
          simp only [List.mem_singleton, Observation.cycle.injEq] at observed
          subst reached
          exact (regular_at_exact graph node).mp cyclic
        · cases current : graph node <;> simp only [current] at observed
          case unresolved => simp at observed
          case scalar => simp at observed
          case nominal => simp at observed
          case structural actual children =>
            split at observed
            · exact inspect_all_children_cycle_sound graph patterns children reached observed
            · simp at observed
    | nominal expected patterns =>
        simp only [inspectAll] at observed
        split at observed
        · rename_i cyclic
          simp only [List.mem_singleton, Observation.cycle.injEq] at observed
          subst reached
          exact (regular_at_exact graph node).mp cyclic
        · cases current : graph node <;> simp only [current] at observed
          case unresolved => simp at observed
          case scalar => simp at observed
          case structural => simp at observed
          case nominal actual children =>
            split at observed
            · exact inspect_all_children_cycle_sound graph patterns children reached observed
            · simp at observed
  termination_by sizeOf pattern

  theorem inspect_all_children_cycle_sound (graph : Graph n) (patterns : List Pattern)
      (nodes : List (Fin n)) (reached : Fin n)
      (observed : .cycle reached ∈ inspectAllChildren graph patterns nodes) : RegularAt graph reached := by
    cases patterns with
    | nil => cases nodes <;> simp [inspectAllChildren] at observed
    | cons pattern patterns =>
        cases nodes with
        | nil => simp [inspectAllChildren] at observed
        | cons node nodes =>
            rw [inspect_all_children_cons, List.mem_append] at observed
            rcases observed with first | last
            · exact inspect_all_cycle_sound graph pattern node reached first
            · exact inspect_all_children_cycle_sound graph patterns nodes reached last
  termination_by sizeOf patterns
end

theorem variable_opaque (graph : Graph n) (name : Nat) (node : Fin n) :
    inspect graph (.variable name) node = .matched [(name, node)] := by simp [inspect]

theorem shared_opaque (graph : Graph n) (names : List Nat) (node : Fin n) :
    inspect graph (.shared names) node = .matched (names.map fun name => (name, node)) := by simp [inspect]

/-- Every shared variable receives the exact same original graph node. -/
theorem shared_capture (names : List Nat) (node : Fin n) (name : Nat)
    (member : name ∈ names) : (name, node) ∈
      (names.map fun name => (name, node)) := List.mem_map.mpr ⟨name, member, rfl⟩

/-- The raw table agrees with the established whole-payload lookup rule. -/
theorem shared_lookup (names : List Nat) (node : Fin n) (name : Nat) :
    CommonRoleCanonicalRows.lookup name (names.map fun captured => (captured, node)) =
      if name ∈ names then some node else none :=
  CommonRoleSharedPayloadCapture.lookup_repeated_payload names node name

/-- A one-snapshot observation. `heads` is not selection, and `unknown` is
not yet the whole resolver's pending state. Ordinary constraint propagation,
where obligations, and graph-update revalidation are still required. -/
inductive Snapshot (n : Nat) where
  | unknown
  | cycle (node : Fin n)
  | heads (observations : List (Nat × List (Observation n)))
  deriving DecidableEq, Repr

def inspectSnapshot (graph : Graph n) (role : Nat) (node : Fin n)
    (visible : List VisibleHead) : Snapshot n :=
  match graph node with
  | .unresolved => .unknown
  | _ => if regularAt graph node then .cycle node
      else .heads (inspectAllVisible graph role node visible)

theorem snapshot_unknown_exact (graph : Graph n) (role : Nat) (node : Fin n)
    (visible : List VisibleHead) :
    inspectSnapshot graph role node visible = .unknown ↔ graph node = .unresolved := by
  cases found : graph node <;> simp [inspectSnapshot, found]
  all_goals split <;> simp_all

theorem snapshot_cycle_sound (graph : Graph n) (role : Nat) (node reached : Fin n)
    (visible : List VisibleHead) (observed : inspectSnapshot graph role node visible = .cycle reached) :
    reached = node ∧ RegularAt graph node := by
  cases found : graph node <;> simp only [inspectSnapshot, found] at observed
  case unresolved => cases observed
  all_goals split at observed
  all_goals try cases observed
  all_goals rename_i regular
  all_goals exact ⟨rfl, (regular_at_exact graph node).mp regular⟩

theorem cyclic_structural_encounter (graph : Graph n) (node : Fin n)
    (constructor : Nat) (children : List Pattern)
    (cyclic : RegularAt graph node) :
    inspect graph (.structural constructor children) node = .cycle node := by
  simp [inspect, (regular_at_exact graph node).mpr cyclic]

theorem unresolved_structural (graph : Graph n) (node : Fin n)
    (constructor : Nat) (children : List Pattern) (unresolved : graph node = .unresolved) :
    inspect graph (.structural constructor children) node = .unresolved := by
  simp [inspect, regularAt, unresolved]

mutual
  /-- Every cycle reported by the actual inspector is a real anonymous
  structural cycle in the finite input graph. -/
  theorem inspect_cycle_sound (graph : Graph n) (pattern : Pattern) (node reached : Fin n)
      (observed : inspect graph pattern node = .cycle reached) : RegularAt graph reached := by
    cases pattern with
    | «variable» name => simp [inspect] at observed
    | shared names => simp [inspect] at observed
    | scalar expected =>
        simp only [inspect] at observed
        split at observed
        · rename_i cyclic
          cases observed
          exact (regular_at_exact graph node).mp cyclic
        · cases current : graph node <;> simp_all
          split at observed <;> cases observed
    | structural expected patterns =>
        simp only [inspect] at observed
        split at observed
        · rename_i cyclic
          cases observed
          exact (regular_at_exact graph node).mp cyclic
        · cases current : graph node <;> simp only [current] at observed
          case unresolved => cases observed
          case scalar => cases observed
          case nominal => cases observed
          case structural actual children =>
            split at observed
            · exact inspect_children_cycle_sound graph patterns children reached observed
            · cases observed
    | nominal expected patterns =>
        simp only [inspect] at observed
        split at observed
        · rename_i cyclic
          cases observed
          exact (regular_at_exact graph node).mp cyclic
        · cases current : graph node <;> simp only [current] at observed
          case unresolved => cases observed
          case scalar => cases observed
          case structural => cases observed
          case nominal actual children =>
            split at observed
            · exact inspect_children_cycle_sound graph patterns children reached observed
            · cases observed
  termination_by sizeOf pattern

  theorem inspect_children_cycle_sound (graph : Graph n) (patterns : List Pattern)
      (nodes : List (Fin n)) (reached : Fin n)
      (observed : inspectChildren graph patterns nodes = .cycle reached) : RegularAt graph reached := by
    cases patterns with
    | nil => cases nodes <;> simp [inspectChildren] at observed
    | cons pattern patterns =>
        cases nodes with
        | nil => simp [inspectChildren] at observed
        | cons node nodes =>
            simp only [inspectChildren] at observed
            cases first : inspect graph pattern node with
            | mismatch => simp [combine, first] at observed
            | unresolved => simp [combine, first] at observed
            | cycle found =>
                simp only [combine, first, Observation.cycle.injEq] at observed
                subst reached
                exact inspect_cycle_sound graph pattern node found first
            | matched captures =>
                cases last : inspectChildren graph patterns nodes with
                | mismatch => simp [combine, first, last] at observed
                | unresolved => simp [combine, first, last] at observed
                | matched rest => simp [combine, first, last] at observed
                | cycle found =>
                    simp only [combine, first, last, Observation.cycle.injEq] at observed
                    subst reached
                    exact inspect_children_cycle_sound graph patterns nodes found last
  termination_by sizeOf patterns
end

end Yulang.CommonRoleGraphInspection
