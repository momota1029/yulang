import YulangClosure.Contracts
import YulangClosure.NativeContextExpansion
import YulangClosure.NativeDrainOwnership
import YulangClosure.NativeContextTables

/-!
Termination obligations for the original inference algorithm, without changing
its transition rules or supported source language.

The Context parser result below supplies a strictly decreasing measure for the
actual `NativeContextExpansion.scanStep` projection.  The existing `scanLoop`
fuel is proved sufficient from this measure; no finite successful transcript,
acyclic-table premise, resource cap, or successful parse is assumed.

The shared drain ownership projection deliberately admits externally requested
allocation events.  Its non-accessibility theorem prevents that conservation
model from being mistaken for a whole inference termination proof.  It is not
a source-qualified counterexample to the Rust inference algorithm.

The original `SourceProblem.InferenceTermination` remains an independent target:
its actual source initial states and all native inference transitions require
one global progress argument across allocation, callbacks, extrusion, intrusion,
Replay and generalization.  These local results do not assume that argument.
-/

namespace YulangClosure.OriginalInferenceTermination

open NativeContextExpansion

/-- Proof-only pending-stack measure.  A node has at most two children and each
successful nontrivial child ID is strictly smaller than its parent ID. -/
def pendingRank : List (Nat × Mode) → Nat
  | [] => 0
  | (id, _) :: rest => 3 ^ id + pendingRank rest

def scanRank (s : Scan) : Nat := pendingRank s.pending

theorem two_children_smaller {left right parent : Nat}
    (hl : left < parent) (hr : right < parent) :
    3 ^ left + 3 ^ right < 3 ^ parent := by
  have lp : left ≤ parent - 1 := by omega
  have rp : right ≤ parent - 1 := by omega
  have a := Nat.pow_le_pow_right (by decide : 0 < 3) lp
  have b := Nat.pow_le_pow_right (by decide : 0 < 3) rp
  have positive := Nat.pow_pos (n := parent - 1) (by decide : 0 < 3)
  have eq : parent = (parent - 1) + 1 := by omega
  rw [eq, Nat.pow_succ]
  omega

/-- Every successful native parser iteration decreases the measure.  Malformed
nodes/weights are rejected before they can create a nondecreasing transition. -/
theorem scanStep_decreases {t : Tables} {s u : Scan}
    (next : scanStep t s = some u) : scanRank u < scanRank s := by
  cases pending : s.pending with
  | nil => simp [scanStep, pending] at next
  | cons pair rest =>
      rcases pair with ⟨id, mode⟩
      simp only [scanStep, pending] at next
      split at next
      · cases next
        simp only [scanRank, pending, pendingRank]
        have := Nat.pow_pos (n := id) (by decide : 0 < 3)
        omega
      · cases node : t.contexts id with
        | none => simp [node] at next
        | some value =>
            simp only [node] at next
            cases value with
            | «prefix» w input =>
                by_cases guard : (mode = .outer ∨ (mode = .replay ∧ input = 0)) ∧
                    input < id ∧ weightValid t w = true
                · simp [guard] at next
                  cases next
                  simp only [scanRank, pending, pendingRank]
                  have := Nat.pow_lt_pow_of_lt (by decide : 1 < 3) guard.2.1
                  omega
                · simp [guard] at next
            | replay lower upper =>
                by_cases guard : lower < id ∧ upper < id
                · simp [guard] at next
                  cases next
                  simp only [scanRank, pending, pendingRank]
                  have := two_children_smaller guard.1 guard.2
                  omega
                · simp [guard] at next
            | swap input | without input =>
                by_cases guard : input < id
                · simp [guard] at next
                  cases next
                  simp only [scanRank, pending, pendingRank]
                  have := Nat.pow_lt_pow_of_lt (by decide : 1 < 3) guard
                  omega
                · simp [guard] at next
            | suffix input w | both input certificate => cases next

/-- Actual local parser transitions are well founded for arbitrary tables,
including malformed tables.  No fuel/transcript premise occurs. -/
theorem scanStep_wellFounded (t : Tables) :
    WellFounded (fun next prev => scanStep t prev = some next) := by
  apply Subrelation.wf (r := fun next prev => scanRank next < scanRank prev)
  · intro next prev step
    exact scanStep_decreases step
  · exact (measure scanRank).wf

theorem scanStep_accessible (t : Tables) (s : Scan) :
    Acc (fun next prev => scanStep t prev = some next) s :=
  (scanStep_wellFounded t).apply s

/-- Local descent is uniform in the observed table.  Table growth between
iterations therefore does not require a fixed final graph for this proof. -/
theorem scanStep_varying_tables_wellFounded :
    WellFounded (fun next prev => ∃ t : Tables, scanStep t prev = some next) := by
  apply Subrelation.wf (r := fun next prev => scanRank next < scanRank prev)
  · intro next prev step
    obtain ⟨t, executed⟩ := step
    exact scanStep_decreases executed
  · exact (measure scanRank).wf

theorem pendingRank_zero_iff (pending : List (Nat × Mode)) :
    pendingRank pending = 0 ↔ pending = [] := by
  cases pending with
  | nil => simp [pendingRank]
  | cons pair rest =>
      rcases pair with ⟨id, mode⟩
      have positive := Nat.pow_pos (n := id) (by decide : 0 < 3)
      simp only [pendingRank, List.cons_ne_nil, iff_false]
      omega

/-- A fuel-free proof-side presentation of the exact native parser loop.
Failure is a genuine malformed-input/unsupported-constructor result; it is not
a timeout.  The only recursive call follows the unchanged `scanStep`. -/
def scanTotal (t : Tables) (s : Scan) : Option Parsed :=
  if s.pending = [] then finish s
  else match _next : scanStep t s with
    | none => none
    | some u => scanTotal t u
termination_by scanRank s
decreasing_by exact scanStep_decreases _next

/-- The original checker stabilizes by a bound derived from its initial stack.
This includes rejection.  There is no assumed successful `ScanRun`. -/
theorem scanLoop_eq_total (t : Tables) (fuel : Nat) (s : Scan)
    (enough : scanRank s ≤ fuel) : scanLoop t fuel s = scanTotal t s := by
  induction fuel generalizing s with
  | zero =>
      have empty : s.pending = [] :=
        (pendingRank_zero_iff s.pending).mp (Nat.eq_zero_of_le_zero enough)
      simp only [scanLoop, scanTotal, empty, ↓reduceIte]
  | succ fuel ih =>
      rw [scanLoop, scanTotal]
      by_cases empty : s.pending = []
      · simp [empty]
      · simp only [empty, ↓reduceIte]
        cases next : scanStep t s with
        | none => rfl
        | some u =>
            have smaller := scanStep_decreases next
            exact ih u (by omega)

theorem scanLoop_stable (t : Tables) (s : Scan) (fuel extra : Nat)
    (enough : scanRank s ≤ fuel) :
    scanLoop t (fuel + extra) s = scanLoop t fuel s := by
  rw [scanLoop_eq_total t _ s (by omega), scanLoop_eq_total t fuel s enough]

/-- A single root gives a closed sufficient bound even with repeated two-child
Replay branching.  It is ghost evidence, never a native allocation/work cap. -/
theorem parse_stable (t : Tables) (root extra : Nat) :
    parse t (3 ^ root + extra) root = parse t (3 ^ root) root := by
  apply scanLoop_stable
  simp [scanRank, pendingRank]

theorem scanTotal_success_iff (t : Tables) (s : Scan) (p : Parsed) :
    scanTotal t s = some p ↔ ScanRun t s p := by
  constructor
  · intro success
    apply scan_computes_run (fuel := scanRank s)
    rw [scanLoop_eq_total t _ s (Nat.le_refl _)]
    exact success
  · intro run
    induction run with
    | @done s p result =>
        have empty : s.pending = [] := by
          unfold finish at result
          split at result
          · rename_i guard
            exact guard.1
          · cases result
        rw [scanTotal, ite_eq_left empty]
        exact result
    | step pending next rest ih =>
        rw [scanTotal, ite_eq_right pending, next]
        exact ih

/-- Finite exact native parser execution, with success and rejection both
represented.  This relation is concluded below, never assumed for totality. -/
inductive ScanExecution (t : Tables) : Scan → Option Parsed → Prop
  | done (s : Scan) (empty : s.pending = []) : ScanExecution t s (finish s)
  | reject (s : Scan) (pending : s.pending ≠ []) (rejected : scanStep t s = none) :
      ScanExecution t s none
  | step {s u result} (pending : s.pending ≠ []) (next : scanStep t s = some u)
      (rest : ScanExecution t u result) : ScanExecution t s result

theorem scanTotal_execution (t : Tables) (s : Scan) :
    ScanExecution t s (scanTotal t s) := by
  induction s using (scanStep_wellFounded t).induction with
  | h s ih =>
      rw [scanTotal]
      by_cases empty : s.pending = []
      · rw [ite_eq_left empty]
        exact .done s empty
      · rw [ite_eq_right empty]
        cases next : scanStep t s with
        | none => exact .reject s empty next
        | some u => exact .step empty next (ih u next)

/-! The topological input law is also constructed from the existing native
interner events.  We reuse the previously proved allocation lemma rather than
assume a DAG for every table.  Commit, cancellation and numeric-ID reuse retain
this property; a post-cancellation fresh node still refers only to old nodes. -/

open NativeContextTables (Store values internCell)
open NativeValuePorts (ContextsFormed contextInputs)

def storeContextsFormed (s : Store) : Prop := ContextsFormed (values s.contexts)

theorem intern_contexts_formed (s : Store) (node : Expr)
    (formed : storeContextsFormed s)
    (inputs : ∀ input ∈ contextInputs node, input ≤ s.contexts.length) :
    storeContextsFormed (s.intern node).1 := by
  change ContextsFormed (values (internCell s.contexts s.clock node).1)
  rw [(NativeContextTables.intern_values s.contexts s.clock node).1]
  exact NativeValuePorts.context_preserves_formation
    (arena := { contexts := values s.contexts }) formed
    (by simpa [values] using inputs)

theorem store_step_contexts_formed {s u : Store} (event : NativeContextTables.Step s u)
    (formed : storeContextsFormed s) : storeContextsFormed u := by
  cases event with
  | context node idle children index reserved success =>
      exact intern_contexts_formed s node formed children
  | reserveView | reserveCopy | sourceWeight | publishView | sampleView | contribution =>
      exact formed

theorem store_run_contexts_formed {s u : Store} (run : NativeContextTables.Run s u)
    (formed : storeContextsFormed s) : storeContextsFormed u := by
  induction run with
  | nil => exact formed
  | snoc prior event ih => exact store_step_contexts_formed event ih

theorem store_history_contexts_formed {s : Store} (history : NativeContextTables.History s) :
    storeContextsFormed s := by
  induction history with
  | initial => simp [storeContextsFormed, ContextsFormed, values]
  | commit prior run idle ih => exact store_run_contexts_formed run ih
  | cancel prior run ih =>
      simpa only [storeContextsFormed, (NativeContextTables.cancellation_vectors run).1] using ih

/-- Successful readback from a constructed native Context store gives the exact
strict child-ID guard, including Replay's two children and all six constructors. -/
theorem constructed_context_children {s : Store} (history : NativeContextTables.History s)
    {id : Nat} {node : Expr} (found : s.tables.contexts id = some node) :
    ∀ child ∈ contextInputs node, child < id := by
  have formed := store_history_contexts_formed history
  unfold Store.tables Store.contextAt at found
  by_cases zero : id = 0
  · simp [zero] at found
  · simp only [zero, ↓reduceIte] at found
    have valueFound : (values s.contexts)[id - 1]? = some node := by
      simpa only [values, List.getElem?_map] using found
    intro child member
    have bound := formed (id - 1) node valueFound child member
    omega

/-- This application is to the actual native table projection and covers every
root, including an invalid root.  It uses no finite-success receipt. -/
theorem native_context_scan_accessible (s : Store) (root : Nat) :
    Acc (fun next prev => scanStep s.tables prev = some next)
      ⟨[(root, .outer)], [], [], root, false, false, false⟩ :=
  scanStep_accessible s.tables _

/-! The other native Context walkers use postorder ready markers (fold/rename)
or direct descent (payload discovery).  Their successful stack actions are
covered by this control projection.  A callback's evaluation semantics and its
Rust refinement are not defined by these actions. -/

def traversalRank : List (Nat × Bool) → Nat
  | [] => 0
  | (id, ready) :: rest => (if ready then 1 else 4 ^ id) + traversalRank rest

theorem traversalRank_append (left right : List (Nat × Bool)) :
    traversalRank (left ++ right) = traversalRank left + traversalRank right := by
  induction left with
  | nil => simp [traversalRank]
  | cons item rest ih => simp only [List.cons_append, traversalRank, ih, Nat.add_assoc]

theorem traversalRank_reverse (pending : List (Nat × Bool)) :
    traversalRank pending.reverse = traversalRank pending := by
  induction pending with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨id, ready⟩
      simp only [List.reverse_cons, traversalRank_append, ih, traversalRank]
      omega

theorem traversalRank_filter_le (pending : List (Nat × Bool)) (keep : Nat × Bool → Bool) :
    traversalRank (pending.filter keep) ≤ traversalRank pending := by
  induction pending with
  | nil => simp [traversalRank]
  | cons pair rest ih =>
      rcases pair with ⟨id, ready⟩
      cases guard : keep (id, ready) <;> simp only [List.filter_cons, guard, Bool.false_eq_true,
        ↓reduceIte, traversalRank]
      · exact Nat.le_trans ih (Nat.le_add_left _ _)
      · exact Nat.add_le_add_left ih _

theorem two_children_with_ready_smaller {left right parent : Nat}
    (hl : left < parent) (hr : right < parent) :
    4 ^ left + 4 ^ right + 1 < 4 ^ parent := by
  have a := Nat.pow_le_pow_right (by decide : 0 < 4) (show left ≤ parent - 1 by omega)
  have b := Nat.pow_le_pow_right (by decide : 0 < 4) (show right ≤ parent - 1 by omega)
  have positive := Nat.pow_pos (n := parent - 1) (by decide : 0 < 4)
  have eq : parent = (parent - 1) + 1 := by omega
  rw [eq, Nat.pow_succ]
  omega

theorem context_children_with_ready_smaller (node : Expr) (parent : Nat)
    (children : ∀ child ∈ contextInputs node, child < parent) :
    traversalRank ((contextInputs node).map (fun id => (id, false))) + 1 < 4 ^ parent := by
  cases node with
  | «prefix» w input | suffix input w | swap input | both input certificate | without input =>
      have small := two_children_with_ready_smaller
        (children input (by simp [contextInputs])) (children input (by simp [contextInputs]))
      have positive := Nat.pow_pos (n := input) (by decide : 0 < 4)
      simp only [contextInputs, List.map_cons, List.map_nil, traversalRank, Bool.false_eq_true,
        ↓reduceIte, Nat.add_zero]
      omega
  | replay lower upper =>
      have small := two_children_with_ready_smaller
        (children lower (by simp [contextInputs])) (children upper (by simp [contextInputs]))
      simpa [contextInputs, traversalRank] using small

/-- Logical next-pop order differs between `extend_from_slice` in payload
discovery and reversed pushes in postorder traversal.  Both orders are kept. -/
def traversalChildren (node : Expr) (backwards : Bool) : List (Nat × Bool) :=
  let children := (contextInputs node).map (fun child => (child, false))
  if backwards then children.reverse else children

theorem traversalChildren_rank (node : Expr) (backwards : Bool) :
    traversalRank (traversalChildren node backwards) =
      traversalRank ((contextInputs node).map fun child => (child, false)) := by
  cases backwards <;> simp [traversalChildren, traversalRank_reverse]

/-- An overapproximation of successful stack actions only.  `pop` covers a
memo hit, Identity, or a completed callback.  Descents retain actual node
children, the native child-ID guard and arbitrary already-completed filtering.
No finiteness or callback-progress premise is built into this relation. -/
inductive ContextTraversalStep (t : Tables) : List (Nat × Bool) → List (Nat × Bool) → Prop
  | pop (item : Nat × Bool) (rest : List (Nat × Bool)) :
      ContextTraversalStep t (item :: rest) rest
  | descend (id : Nat) (node : Expr) (rest : List (Nat × Bool))
      (found : t.contexts id = some node)
      (children : ∀ child ∈ contextInputs node, child < id)
      (keep : Nat × Bool → Bool) (ready backwards : Bool) :
      ContextTraversalStep t ((id, false) :: rest)
        (((traversalChildren node backwards).filter keep) ++
          (if ready then (id, true) :: rest else rest))

theorem contextTraversal_decreases {t : Tables} {before after : List (Nat × Bool)}
    (step : ContextTraversalStep t before after) : traversalRank after < traversalRank before := by
  cases step with
  | pop item rest =>
      rcases item with ⟨id, ready⟩
      have positive := Nat.pow_pos (n := id) (by decide : 0 < 4)
      cases ready <;> simp [traversalRank] <;> omega
  | descend id node rest found children keep ready backwards =>
      have bound := context_children_with_ready_smaller node id children
      have filtered := traversalRank_filter_le (traversalChildren node backwards) keep
      rw [traversalChildren_rank] at filtered
      rw [traversalRank_append]
      cases ready <;> simp only [traversalRank, Bool.false_eq_true,
        ↓reduceIte] <;> omega

theorem contextTraversal_wellFounded (t : Tables) :
    WellFounded (fun next prev => ContextTraversalStep t prev next) := by
  apply Subrelation.wf (r := fun next prev => traversalRank next < traversalRank prev)
  · intro next prev step
    exact contextTraversal_decreases step
  · exact (measure traversalRank).wf

theorem contextTraversal_varying_tables_wellFounded :
    WellFounded (fun next prev => ∃ t : Tables, ContextTraversalStep t prev next) := by
  apply Subrelation.wf (r := fun next prev => traversalRank next < traversalRank prev)
  · intro next prev step
    obtain ⟨t, executed⟩ := step
    exact contextTraversal_decreases executed
  · exact (measure traversalRank).wf

theorem constructed_postorder_descent {s : Store} (history : NativeContextTables.History s)
    {id : Nat} {node : Expr} (found : s.tables.contexts id = some node)
    (rest : List (Nat × Bool)) (keep : Nat × Bool → Bool) (ready backwards : Bool) :
    ContextTraversalStep s.tables ((id, false) :: rest)
      (((traversalChildren node backwards).filter keep) ++
        (if ready then (id, true) :: rest else rest)) :=
  .descend id node rest found (constructed_context_children history found) keep ready backwards

/-- The event conservation projection allows arbitrarily many external reserve
events.  Therefore it cannot itself be the terminating original inference
relation.  This is a theorem about the existing abstraction, not a native/source
divergence witness. -/
theorem drain_projection_not_accessible (s : NativeDrainOwnership.State) :
    ¬ Acc (fun next prev => NativeDrainOwnership.Step prev next) s := by
  intro accessible
  induction accessible with
  | intro state _ ih => exact ih _ (NativeDrainOwnership.Step.reserveOther state)

end YulangClosure.OriginalInferenceTermination
