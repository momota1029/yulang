import YulangClosure.NativeFreshScopeTransport

/-!
CONSTRUCTED, UNCHECKED research projection for sprint Context coverage r3.
The primary owns all Lean execution and axiom auditing. No root import changes.

`Step` erases the ready bit and payloads from the successful loop boundaries of
candidate_context.rs:1566--1683. Expansion retains the parent until its children
are processed; publication requires each child map lookup to succeed. The
FreshUse map starts empty. Membership is the domain of the map, not its values.
The theorem is about this explicit event projection, not an established Rust
trace interpretation, termination, payload correctness, or whole soundness.

All six Context constructors and identity are represented by `Expr`; arbitrary
sharing and duplicate roots are allowed. Identity is a logical observation and
has no stored ContextExpr row. The borrowed evidence closure excludes its row.
`Attached` covers only contexts actually attached at admission. Stability of
preparation/admission roots is NOT assumed and is NOT proved here. See the
handoff for the restoration-driver seam. The local discharge witness below
refutes stability under arbitrary discharge updates, not an actual reachable
FreshUse restoration route or original source soundness.
-/
namespace YulangClosure.NativeFreshUseContextCoverageR3

inductive Expr where
  | identity
  | prefixLeft (input weight : Nat)
  | suffixRightPops (input weight : Nat)
  | swap (input : Nat)
  | bothFromRight (input certificate : Nat)
  | replay (lower upper : Nat)
  | withoutLeftFilter (input : Nat)
  deriving DecidableEq, Repr

def Expr.children : Expr → List Nat
  | .identity => []
  | .prefixLeft input _ | .suffixRightPops input _ | .swap input
  | .bothFromRight input _ | .withoutLeftFilter input => [input]
  | .replay lower upper => [lower, upper]

def Expr.weight : Expr → Option Nat
  | .prefixLeft _ weight | .suffixRightPops _ weight => some weight
  | _ => none

abbrev Children := Nat → List Nat

/-- Reachability includes identity when a source root/child is identity. -/
inductive Reach (children : Children) (roots : List Nat) : Nat → Prop where
  | root {id} : id ∈ roots → Reach children roots id
  | child {parent id} : Reach children roots parent → id ∈ children parent →
      Reach children roots id

structure Scan where
  pending : List Nat
  keys : List Nat

/-- Ready-bit erasure of successful native traversal. `finish` records the
successful child lookups; it does not assume any transitive coverage. Extra
payload/frontier/weight guards can only remove executions from this relation. -/
inductive Step (children : Children) : Scan → Scan → Prop where
  | skip (id : Nat) (rest keys : List Nat) (seen : id ∈ keys) :
      Step children ⟨id :: rest, keys⟩ ⟨rest, keys⟩
  | expand (id : Nat) (rest keys : List Nat) :
      Step children ⟨id :: rest, keys⟩ ⟨children id ++ id :: rest, keys⟩
  | finish (id : Nat) (rest keys : List Nat)
      (lookups : ∀ child ∈ children id, child ∈ keys) :
      Step children ⟨id :: rest, keys⟩ ⟨rest, id :: keys⟩

inductive Run (children : Children) : Scan → Scan → Prop where
  | refl (state : Scan) : Run children state state
  | tail {first middle last} : Run children first middle →
      Step children middle last → Run children first last

def Marked (state : Scan) (id : Nat) : Prop :=
  id ∈ state.keys ∨ id ∈ state.pending

def Closed (children : Children) (keys : List Nat) : Prop :=
  ∀ parent ∈ keys, ∀ child ∈ children parent, child ∈ keys

theorem step_keeps_marked {children : Children} {before after : Scan}
    (step : Step children before after) {id : Nat}
    (marked : Marked before id) : Marked after id := by
  cases step with
  | skip head rest keys seen =>
      rcases marked with old | pending
      · exact Or.inl old
      · rcases List.mem_cons.mp pending with same | later
        · subst id; exact Or.inl seen
        · exact Or.inr later
  | expand head rest keys =>
      rcases marked with old | pending
      · exact Or.inl old
      · exact Or.inr (List.mem_append.mpr (Or.inr pending))
  | finish head rest keys lookups =>
      rcases marked with old | pending
      · exact Or.inl (List.mem_cons_of_mem head old)
      · rcases List.mem_cons.mp pending with same | later
        · subst id; exact Or.inl (List.mem_cons_self)
        · exact Or.inr later

theorem step_keeps_closed {children : Children} {before after : Scan}
    (step : Step children before after) (closed : Closed children before.keys) :
    Closed children after.keys := by
  cases step with
  | skip => exact closed
  | expand => exact closed
  | finish head rest keys lookups =>
      intro parent member child edge
      rcases List.mem_cons.mp member with same | old
      · subst parent
        exact List.mem_cons_of_mem head (lookups child edge)
      · exact List.mem_cons_of_mem head (closed parent old child edge)

theorem step_keeps_sound {children : Children} {roots : List Nat}
    {before after : Scan} (step : Step children before after)
    (sound : ∀ id, Marked before id → Reach children roots id) :
    ∀ id, Marked after id → Reach children roots id := by
  cases step with
  | skip head rest keys seen =>
      intro id marked
      rcases marked with old | pending
      · exact sound id (Or.inl old)
      · exact sound id (Or.inr (List.mem_cons_of_mem head pending))
  | expand head rest keys =>
      intro id marked
      rcases marked with old | pending
      · exact sound id (Or.inl old)
      · rcases List.mem_append.mp pending with edge | previous
        · exact Reach.child (sound head (Or.inr List.mem_cons_self)) edge
        · exact sound id (Or.inr previous)
  | finish head rest keys lookups =>
      intro id marked
      rcases marked with new | pending
      · rcases List.mem_cons.mp new with same | old
        · subst id; exact sound head (Or.inr List.mem_cons_self)
        · exact sound id (Or.inl old)
      · exact sound id (Or.inr (List.mem_cons_of_mem head pending))

theorem run_keeps_marked {children : Children} {before after : Scan}
    (run : Run children before after) {id : Nat} :
    Marked before id → Marked after id := by
  induction run with
  | refl => exact fun marked => marked
  | tail prior step ih => exact fun marked => step_keeps_marked step (ih marked)

theorem run_keeps_closed {children : Children} {before after : Scan}
    (run : Run children before after) : Closed children before.keys →
    Closed children after.keys := by
  induction run with
  | refl => exact fun closed => closed
  | tail prior step ih => exact fun closed => step_keeps_closed step (ih closed)

theorem run_keeps_sound {children : Children} {roots : List Nat}
    {before after : Scan} (run : Run children before after) :
    (∀ id, Marked before id → Reach children roots id) →
    ∀ id, Marked after id → Reach children roots id := by
  induction run with
  | refl => exact fun sound => sound
  | tail prior step ih => exact fun sound => step_keeps_sound step (ih sound)

/-- Exact domain from a completed successful traversal; no domain/closure
premise is supplied. This proves neither a run's existence nor Rust erasure. -/
theorem completed_exact_domain (children : Children) (roots keys : List Nat)
    (run : Run children ⟨roots, []⟩ ⟨[], keys⟩) :
    ∀ id, id ∈ keys ↔ Reach children roots id := by
  have sound : ∀ id, Marked ⟨roots, []⟩ id → Reach children roots id := by
    intro id marked
    rcases marked with impossible | root
    · cases impossible
    · exact Reach.root root
  have closed : Closed children keys := run_keeps_closed run (by
    intro parent impossible; cases impossible)
  have rootsIn : ∀ id ∈ roots, id ∈ keys := by
    intro id member
    have marked := run_keeps_marked run (Or.inr member)
    rcases marked with found | impossible
    · exact found
    · cases impossible
  intro id
  constructor
  · intro member
    exact run_keeps_sound run sound id (Or.inl member)
  · intro reachable
    induction reachable with
    | root member => exact rootsIn _ member
    | child parent edge ih => exact closed _ ih _ edge

/-- A finite DAG is enforced in native code by child IDs strictly decreasing.
This is a structural predicate, not a claimed Rust global instance. The exact
domain theorem above also applies to any completed successful cyclic input. -/
def FiniteDag (count : Nat) (children : Children) : Prop :=
  children 0 = [] ∧ ∀ parent, parent ≤ count →
    ∀ child ∈ children parent, child < parent

theorem completed_identity_key (children : Children) (roots keys : List Nat)
    (run : Run children ⟨roots, []⟩ ⟨[], keys⟩) (identityRoot : 0 ∈ roots) :
    0 ∈ keys := (completed_exact_domain children roots keys run 0).mpr
      (.root identityRoot)

theorem completed_empty_domain (children : Children) (keys : List Nat)
    (run : Run children ⟨[], []⟩ ⟨[], keys⟩) : ∀ id, id ∉ keys := by
  intro id member
  have reachable := (completed_exact_domain children [] keys run id).mp member
  induction reachable with
  | root impossible => cases impossible
  | child parent edge ih => exact ih

/-- Post-bound evidence seeds both endpoints of a touching transport and then
follows all children. Identity is handled separately, without a stored row. -/
inductive Attached (stored : Nat → Nat) (parents : List Nat)
    (transports : List (Nat × Nat)) : Nat → Prop where
  | parent {relation} : relation ∈ parents → Attached stored parents transports (stored relation)
  | target {parent child} : parent ∈ parents → (parent, child) ∈ transports →
      Attached stored parents transports (stored child)

def LogicalObservation (children : Children) (roots : List Nat) (id : Nat) : Prop :=
  id = 0 ∨ Reach children roots id

/-- A subset of retained_input's context seeds: initial selected relation keys
and each directly touching transport child. Additional fixed-point iterations
can add observations; this formula does not assert that no others are selected. -/
def observationRoots (stored : Nat → Nat) (parents : List Nat)
    (transports : List (Nat × Nat)) : List Nat :=
  parents.map stored ++
    (transports.filter (fun pair => decide (pair.1 ∈ parents))).map
      (fun pair => stored pair.2)

theorem attached_target_observed (children : Children) (stored : Nat → Nat)
    (parents : List Nat) (transports : List (Nat × Nat))
    {parent child : Nat} (selected : parent ∈ parents)
    (transport : (parent, child) ∈ transports) :
    LogicalObservation children (observationRoots stored parents transports)
      (stored child) := by
  apply Or.inr
  apply Reach.root
  apply List.mem_append.mpr
  apply Or.inr
  apply List.mem_map.mpr
  refine ⟨(parent, child), ?_, rfl⟩
  apply List.mem_filter.mpr
  exact ⟨transport, by simpa using selected⟩

/-- Successful lookup equation of post_check_context, independent of payloads. -/
def postCheck (stored : Nat) (discharged : Bool) (residual : Option Nat) : Nat :=
  if discharged then residual.getD 0 else stored

theorem undischarge_reads_stored (stored : Nat) (residual : Option Nat) :
    postCheck stored false residual = stored := rfl

theorem discharge_reads_residual (stored : Nat) (residual : Nat) :
    postCheck stored true (some residual) = residual := rfl

/-- Local state-update counterexample only. Executable reachability of this
update between two FreshUse reads is an additional unproved source obligation. -/
theorem discharge_can_change_root :
    postCheck 2 false none = 2 ∧ postCheck 2 true (some 1) = 1 ∧
      postCheck 2 false none ≠ postCheck 2 true (some 1) := by
  decide

namespace LocalWitness

/-!
Constructor-consistent local configuration, NOT a proved reachable history:
context 1 = PrefixLeft(oldWeight,Identity), context 2 =
PrefixLeft(newWeight,Identity). Native renaming maps 0↦0 and 1↦2.
If the original relation is newly discharged between reads, admission uses
0↦0. Borrowed closure from the old parent key 1 and fresh child key 0 never
selects context 2. A successful restoration causing this update is NOT supplied.
-/
def children (id : Nat) : List Nat := if id = 0 then [] else [0]

def map (id : Nat) : Nat := if id = 1 then 2 else id

theorem completed_source_scan :
    Run children ⟨[1], []⟩ ⟨[], [1, 0]⟩ := by
  refine .tail (.tail (.tail (.refl _) (.expand 1 [] []))
    (.finish 0 [1] [] ?_)) (.finish 1 [] [0] ?_)
  · intro child edge
    simp [children] at edge
  · intro child edge
    simpa [children] using edge

theorem reachable_avoids_two {id : Nat} (reachable : Reach children [1, 0] id) :
    id ≠ 2 := by
  induction reachable with
  | @root id member =>
      intro same
      subst id
      simp at member
  | @child parent child reached edge ih =>
      by_cases zero : parent = 0
      · simp [children, zero] at edge
      · have equal : child = 0 := by simpa [children, zero] using edge
        subst child
        decide

theorem prepared_image_can_escape_changed_root_closure :
    map 1 = 2 ∧ postCheck 1 false none = 1 ∧ postCheck 1 true none = 0 ∧
      ¬ LogicalObservation children [1, 0] (map 1) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro observed
  rcases observed with identity | reachable
  · change 2 = 0 at identity
    cases identity
  · exact reachable_avoids_two reachable rfl

end LocalWitness

end YulangClosure.NativeFreshUseContextCoverageR3
