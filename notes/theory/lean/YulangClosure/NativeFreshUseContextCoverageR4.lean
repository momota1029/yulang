import YulangClosure.NativeFreshUseContextCoverageR3

/-!
CONSTRUCTED, UNCHECKED r4 research. No Lean/Lake invocation or axiom audit
has been performed. The primary owns verification after independent review.

The control states below retain the native outer root loop, stack ready bits,
verified set, and map domain separately. `NativeStep` is the successful-control
projection of candidate_context.rs:1566--1672, including the omitted-verified-
child optimization. It excludes fallible payload/allocation guards; successful
Rust execution has to be related to these states by a separate interpretation.
The theorems establish the control-projection invariants and exact domain,
without assuming domain equality or transitive coverage. They do not provide
that Rust interpretation, native termination, rollback, payload/map-value
correctness, restoration noninterference, or whole-source inference soundness.

Identity is a logical observation and is NEVER a stored ContextExpr row.
The final section gives a closure calculus for immutable stored constructors:
discharging a relation changes its effective root, not its stored constructor.
This proves preservation for an already attached target. Attaching every
prepared map image across later restoration remains OPEN.
-/
namespace YulangClosure.NativeFreshUseContextCoverageR4

open NativeFreshUseContextCoverageR3

structure NativeScan where
  roots : List Nat
  pending : List (Nat × Bool)
  verified : List Nat
  keys : List Nat

def active (state : NativeScan) : List Nat :=
  state.pending.map Prod.fst ++ state.roots

def marked (state : NativeScan) (id : Nat) : Prop :=
  id ∈ state.keys ∨ id ∈ active state

/-- Native reverse-push/forward-pop order, with already verified children
omitted exactly as in the source. List membership represents finite set
membership; hash iteration order is not part of the claim. -/
def scheduled (children verified : List Nat) : List (Nat × Bool) :=
  (children.filter (fun id => !(decide (id ∈ verified)))).map
    (fun id => (id, false))

theorem scheduled_member (children verified : List Nat) (id : Nat) :
    id ∈ (scheduled children verified).map Prod.fst ↔
      id ∈ children ∧ id ∉ verified := by
  simp [scheduled, List.map_map]

inductive NativeStep (children : Children) : NativeScan → NativeScan → Prop where
  | root (id : Nat) (roots verified keys : List Nat) :
      NativeStep children ⟨id :: roots, [], verified, keys⟩
        ⟨roots, [(id, false)], verified, keys⟩
  | skip (id : Nat) (ready : Bool) (roots : List Nat)
      (rest : List (Nat × Bool)) (verified keys : List Nat)
      (seen : id ∈ verified) :
      NativeStep children ⟨roots, (id, ready) :: rest, verified, keys⟩
        ⟨roots, rest, verified, keys⟩
  | expand (id : Nat) (roots : List Nat) (rest : List (Nat × Bool))
      (verified keys : List Nat) (unseen : id ∉ verified)
      (nonempty : children id ≠ [])
      (decreasing : ∀ child ∈ children id, child < id) :
      NativeStep children ⟨roots, (id, false) :: rest, verified, keys⟩
        ⟨roots, scheduled (children id) verified ++ (id, true) :: rest,
          verified, keys⟩
  | publish (id : Nat) (ready : Bool) (roots : List Nat)
      (rest : List (Nat × Bool)) (verified keys : List Nat)
      (unseen : id ∉ verified)
      (readyOrLeaf : ready = true ∨ children id = [])
      (decreasing : ∀ child ∈ children id, child < id)
      (lookups : ∀ child ∈ children id, child ∈ keys) :
      NativeStep children ⟨roots, (id, ready) :: rest, verified, keys⟩
        ⟨roots, rest, id :: verified, id :: keys⟩

inductive NativeRun (children : Children) : NativeScan → NativeScan → Prop where
  | refl (state : NativeScan) : NativeRun children state state
  | tail {first middle last} : NativeRun children first middle →
      NativeStep children middle last → NativeRun children first last

def agrees (state : NativeScan) : Prop :=
  ∀ id, id ∈ state.verified ↔ id ∈ state.keys

theorem step_agrees {children : Children} {before after : NativeScan}
    (step : NativeStep children before after) (old : agrees before) :
    agrees after := by
  cases step with
  | root => exact old
  | skip => exact old
  | expand => exact old
  | publish id ready roots rest verified keys unseen readyOrLeaf decreasing lookups =>
      intro key
      simp only [List.mem_cons]
      exact or_congr Iff.rfl (old key)

theorem step_closed {children : Children} {before after : NativeScan}
    (step : NativeStep children before after)
    (old : Closed children before.keys) : Closed children after.keys := by
  cases step with
  | root => exact old
  | skip => exact old
  | expand => exact old
  | publish id ready roots rest verified keys unseen readyOrLeaf decreasing lookups =>
      intro parent member child edge
      rcases List.mem_cons.mp member with same | previous
      · subst parent
        exact List.mem_cons_of_mem id (lookups child edge)
      · exact List.mem_cons_of_mem id (old parent previous child edge)

theorem step_marked {children : Children} {before after : NativeScan}
    (step : NativeStep children before after) (same : agrees before)
    {id : Nat} (old : marked before id) : marked after id := by
  cases step with
  | root head roots verified keys =>
      simpa [marked, active] using old
  | skip head ready roots rest verified keys seen =>
      rcases old with key | pending
      · exact Or.inl key
      · have positions : id = head ∨ id ∈ rest.map Prod.fst ++ roots := by
          simpa [active] using pending
        rcases positions with equal | later
        · subst id; exact Or.inl ((same head).mp seen)
        · exact Or.inr later
  | expand head roots rest verified keys unseen nonempty decreasing =>
      rcases old with key | pending
      · exact Or.inl key
      · apply Or.inr
        have positions : id = head ∨ id ∈ rest.map Prod.fst ++ roots := by
          simpa [active] using pending
        simp only [active, List.map_append, List.map_cons, List.append_assoc,
          List.mem_append, List.mem_cons, or_assoc]
        simp only [List.mem_append, or_assoc] at positions
        exact Or.inr positions
  | publish head ready roots rest verified keys unseen readyOrLeaf decreasing lookups =>
      rcases old with key | pending
      · exact Or.inl (List.mem_cons_of_mem head key)
      · have positions : id = head ∨ id ∈ rest.map Prod.fst ++ roots := by
          simpa [active] using pending
        rcases positions with equal | later
        · subst id; exact Or.inl List.mem_cons_self
        · exact Or.inr later

theorem step_sound {children : Children} {roots : List Nat}
    {before after : NativeScan} (step : NativeStep children before after)
    (old : ∀ id, marked before id → Reach children roots id) :
    ∀ id, marked after id → Reach children roots id := by
  cases step with
  | root head remaining verified keys =>
      simpa [marked, active] using old
  | skip head ready remaining rest verified keys seen =>
      intro id found
      apply old id
      rcases found with key | later
      · exact Or.inl key
      · exact Or.inr (by simpa [active] using
          (Or.inr later : id = head ∨ id ∈ rest.map Prod.fst ++ remaining))
  | expand head remaining rest verified keys unseen nonempty decreasing =>
      intro id found
      rcases found with key | pending
      · exact old id (Or.inl key)
      · have positions : id ∈ (scheduled (children head) verified).map Prod.fst ∨
            id = head ∨ id ∈ rest.map Prod.fst ++ remaining := by
          simpa [active, List.map_append, List.append_assoc, or_assoc] using pending
        rcases positions with added | equal | later
        · have edge := ((scheduled_member (children head) verified id).mp added).1
          exact Reach.child (old head (Or.inr (by simp [active]))) edge
        · subst id; exact old head (Or.inr (by simp [active]))
        · exact old id (Or.inr (by simpa [active] using
            (Or.inr later : id = head ∨ id ∈ rest.map Prod.fst ++ remaining)))
  | publish head ready remaining rest verified keys unseen readyOrLeaf decreasing lookups =>
      intro id found
      rcases found with key | later
      · rcases List.mem_cons.mp key with equal | previous
        · subst id; exact old head (Or.inr (by simp [active]))
        · exact old id (Or.inl previous)
      · exact old id (Or.inr (by simpa [active] using
          (Or.inr later : id = head ∨ id ∈ rest.map Prod.fst ++ remaining)))

theorem run_invariants {children : Children} {roots : List Nat}
    {before after : NativeScan} (run : NativeRun children before after)
    (same : agrees before) (closed : Closed children before.keys)
    (sound : ∀ id, marked before id → Reach children roots id) :
    agrees after ∧ Closed children after.keys ∧
      (∀ id, marked after id → Reach children roots id) ∧
      (∀ id, marked before id → marked after id) := by
  induction run with
  | refl => exact ⟨same, closed, sound, fun _ found => found⟩
  | tail prior step ih =>
      obtain ⟨same', closed', sound', keeps⟩ := ih
      exact ⟨step_agrees step same', step_closed step closed',
        step_sound step sound', fun id found => step_marked step same' (keeps id found)⟩

/-- Native outer-loop/ready-stack projection, including successful empty and
duplicate/shared-root executions. No equality-of-domain hypothesis appears. -/
theorem completed_native_control_domain (children : Children)
    (roots verified keys : List Nat)
    (run : NativeRun children ⟨roots, [], [], []⟩ ⟨[], [], verified, keys⟩) :
    (∀ id, id ∈ verified ↔ id ∈ keys) ∧
      (∀ id, id ∈ keys ↔ Reach children roots id) := by
  have initialSame : agrees ⟨roots, [], [], []⟩ := by
    intro id; rfl
  have initialClosed : Closed children [] := by
    intro parent impossible; cases impossible
  have initialSound : ∀ id, marked ⟨roots, [], [], []⟩ id →
      Reach children roots id := by
    intro id found
    have member : id ∈ roots := by simpa [marked, active] using found
    exact Reach.root member
  obtain ⟨same, closed, sound, keeps⟩ :=
    run_invariants run initialSame initialClosed initialSound
  refine ⟨same, ?_⟩
  intro id
  constructor
  · intro member; exact sound id (Or.inl member)
  · intro reachable
    induction reachable with
    | root member =>
        have retained := keeps _ (Or.inr (by simpa [active] using member))
        simpa [marked, active] using retained
    | child parent edge ih => exact closed _ ih _ edge

theorem completed_control_identity (children : Children)
    (roots verified keys : List Nat)
    (run : NativeRun children ⟨roots, [], [], []⟩ ⟨[], [], verified, keys⟩)
    (identityRoot : 0 ∈ roots) : 0 ∈ keys :=
  ((completed_native_control_domain children roots verified keys run).2 0).mpr
    (Reach.root identityRoot)

theorem completed_control_empty (children : Children) (verified keys : List Nat)
    (run : NativeRun children ⟨[], [], [], []⟩ ⟨[], [], verified, keys⟩) :
    ∀ id, id ∉ keys := by
  intro id member
  have reachable :=
    ((completed_native_control_domain children [] verified keys run).2 id).mp member
  induction reachable with
  | root impossible => cases impossible
  | child parent edge ih => exact ih

/-- Actual readback distinguishes logical identity and stored constructors. -/
inductive Readback (expression : Nat → Expr) (seeds : List Nat) : Nat → Prop where
  | seed {id} : id ∈ seeds → Readback expression seeds id
  | child {parent id} : Readback expression seeds parent → parent ≠ 0 →
      id ∈ (expression parent).children → Readback expression seeds id

def StoredObservation (expression : Nat → Expr) (seeds : List Nat) (id : Nat) : Prop :=
  id ≠ 0 ∧ Readback expression seeds id

def LogicalObservationR4 (expression : Nat → Expr) (seeds : List Nat) (id : Nat) : Prop :=
  id = 0 ∨ StoredObservation expression seeds id

def WeightObservation (expression : Nat → Expr) (seeds : List Nat) (weight : Nat) : Prop :=
  ∃ id, StoredObservation expression seeds id ∧ (expression id).weight = some weight

theorem identity_has_no_stored_row (expression : Nat → Expr) (seeds : List Nat) :
    ¬ StoredObservation expression seeds 0 := fun stored => stored.1 rfl

theorem identity_logically_observed (expression : Nat → Expr) (seeds : List Nat) :
    LogicalObservationR4 expression seeds 0 := Or.inl rfl

theorem seeded_target_observed (expression : Nat → Expr) (seeds : List Nat)
    (id : Nat) (seeded : id ∈ seeds) : LogicalObservationR4 expression seeds id := by
  by_cases identity : id = 0
  · exact Or.inl identity
  · exact Or.inr ⟨identity, Readback.seed seeded⟩

theorem observed_child (expression : Nat → Expr) (seeds : List Nat)
    {parent child : Nat} (stored : StoredObservation expression seeds parent)
    (edge : child ∈ (expression parent).children) :
    LogicalObservationR4 expression seeds child := by
  by_cases identity : child = 0
  · exact Or.inl identity
  · exact Or.inr ⟨identity, Readback.child stored.2 stored.1 edge⟩

theorem observed_constructor_weight (expression : Nat → Expr) (seeds : List Nat)
    {id weight : Nat} (stored : StoredObservation expression seeds id)
    (payload : (expression id).weight = some weight) :
    WeightObservation expression seeds weight := ⟨id, stored, payload⟩

/-- An already selected constructor remains observed when readback seeds grow.
No effective relation root or discharge-stability premise is used. -/
theorem readback_monotone (expression : Nat → Expr) (before after : List Nat)
    (included : ∀ id ∈ before, id ∈ after) {id : Nat}
    (observed : Readback expression before id) : Readback expression after id := by
  induction observed with
  | seed member => exact Readback.seed (included _ member)
  | child parent nonzero edge ih => exact Readback.child ih nonzero edge

theorem weight_monotone (expression : Nat → Expr) (before after : List Nat)
    (included : ∀ id ∈ before, id ∈ after) {weight : Nat}
    (observed : WeightObservation expression before weight) :
    WeightObservation expression after weight := by
  obtain ⟨id, stored, payload⟩ := observed
  exact ⟨id, ⟨stored.1, readback_monotone expression before after included stored.2⟩, payload⟩

/-- The native successful constructor reconstruction, before interning. All
six stored constructors remain present; identity has no stored constructor. -/
def renameExpr (contextMap weightMap certificateMap : Nat → Nat) : Expr → Expr
  | .identity => .identity
  | .prefixLeft input weight => .prefixLeft (contextMap input) (weightMap weight)
  | .suffixRightPops input weight => .suffixRightPops (contextMap input) (weightMap weight)
  | .swap input => .swap (contextMap input)
  | .bothFromRight input certificate =>
      .bothFromRight (contextMap input) (certificateMap certificate)
  | .replay lower upper => .replay (contextMap lower) (contextMap upper)
  | .withoutLeftFilter input => .withoutLeftFilter (contextMap input)

theorem renamed_children (contextMap weightMap certificateMap : Nat → Nat)
    (expression : Expr) :
    (renameExpr contextMap weightMap certificateMap expression).children =
      expression.children.map contextMap := by
  cases expression <;> rfl

theorem renamed_weight (contextMap weightMap certificateMap : Nat → Nat)
    (expression : Expr) :
    (renameExpr contextMap weightMap certificateMap expression).weight =
      expression.weight.map weightMap := by
  cases expression <;> rfl

/-- Stored constructor observability follows at each individual successful
interner result when that result has been selected. This does not assert that
every prepared result was selected by the completed native consumer. -/
theorem selected_renamed_weight (source target : Nat → Expr)
    (contextMap weightMap certificateMap : Nat → Nat) (seeds : List Nat)
    {id weight : Nat}
    (published : target (contextMap id) =
      renameExpr contextMap weightMap certificateMap (source id))
    (nonidentity : contextMap id ≠ 0) (seeded : contextMap id ∈ seeds)
    (payload : (source id).weight = some weight) :
    WeightObservation target seeds (weightMap weight) := by
  apply observed_constructor_weight target seeds
    ⟨nonidentity, Readback.seed seeded⟩
  rw [published, renamed_weight, payload]
  rfl

end YulangClosure.NativeFreshUseContextCoverageR4
