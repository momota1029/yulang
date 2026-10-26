import YulangClosure.SimpleSubGeneralizationSoundness

/-!
Owner-local publication for finite structural bounds. Positive owners store a
lower bound; negative owners store an upper bound, matching candidate_scheme
expand_row. Capture reachability stops at nonlocal owners. Allocation eligibility
is separate: prepare_candidate_fresh_use additionally rechecks current level and
non_generic. This module derives clause inclusion, not equality of publications.

The explicit dependency-closure and inactive-image conditions below are NOT
claimed as invariants of every Rust history. Extra effect incidence/reverse
frontiers, canonical first-image coherence, evidence and source scope remain
native correspondence obligations. No source typing or final clause-inclusion
law is assumed.
-/
namespace YulangClosure.SimpleSub.ScopedPublication

structure Row where
  kind : Kind
  index : Nat
  deriving DecidableEq

abbrev Flags := Kind → Nat → Bool

def Row.active (flags : Flags) (r : Row) : Bool := flags r.kind r.index

def Row.rename (q : Renaming) (r : Row) : Row := ⟨r.kind, q r.kind r.index⟩

def vars {k} : Term k → List Row
  | .var i => [⟨k, i⟩]
  | .atom _ | .bottom | .top | .recordNil | .tupleNil | .variantNil => []
  | .union a b | .intersection a b => vars a ++ vars b
  | .function a ae re r => vars a ++ vars ae ++ vars re ++ vars r
  | .recordCons _ _ a b | .tupleCons a b | .variantCons _ a b => vars a ++ vars b

theorem vars_rename (q : Renaming) {k} (t : Term k) :
    vars (t.rename q) = (vars t).map (Row.rename q) := by
  induction t <;> simp_all [vars, Term.rename, Term.subst, List.map_append, Row.rename]

theorem subst_congr_vars (ρ σ : Valuation) {k} (t : Term k)
    (same : ∀ k i, (⟨k, i⟩ : Row) ∈ vars t → ρ k i = σ k i) :
    t.subst ρ = t.subst σ := by
  induction t <;> simp_all [vars, Term.subst]

theorem rename_fixed {k} (t : Term k) (f : Renaming)
    (fixed : ∀ k i, (⟨k, i⟩ : Row) ∈ vars t → f k i = i) : t.rename f = t := by
  calc
    t.rename f = t.subst (fun _ i => .var i) := by
      apply subst_congr_vars
      intro k i member
      exact congrArg Term.var (fixed k i member)
    _ = t := Term.subst_id t

theorem rename_comp (q f : Renaming) {k} (t : Term k) :
    (t.rename q).rename f = t.rename (fun k i => f k (q k i)) := by
  simp [Term.rename, Term.subst_comp, Term.subst]

structure Bound where
  kind : Kind
  owner : Nat
  side : Polarity
  body : Term kind

def Bound.row (b : Bound) : Row := ⟨b.kind, b.owner⟩

def Bound.clause (b : Bound) : Constraint :=
  match b.side with
  | .positive => ⟨b.kind, b.body, .var b.owner⟩
  | .negative => ⟨b.kind, .var b.owner, b.body⟩

def Bound.rename (q : Renaming) (b : Bound) : Bound :=
  ⟨b.kind, q b.kind b.owner, b.side, b.body.rename q⟩

@[simp] theorem Bound.rename_row (q : Renaming) (b : Bound) :
    (b.rename q).row = b.row.rename q := rfl

@[simp] theorem Bound.rename_clause (q : Renaming) (b : Bound) :
    (b.rename q).clause = b.clause.rename q := by
  cases b with | mk k i side body =>
    cases side <;> rfl

def BoundsBounded (n : Nat) (bounds : List Bound) : Prop :=
  ∀ b, b ∈ bounds → b.owner < n ∧ Generalization.Bounded n b.body

theorem Bound.clause_bounded {n} (b : Bound)
    (bounded : b.owner < n ∧ Generalization.Bounded n b.body) : Generalization.ConstraintBounded n b.clause := by
  cases b with | mk k i side body =>
    cases side with
    | positive => exact ⟨bounded.2, bounded.1⟩
    | negative => exact bounded

/-- Root rows are retained; only local owners expose their bound dependencies. -/
inductive Reach (bounds : List Bound) (captured : Flags) (roots : List Row) : Row → Prop
  | root (r : Row) : r ∈ roots → Reach bounds captured roots r
  | step (b : Bound) : b ∈ bounds → Reach bounds captured roots b.row →
      b.row.active captured = true → (r : Row) → r ∈ vars b.body →
      Reach bounds captured roots r

/-- No active dependency can hide below an owner at which capture stops. This
is a concrete dependency property, not a conclusion about published clauses. -/
def StoppedClosed (bounds : List Bound) (captured : Flags) : Prop :=
  ∀ b, b ∈ bounds → b.row.active captured = false →
    ∀ r, r ∈ vars b.body → r.active captured = false

theorem reachable_active_image {bounds before after roots q}
    (closed : StoppedClosed (bounds.map (Bound.rename q)) after)
    {r} (reach : Reach bounds before roots r) :
    (r.rename q).active after = true →
      Reach (bounds.map (Bound.rename q)) after (roots.map (Row.rename q)) (r.rename q) := by
  induction reach with
  | root r member =>
    intro _
    exact .root _ (List.mem_map.mpr ⟨r, member, rfl⟩)
  | step b member prior active r dependency ih =>
    intro targetActive
    have mapped : b.rename q ∈ bounds.map (Bound.rename q) := List.mem_map.mpr ⟨b, member, rfl⟩
    have dep : r.rename q ∈ vars (b.rename q).body := by
      rw [Bound.rename, vars_rename]
      exact List.mem_map.mpr ⟨r, dependency, rfl⟩
    have ownerActive : (b.rename q).row.active after = true := by
      cases h : (b.rename q).row.active after with
      | true => rfl
      | false =>
        have stopped := closed _ mapped h _ dep
        rw [targetActive] at stopped
        contradiction
    exact .step _ mapped (ih ownerActive) ownerActive _ dep

/-- Boolean guard encoding only; these are not source birth or live row levels. -/
def guardLevels (flags : Flags) : Generalization.Levels := fun k i => if flags k i then 1 else 0

def fresh (n : Nat) (flags : Flags) (use : Nat) : Renaming :=
  Generalization.freshen n 0 (guardLevels flags) use

@[simp] theorem fresh_inactive {n flags use k i} (inactive : flags k i = false) :
    fresh n flags use k i = i := by simp [fresh, Generalization.freshen, guardLevels, inactive]

@[simp] theorem fresh_active {n flags use k i} (active : flags k i = true) :
    fresh n flags use k i = Generalization.copyIndex n use i := by
  simp [fresh, Generalization.freshen, guardLevels, active, Generalization.copyIndex]

def InactiveImages (n : Nat) (before after : Flags) (q : Renaming) : Prop :=
  ∀ k i, i < n → before k i = false → after k (q k i) = false

theorem guard_anchors {n before after q} (images : InactiveImages n before after q) :
    Generalization.PreservesAnchors n 0 (guardLevels before) (guardLevels after) q := by
  intro k i hi low
  have inactive : before k i = false := by
    cases h : before k i <;> simp_all [guardLevels]
  simp [guardLevels, images k i hi inactive]

/-- A complete retained base plus only the bounds of reached local owners.
Every actual use gets one coherent renaming, including four-port dependencies. -/
inductive Published (n : Nat) (bounds : List Bound) (captured allocation : Flags)
    (roots : List Row) (uses : List Nat) : Constraint → Prop
  | base (b : Bound) : b ∈ bounds → Published n bounds captured allocation roots uses b.clause
  | copy (b : Bound) : b ∈ bounds → (use : Nat) → use ∈ uses →
      Reach bounds captured roots b.row → b.row.active captured = true →
      Published n bounds captured allocation roots uses (b.clause.rename (fresh n allocation use))

def Satisfied (n : Nat) (bounds : List Bound) (captured allocation : Flags)
    (roots : List Row) (uses : List Nat) (ρ : Valuation) : Prop :=
  ∀ c, Published n bounds captured allocation roots uses c → c.Satisfied ρ

private theorem rename_congr_bounded {n k} {t : Term k} (bounded : Generalization.Bounded n t)
    (f g : Renaming) (same : ∀ k i, i < n → f k i = g k i) : t.rename f = t.rename g := by
  apply Generalization.subst_congr_on n _ _ _ bounded
  intro k i hi
  exact congrArg Term.var (same k i hi)

private theorem base_commutes {n count after q} (c : Constraint)
    (bounded : Generalization.ConstraintBounded n c) :
    c.rename (Generalization.transport n count 0 (guardLevels after) q) = c.rename q := by
  cases c with | mk k lower upper =>
    unfold Constraint.rename
    rw [rename_congr_bounded bounded.1 _ _ (fun _ _ hi => Generalization.transport_base hi),
      rename_congr_bounded bounded.2 _ _ (fun _ _ hi => Generalization.transport_base hi)]

private theorem copy_commutes {n count before after q use} (c : Constraint)
    (bounded : Generalization.ConstraintBounded n c) (images : InactiveImages n before after q)
    (hu : use < count) :
    (c.rename (fresh n before use)).rename (Generalization.transport n count 0 (guardLevels after) q) =
      (c.rename q).rename (fresh n after use) := by
  have eqn : ∀ k i, i < n →
      Generalization.transport n count 0 (guardLevels after) q k (fresh n before use k i) =
        fresh n after use k (q k i) := by
    intro k i hi
    exact Generalization.transport_freshen (guard_anchors images) hu hi
  cases c with | mk k lower upper =>
    simp only [Constraint.rename, rename_comp]
    rw [rename_congr_bounded bounded.1 _ _ eqn, rename_congr_bounded bounded.2 _ _ eqn]

theorem stopped_clause_fixed {n captured allocation use} (b : Bound)
    (owner : b.row.active captured = false)
    (dependencies : ∀ r, r ∈ vars b.body → r.active captured = false)
    (stops : ∀ k i, captured k i = false → allocation k i = false) :
    b.clause.rename (fresh n allocation use) = b.clause := by
  have body := rename_fixed b.body (fresh n allocation use) (by
    intro k i member
    exact fresh_inactive (stops k i (dependencies ⟨k, i⟩ member)))
  have row : fresh n allocation use b.kind b.owner = b.owner :=
    fresh_inactive (stops _ _ owner)
  cases b with | mk k i side term =>
    cases side <;> simp_all [Bound.clause, Constraint.rename, Term.rename, Term.subst]

/-- Derived inclusion of every transported original published clause. Post-low
owners use their retained base clause, justified by dependency closure. No
reverse reachability or quotient-class saturation is needed for this direction. -/
theorem publication_clause_image {n count bounds beforeCap afterCap beforeUse afterUse roots uses q}
    (bounded : BoundsBounded n bounds)
    (images : InactiveImages n beforeUse afterUse q)
    (closed : StoppedClosed (bounds.map (Bound.rename q)) afterCap)
    (stops : ∀ k i, afterCap k i = false → afterUse k i = false)
    (useBounds : ∀ use, use ∈ uses → use < count)
    {c} (published : Published n bounds beforeCap beforeUse roots uses c) :
    Published n (bounds.map (Bound.rename q)) afterCap afterUse (roots.map (Row.rename q)) uses
      (c.rename (Generalization.transport n count 0 (guardLevels afterUse) q)) := by
  cases published with
  | base b member =>
    rw [base_commutes _ (b.clause_bounded (bounded b member))]
    rw [← Bound.rename_clause]
    exact .base _ (List.mem_map.mpr ⟨b, member, rfl⟩)
  | copy b member use hu reach active =>
    rw [copy_commutes _ (b.clause_bounded (bounded b member)) images (useBounds use hu)]
    rw [← Bound.rename_clause]
    have mapped : b.rename q ∈ bounds.map (Bound.rename q) := List.mem_map.mpr ⟨b, member, rfl⟩
    cases h : (b.rename q).row.active afterCap with
    | true =>
      exact .copy _ mapped use hu (reachable_active_image closed reach h) h
    | false =>
      rw [stopped_clause_fixed _ h (closed _ mapped h) stops]
      exact .base _ mapped

/-- One valuation reflects the retained base and the actual selected owner
clauses of arbitrarily many finite uses, rather than all-store copies. -/
theorem publication_solution_pullback {n count bounds beforeCap afterCap beforeUse afterUse roots uses q}
    (bounded : BoundsBounded n bounds)
    (images : InactiveImages n beforeUse afterUse q)
    (closed : StoppedClosed (bounds.map (Bound.rename q)) afterCap)
    (stops : ∀ k i, afterCap k i = false → afterUse k i = false)
    (useBounds : ∀ use, use ∈ uses → use < count)
    (ρ : Valuation)
    (solved : Satisfied n (bounds.map (Bound.rename q)) afterCap afterUse
      (roots.map (Row.rename q)) uses ρ) :
    Satisfied n bounds beforeCap beforeUse roots uses
      (fun k i => ρ k (Generalization.transport n count 0 (guardLevels afterUse) q k i)) := by
  intro c hc
  exact (Constraint.rename_satisfied _ ρ c).mp
    (solved _ (publication_clause_image bounded images closed stops useBounds hc))

theorem publication_with_clients {n count bounds beforeCap afterCap beforeUse afterUse roots uses q}
    (bounded : BoundsBounded n bounds)
    (images : InactiveImages n beforeUse afterUse q)
    (closed : StoppedClosed (bounds.map (Bound.rename q)) afterCap)
    (stops : ∀ k i, afterCap k i = false → afterUse k i = false)
    (useBounds : ∀ use, use ∈ uses → use < count)
    (clients : Store) (ρ : Valuation)
    (solved : Satisfied n (bounds.map (Bound.rename q)) afterCap afterUse
      (roots.map (Row.rename q)) uses ρ)
    (clientSolved : Store.Satisfied ρ (clients.map (Constraint.rename (Generalization.transport n count 0 (guardLevels afterUse) q)))) :
    Satisfied n bounds beforeCap beforeUse roots uses
      (fun k i => ρ k (Generalization.transport n count 0 (guardLevels afterUse) q k i)) ∧
    clients.Satisfied (fun k i => ρ k (Generalization.transport n count 0 (guardLevels afterUse) q k i)) := by
  exact ⟨publication_solution_pullback bounded images closed stops useBounds ρ solved,
    (Store.quotient_pullback _ _ _).mp clientSolved⟩

structure Metadata where
  levels : Generalization.Levels
  nonGeneric : Flags

def captureGuard (boundary : Nat) (metadata : Metadata) : Flags :=
  fun k i => decide (boundary < metadata.levels k i) && !(metadata.nonGeneric k i)

def useGuard (captured : Flags) (boundary : Nat) (metadata : Metadata) : Flags :=
  fun k i => captured k i && captureGuard boundary metadata k i

theorem useGuard_stops (captured : Flags) (boundary : Nat) (metadata : Metadata)
    (k : Kind) (i : Nat) (inactive : captured k i = false) :
    useGuard captured boundary metadata k i = false := by simp [useGuard, inactive]

def BoundLevelsClosed (bounds : List Bound) (levels : Generalization.Levels) : Prop :=
  ∀ b, b ∈ bounds → ∀ r, r ∈ vars b.body → levels r.kind r.index ≤ levels b.kind b.owner

def NonGenericClosed (bounds : List Bound) (flags : Flags) : Prop :=
  ∀ b, b ∈ bounds → flags b.kind b.owner = true →
    ∀ r, r ∈ vars b.body → flags r.kind r.index = true

/-- Actual level inequalities plus non-generic dependency propagation imply
stopping closure. Minimum owner level alone is insufficient. -/
theorem capture_stopped_closed {bounds boundary metadata}
    (levels : BoundLevelsClosed bounds metadata.levels)
    (nonGeneric : NonGenericClosed bounds metadata.nonGeneric) :
    StoppedClosed bounds (captureGuard boundary metadata) := by
  intro b member stopped r dependency
  by_cases high : boundary < metadata.levels b.kind b.owner
  · have ng : metadata.nonGeneric b.kind b.owner = true := by
      cases h : metadata.nonGeneric b.kind b.owner <;>
        simp_all [Row.active, Bound.row, captureGuard]
    have dep := nonGeneric b member ng r dependency
    simp [Row.active, captureGuard, dep]
  · have le := levels b member r dependency
    have low : ¬ boundary < metadata.levels r.kind r.index := by omega
    simp [Row.active, captureGuard, low]

/-- Exact metadata properties needed for an inactive image. They reflect the
minimum-level and non-generic-OR merge fields, but their all-history native
invariants are not assumed to follow from inspecting a single write site. -/
def MetadataTransport (n : Nat) (before after : Metadata) (q : Renaming) : Prop :=
  (∀ k i, i < n → after.levels k (q k i) ≤ before.levels k i) ∧
  (∀ k i, i < n → before.nonGeneric k i = true → after.nonGeneric k (q k i) = true)

theorem capture_inactive_images {n before after q boundary}
    (metadata : MetadataTransport n before after q) :
    InactiveImages n (captureGuard boundary before) (captureGuard boundary after) q := by
  intro k i hi inactive
  by_cases high : boundary < before.levels k i
  · have ng : before.nonGeneric k i = true := by
      cases h : before.nonGeneric k i <;> simp_all [captureGuard]
    simp [captureGuard, metadata.2 k i hi ng]
  · have lowered := metadata.1 k i hi
    have low : ¬ boundary < after.levels k (q k i) := by omega
    simp [captureGuard, low]

theorem use_inactive_images {n beforeCap afterCap beforeLive afterLive q boundary}
    (capture : InactiveImages n beforeCap afterCap q)
    (live : MetadataTransport n beforeLive afterLive q) :
    InactiveImages n (useGuard beforeCap boundary beforeLive)
      (useGuard afterCap boundary afterLive) q := by
  intro k i hi inactive
  cases cap : beforeCap k i with
  | false => simp [useGuard, capture k i hi cap]
  | true =>
    have stopped : captureGuard boundary beforeLive k i = false := by
      simpa [useGuard, cap] using inactive
    simp [useGuard, capture_inactive_images live k i hi stopped]

/-- Native-guard specialization: capture uses the snapshot level/non-generic
pair; allocation additionally uses current metadata. The closure hypothesis is
on dependencies of actual owned clauses, not on arbitrary copied-store models. -/
theorem metadata_publication_with_clients
    {n count bounds beforeCapture afterCapture beforeLive afterLive roots uses q boundary}
    (bounded : BoundsBounded n bounds)
    (captureTransport : MetadataTransport n beforeCapture afterCapture q)
    (liveTransport : MetadataTransport n beforeLive afterLive q)
    (levelClosure : BoundLevelsClosed (bounds.map (Bound.rename q)) afterCapture.levels)
    (nonGenericClosure : NonGenericClosed (bounds.map (Bound.rename q)) afterCapture.nonGeneric)
    (useBounds : ∀ use, use ∈ uses → use < count)
    (clients : Store) (ρ : Valuation)
    (solved : Satisfied n (bounds.map (Bound.rename q))
      (captureGuard boundary afterCapture)
      (useGuard (captureGuard boundary afterCapture) boundary afterLive)
      (roots.map (Row.rename q)) uses ρ)
    (clientSolved : Store.Satisfied ρ (clients.map (Constraint.rename
      (Generalization.transport n count 0
        (guardLevels (useGuard (captureGuard boundary afterCapture) boundary afterLive)) q)))) :
    Satisfied n bounds (captureGuard boundary beforeCapture)
      (useGuard (captureGuard boundary beforeCapture) boundary beforeLive) roots uses
      (fun k i => ρ k (Generalization.transport n count 0
        (guardLevels (useGuard (captureGuard boundary afterCapture) boundary afterLive)) q k i)) ∧
    clients.Satisfied (fun k i => ρ k (Generalization.transport n count 0
      (guardLevels (useGuard (captureGuard boundary afterCapture) boundary afterLive)) q k i)) := by
  exact publication_with_clients bounded
    (use_inactive_images (capture_inactive_images captureTransport) liveTransport)
    (capture_stopped_closed levelClosure nonGenericClosure)
    (useGuard_stops _ _ _) useBounds clients ρ solved clientSolved

/-- Numeric level closure alone cannot justify stopping on non-generic owners.
This is a finite metadata counterexample, not an accepted source-program claim. -/
def guardCounterexample : Bound := ⟨.value, 0, .positive, .var 1⟩

def guardCounterexampleMetadata : Metadata :=
  ⟨fun _ _ => 2, fun _ i => decide (i = 0)⟩

theorem numeric_closure_does_not_imply_guard_closure :
    BoundLevelsClosed [guardCounterexample] guardCounterexampleMetadata.levels ∧
    ¬ StoppedClosed [guardCounterexample] (captureGuard 0 guardCounterexampleMetadata) := by
  constructor
  · intro b member r dependency
    simp only [List.mem_singleton] at member
    subst b
    exact Nat.le_refl 2
  · intro closed
    have impossible := closed guardCounterexample (by simp)
      (by decide) ⟨.value, 1⟩ (by simp [guardCounterexample, vars])
    change true = false at impossible
    contradiction

/-- Class minima alone likewise need not preserve dependency closure. The
quotient merges owner 0 with low row 2, leaving its high dependency 1 separate. -/
def minimumCounterexampleMap : Renaming := fun _ i => if i = 0 then 2 else i

def minimumCounterexampleLevels : Generalization.Levels := fun _ i => if i = 2 then 0 else 1

def minimumCounterexampleAfter : Metadata :=
  ⟨Generalization.quotientLevels 3 minimumCounterexampleLevels minimumCounterexampleMap,
    fun _ _ => false⟩

theorem minimum_counterexample_canonical : Generalization.Canonical 3 minimumCounterexampleMap := by
  constructor
  · intro k i hi
    simp only [minimumCounterexampleMap]
    split <;> omega
  · intro k i hi
    simp only [minimumCounterexampleMap]
    split <;> simp_all

theorem minimum_does_not_imply_guard_closure :
    BoundLevelsClosed [guardCounterexample] minimumCounterexampleLevels ∧
    ¬ StoppedClosed ([guardCounterexample].map (Bound.rename minimumCounterexampleMap))
      (captureGuard 0 minimumCounterexampleAfter) := by
  constructor
  · intro b member r dependency
    simp only [List.mem_singleton] at member
    subst b
    have row : r = ⟨.value, 1⟩ := by simpa [guardCounterexample, vars] using dependency
    subst r
    exact Nat.le_refl 1
  · intro closed
    have impossible := closed (guardCounterexample.rename minimumCounterexampleMap) (by simp)
      (by decide) ⟨.value, 1⟩ (by simp [Bound.rename, guardCounterexample, Term.rename,
        Term.subst, vars, minimumCounterexampleMap])
    change true = false at impossible
    contradiction

end YulangClosure.SimpleSub.ScopedPublication
