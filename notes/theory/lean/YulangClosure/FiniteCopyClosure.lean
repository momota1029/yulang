import YulangClosure.NativeValueStructure

/-!
A conditional obstruction to finite closure of the post-merge Value projection.

The successor of a negative copy is DERIVED below from individual cut, row,
Function, copying and rewritten-bound rules. It is not a hypothesis. These
rules still require application to an actual completed native prefix: this
module does not prove Replay fiber completeness, settlement scheduling, source
reachability, or signed-occurrence qualification. In particular it is not a
proof that bounded Rust identities can never produce IdentityExhausted.

The intended snapshot is before the FIRST subsequent intrusion settlement.
Rows and selected copy identities therefore have no intervening quotient.
Effects are fixed inert ports; only the two Value ports are represented.
-/

namespace YulangClosure.FiniteCopyClosure

/-- Value-only Function shapes; both ports are row identities. -/
inductive Value where
  | row (id : Nat)
  | function (argument result : Nat)
  deriving DecidableEq, Repr

structure Snapshot where
  level : Nat → Nat
  lower : Nat → Value → Prop
  upper : Nat → Value → Prop
  demand : Value → Value → Prop
  /-- `copy b a r n p` records a completed positive extrusion of F(b,b)
  into r, with negative/positive b copies n,p. The selected negative snapshot
  contained the already-low upper a. This is NOT an arbitrary earlier copy. -/
  copy : Nat → Nat → Nat → Nat → Nat → Prop

/-- Primitive obligations for a successfully completed, merge-free prefix.
They are explicit premises, not a claim of a native or source instance.
The copied-bound clauses refer to the selected snapshot recorded by `copy`;
they do not copy an upper added only after the operation. -/
structure Closed (s : Snapshot) : Prop where
  cut : ∀ {owner lo hi}, s.lower owner lo → s.upper owner hi → s.demand lo hi
  argument : ∀ {a r b t},
    s.demand (.function a r) (.function b t) → s.demand (.row b) (.row a)
  rowUpper : ∀ {a b}, a ≠ b → s.level b ≤ s.level a →
    s.demand (.row a) (.row b) → s.upper a (.row b)
  installLowFunction : ∀ {a r receiver},
    s.demand (.function a r) (.row receiver) →
    s.level a ≤ s.level receiver → s.level r ≤ s.level receiver →
    s.lower receiver (.function a r)
  positiveExtrusion : ∀ {b a receiver},
    s.demand (.function b b) (.row receiver) →
    s.level receiver < s.level b → s.upper b (.row a) →
    s.level a ≤ s.level receiver →
    ∃ n p, s.copy b a receiver n p
  copiedUpper : ∀ {b a receiver n p},
    s.copy b a receiver n p → s.upper n (.row a)
  rewrittenLower : ∀ {b a receiver n p},
    s.copy b a receiver n p → s.lower receiver (.function n p)
  negativeLevel : ∀ {b a receiver n p},
    s.copy b a receiver n p → s.level n = s.level receiver
  positiveLevel : ∀ {b a receiver n p},
    s.copy b a receiver n p → s.level p = s.level receiver
  freshAfterReceiver : ∀ {b a receiver n p},
    s.copy b a receiver n p → receiver < n

/-- The state AFTER the qualified A copy has merged and B <: A has been
admitted. Constructing this seed from a source term is a separate obligation. -/
structure Seed (s : Snapshot) (a b : Nat) : Prop where
  anchorLow : s.level a = 0
  parentHigh : s.level b = 1
  parentLower : s.lower b (.function b b)
  anchorUpper : s.upper a (.function b b)
  parentUpper : s.upper b (.row a)

/-- A copy whose rewritten Function can flow to the fixed low anchor. -/
def AnchoredCopy (s : Snapshot) (a b n : Nat) : Prop :=
  ∃ receiver p, s.copy b a receiver n p ∧ s.level receiver = 0 ∧
    (receiver = a ∨ s.upper receiver (.row a))

theorem initial_copy (s : Snapshot) (a b : Nat)
    (closed : Closed s) (seed : Seed s a b) :
    ∃ n, AnchoredCopy s a b n := by
  have demand := closed.cut seed.parentLower seed.parentUpper
  have younger : s.level a < s.level b := by
    simp [seed.anchorLow, seed.parentHigh]
  obtain ⟨n, p, copied⟩ := closed.positiveExtrusion demand younger
    seed.parentUpper (Nat.le_refl (s.level a))
  exact ⟨n, a, p, copied, seed.anchorLow, Or.inl rfl⟩

/-- The full local cycle, including the previously implicit second
unchanged extrusion when the rewritten Function reaches the low anchor. -/
theorem anchored_copy_produces_newer (s : Snapshot) (a b n : Nat)
    (closed : Closed s) (seed : Seed s a b)
    (anchored : AnchoredCopy s a b n) :
    ∃ next, AnchoredCopy s a b next ∧ n < next := by
  obtain ⟨receiver, p, copied, receiverLow, reachesAnchor⟩ := anchored
  have nLow : s.level n = 0 := (closed.negativeLevel copied).trans receiverLow
  have pLow : s.level p = 0 := (closed.positiveLevel copied).trans receiverLow
  have upperAnchor : s.upper n (.row a) := closed.copiedUpper copied
  have atReceiver : s.lower receiver (.function n p) := closed.rewrittenLower copied
  have atAnchor : s.lower a (.function n p) := by
    cases reachesAnchor with
    | inl same => simpa [same] using atReceiver
    | inr upper =>
        exact closed.installLowFunction (closed.cut atReceiver upper)
          (by simp [nLow, seed.anchorLow])
          (by simp [pLow, seed.anchorLow])
  have functionCut := closed.cut atAnchor seed.anchorUpper
  have contravariant := closed.argument functionCut
  have different : b ≠ n := by
    intro same
    have equalLevels := congrArg s.level same
    simp [seed.parentHigh, nLow] at equalLevels
  have toN : s.upper b (.row n) := closed.rowUpper different
    (by simp [nLow, seed.parentHigh]) contravariant
  have nextDemand := closed.cut seed.parentLower toN
  obtain ⟨next, q, nextCopy⟩ := closed.positiveExtrusion nextDemand
    (by simp [nLow, seed.parentHigh]) seed.parentUpper
    (by simp [seed.anchorLow, nLow])
  exact ⟨next, ⟨n, q, nextCopy, nLow, Or.inr upperAnchor⟩,
    closed.freshAfterReceiver nextCopy⟩

theorem arbitrarily_large_anchored_copy (s : Snapshot) (a b : Nat)
    (closed : Closed s) (seed : Seed s a b) :
    ∀ bound, ∃ n, AnchoredCopy s a b n ∧ bound ≤ n := by
  intro bound
  induction bound with
  | zero =>
      obtain ⟨n, anchored⟩ := initial_copy s a b closed seed
      exact ⟨n, anchored, Nat.zero_le n⟩
  | succ bound ih =>
      obtain ⟨n, anchored, large⟩ := ih
      obtain ⟨next, nextAnchored, newer⟩ :=
        anchored_copy_produces_newer s a b n closed seed anchored
      exact ⟨next, nextAnchored,
        Nat.succ_le_of_lt (Nat.lt_of_le_of_lt large newer)⟩

/-- Only the negative copies of this one parent need a finite bound.
This conclusion concerns successful fixed-point closure, not resource errors. -/
theorem no_finite_copy_closure (s : Snapshot) (a b : Nat)
    (closed : Closed s) (seed : Seed s a b)
    (finiteCopies : ∃ limit, ∀ receiver n p,
      s.copy b a receiver n p → n ≤ limit) : False := by
  obtain ⟨limit, bounded⟩ := finiteCopies
  obtain ⟨n, anchored, large⟩ :=
    arbitrarily_large_anchored_copy s a b closed seed (limit + 1)
  obtain ⟨receiver, p, copied, _, _⟩ := anchored
  exact Nat.not_succ_le_self limit (Nat.le_trans large (bounded receiver n p copied))

/-- A direct application of the EXISTING native selection definition:
B <: N stores an upper on B when B is at 1 and N at 0. No symmetric
row storage or lowering of B is silently assumed in the cycle. -/
theorem native_high_to_low_selects_parent_upper (levels : Nat → Nat)
    (parent receiver : Nat) (parentHigh : levels parent = 1)
    (receiverLow : levels receiver = 0) :
    NativeValueStructure.selectBound levels
      ⟨.row parent, .row receiver⟩ =
      some ⟨parent, .negative, .row receiver⟩ := by
  have different : parent ≠ receiver := by
    intro same
    have equalLevels := congrArg levels same
    simp [parentHigh, receiverLow] at equalLevels
  rw [NativeValueStructure.selected_bound_rows different]
  simp [parentHigh, receiverLow]

end YulangClosure.FiniteCopyClosure
