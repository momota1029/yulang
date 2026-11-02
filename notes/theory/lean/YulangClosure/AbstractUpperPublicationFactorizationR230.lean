import YulangClosure.AbstractUpperInsertionInvariantR229

/-!
R230 structural owner-local publication on the exact successful R229 histories.
The source parents in Contracts remain open. In particular, numeric levels,
the bound-variable SCC below, and structural Sub are not source Value births,
source publication scopes, or complete Yulang Call/effect semantics.
Execution/cache ownership: Luna. Audit commands are requests, not receipts.
-/
namespace YulangClosure.SimpleSub.UpperPublicationR230

open AbstractCore BoundCycleR223 UpperInsertionR229
open ScopedPublication (Bound Flags)

def rowBounds {k : Kind} (owner : Nat) (row : CoreRow k) : List Bound :=
  row.lowerBounds.map (fun body => ⟨k, owner, .positive, body⟩) ++
    row.upperBounds.map (fun body => ⟨k, owner, .negative, body⟩)

def ownedRows {k : Kind} (rows : List (CoreRow k)) : List Bound :=
  rows.zipIdx.flatMap (fun pair => rowBounds pair.2 pair.1)

def ownedBounds (state : CoreState) : List Bound :=
  ownedRows state.valueRows ++ ownedRows state.effectRows

theorem owned_clauses (state : CoreState) :
    (ownedBounds state).map Bound.clause = physicalBounds state := by
  have rows {k : Kind} (rs : List (CoreRow k)) :
      (ownedRows rs).map Bound.clause = physicalRows rs := by
    unfold ownedRows physicalRows
    rw [List.map_flatMap]
    apply congrArg (fun f => rs.zipIdx.flatMap f)
    funext pair
    rcases pair with ⟨row, i⟩
    simp [rowBounds, rowClauses, List.map_append, List.map_map, Function.comp_def, Bound.clause]
  simp only [ownedBounds, physicalBounds, List.map_append, rows]

theorem owned_view {state : CoreState} {b : Bound} (member : b ∈ ownedBounds state) :
    ∃ row : CoreRow b.kind, (state.rows b.kind)[b.owner]? = some row ∧
      (b.side = .positive ∧ b.body ∈ row.lowerBounds ∨
       b.side = .negative ∧ b.body ∈ row.upperBounds) := by
  have view {k : Kind} {rows : List (CoreRow k)} {b : Bound}
      (hb : b ∈ ownedRows rows) :
      (∃ (i : Nat) (row : CoreRow k), rows[i]? = some row ∧
        (∃ body, body ∈ row.lowerBounds ∧ b = ⟨k, i, .positive, body⟩)) ∨
      (∃ (i : Nat) (row : CoreRow k), rows[i]? = some row ∧
        (∃ body, body ∈ row.upperBounds ∧ b = ⟨k, i, .negative, body⟩)) := by
    rcases List.mem_flatMap.mp hb with ⟨⟨row, i⟩, hi, hb⟩
    have lookup := List.mk_mem_zipIdx_iff_getElem?.mp hi
    rcases List.mem_append.mp hb with hb | hb
    · rcases List.mem_map.mp hb with ⟨body, hm, rfl⟩
      exact Or.inl ⟨i, row, lookup, body, hm, rfl⟩
    · rcases List.mem_map.mp hb with ⟨body, hm, rfl⟩
      exact Or.inr ⟨i, row, lookup, body, hm, rfl⟩
  rcases List.mem_append.mp member with member | member
  · rcases view member with ⟨i, row, lookup, body, hm, rfl⟩ |
        ⟨i, row, lookup, body, hm, rfl⟩
    · exact ⟨row, lookup, Or.inl ⟨rfl, hm⟩⟩
    · exact ⟨row, lookup, Or.inr ⟨rfl, hm⟩⟩
  · rcases view member with ⟨i, row, lookup, body, hm, rfl⟩ |
        ⟨i, row, lookup, body, hm, rfl⟩
    · exact ⟨row, lookup, Or.inl ⟨rfl, hm⟩⟩
    · exact ⟨row, lookup, Or.inr ⟨rfl, hm⟩⟩

theorem owned_upper {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) {b : Bound} (member : b ∈ ownedBounds state) :
    b.side = .negative ∧ ∃ row : CoreRow b.kind,
      (state.rows b.kind)[b.owner]? = some row ∧ b.body ∈ row.upperBounds := by
  rcases owned_view member with ⟨row, lookup, lower | upper⟩
  · rw [((history_invariant history).metadata _ _ _ lookup).2.2] at lower
    cases lower.2
  · exact ⟨upper.1, row, lookup, upper.2⟩

theorem owned_bounded {problem : CoreProblem} {state : CoreState}
    (valid : problem.inputValid = true) (history : UpperInsertionR229.History problem state) :
    ScopedPublication.BoundsBounded (scopeSize state) (ownedBounds state) := by
  intro b member
  have clause : b.clause ∈ physicalBounds state := by
    rw [← owned_clauses]
    exact List.mem_map.mpr ⟨b, member, rfl⟩
  have allocated := physical_allocated valid history clause
  have negative := (owned_upper history member).1
  cases b with
  | mk kind owner side body =>
    cases side with
    | positive => cases negative
    | negative => exact ⟨allocated_bounded history allocated.1,
        allocated_bounded history allocated.2⟩

theorem bound_levels_closed {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) :
    ScopedPublication.BoundLevelsClosed (ownedBounds state) (stateLevels state) := by
  intro b member dependency occurs
  rcases (owned_upper history member).2 with ⟨row, lookup, upper⟩
  rcases stored_upper_closed history lookup upper occurs with
    ⟨_, target, ht, _, le, _⟩
  simpa [stateLevels, lookup, ht] using le

def stateNonGeneric (state : CoreState) : Flags :=
  fun k i => (((state.rows k)[i]?).map CoreRow.nonGeneric).getD false

theorem nonGeneric_false {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) : stateNonGeneric state = fun _ _ => false := by
  funext k i
  cases lookup : (state.rows k)[i]? with
  | none => simp [stateNonGeneric, lookup]
  | some row => simp [stateNonGeneric, lookup,
      ((history_invariant history).metadata _ _ _ lookup).2.1]

def metadata (state : CoreState) : ScopedPublication.Metadata :=
  ⟨stateLevels state, stateNonGeneric state⟩

def captured (state : CoreState) (boundary : Nat) : Flags :=
  ScopedPublication.captureGuard boundary (metadata state)

theorem captured_eq {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) (boundary : Nat) (k : Kind) (i : Nat) :
    captured state boundary k i = decide (boundary < stateLevels state k i) := by
  simp [captured, metadata, ScopedPublication.captureGuard, nonGeneric_false history]

theorem stopped_closed {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) (boundary : Nat) :
    ScopedPublication.StoppedClosed (ownedBounds state) (captured state boundary) := by
  apply ScopedPublication.capture_stopped_closed (bound_levels_closed history)
  intro b member ng
  change stateNonGeneric state b.kind b.owner = true at ng
  rw [nonGeneric_false history] at ng
  cases ng

theorem edge_level {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) {k : Kind} {i j : Nat}
    (found : edge (resolvedBounds state) k i j = true) :
    stateLevels state k j ≤ stateLevels state k i := by
  rw [resolved_eq_physical history, ← owned_clauses] at found
  rcases List.any_eq_true.mp found with ⟨clause, member, found⟩
  rcases List.mem_map.mp member with ⟨b, hb, rfl⟩
  have closed := bound_levels_closed history b hb
  have negative := (owned_upper history hb).1
  cases b with
  | mk kind owner side body =>
    cases side with
    | positive => cases negative
    | negative =>
      cases body <;> try simp [Bound.clause, clauseEdge] at found
      rename_i target
      change decide (kind = k ∧ owner = i ∧ target = j) = true at found
      rcases of_decide_eq_true found with ⟨rfl, rfl, rfl⟩
      exact closed ⟨kind, target⟩ (by simp [ScopedPublication.vars])

theorem reach_level {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) {k : Kind} {i j : Nat}
    (path : BirthLevelSCC.Reach (fun a b => edge (resolvedBounds state) k a b = true) i j) :
    stateLevels state k j ≤ stateLevels state k i := by
  induction path with
  | refl => exact Nat.le_refl _
  | cons first _ ih => exact Nat.le_trans ih (edge_level history first)

theorem connected_levels {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) {k : Kind} {i j : Nat}
    (same : connected (scopeSize state) (resolvedBounds state) k i j = true) :
    stateLevels state k i = stateLevels state k j := by
  have paths := Bool.and_eq_true_iff.mp same
  exact Nat.le_antisymm
    (reach_level history (BirthLevelSCC.finiteReach_sound _ paths.2))
    (reach_level history (BirthLevelSCC.finiteReach_sound _ paths.1))

theorem class_levels_same {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) (k : Kind) (i : Nat) :
    stateLevels state k (physicalClass state k i) = stateLevels state k i := by
  apply Eq.symm
  apply connected_levels history
  simpa only [physicalClass, stateQuotient, resolve_identity history] using
    quotient_connected (scopeSize state) (resolvedBounds state) k i

theorem capture_class_uniform {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) (boundary : Nat) (k : Kind) (i : Nat) :
    captured state boundary k (physicalClass state k i) = captured state boundary k i := by
  simp only [captured_eq history, class_levels_same history]

theorem mapped_bound_levels_closed {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) :
    ScopedPublication.BoundLevelsClosed
      ((ownedBounds state).map (Bound.rename (physicalClass state))) (stateLevels state) := by
  intro mapped member dependency occurs
  rcases List.mem_map.mp member with ⟨b, hb, rfl⟩
  rw [Bound.rename, ScopedPublication.vars_rename] at occurs
  rcases List.mem_map.mp occurs with ⟨r, hr, rfl⟩
  simpa only [Bound.rename, ScopedPublication.Row.rename, class_levels_same history] using
    bound_levels_closed history b hb r hr

theorem mapped_stopped_closed {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) (boundary : Nat) :
    ScopedPublication.StoppedClosed
      ((ownedBounds state).map (Bound.rename (physicalClass state))) (captured state boundary) := by
  apply ScopedPublication.capture_stopped_closed (mapped_bound_levels_closed history)
  intro b member ng
  change stateNonGeneric state b.kind b.owner = true at ng
  rw [nonGeneric_false history] at ng
  cases ng

/-- Root coverage is computed from the complete structural query traversal. -/
def queryRoots {k : Kind} (query : Term k) : List ScopedPublication.Row := ScopedPublication.vars query

theorem query_covered (state : CoreState) (boundary : Nat) {k : Kind} (query : Term k)
    (r : ScopedPublication.Row) (occurs : r ∈ ScopedPublication.vars query) :
    ScopedPublication.Reach (ownedBounds state) (captured state boundary) (queryRoots query) r :=
  .root r occurs

/-- Occurrence-local congruence retains every constructor of the existing Sub. -/
theorem subst_equivalent_vars (ρ σ : Valuation) {k : Kind} (t : Term k)
    (same : ∀ k i, (⟨k, i⟩ : ScopedPublication.Row) ∈ ScopedPublication.vars t →
      Equivalent (ρ k i) (σ k i)) : Equivalent (t.subst ρ) (t.subst σ) := by
  let patched : Valuation := fun k i =>
    if (⟨k, i⟩ : ScopedPublication.Row) ∈ ScopedPublication.vars t then σ k i else ρ k i
  have all : ∀ k i, Equivalent (ρ k i) (patched k i) := by
    intro k i
    by_cases member : (⟨k, i⟩ : ScopedPublication.Row) ∈ ScopedPublication.vars t
    · simpa only [patched, if_pos member] using same k i member
    · simp only [patched, if_neg member]
      exact Equivalent.refl _
  have fixed : t.subst patched = t.subst σ := by
    apply ScopedPublication.subst_congr_vars
    intro k i member
    simp only [patched, if_pos member]
  rw [← fixed]
  exact subst_equivalent ρ patched all t

abbrev PublicationSatisfied (state : CoreState) (boundary : Nat)
    (roots : List ScopedPublication.Row) (uses : List Nat) (ρ : Valuation) : Prop :=
  ScopedPublication.Satisfied (scopeSize state) (ownedBounds state)
    (captured state boundary) (captured state boundary) roots uses ρ

abbrev PublicationReach (state : CoreState) (boundary : Nat)
    (roots : List ScopedPublication.Row) (r : ScopedPublication.Row) : Prop :=
  ScopedPublication.Reach (ownedBounds state) (captured state boundary) roots r

abbrev mappedBounds (state : CoreState) : List Bound :=
  (ownedBounds state).map (Bound.rename (physicalClass state))

abbrev MappedSatisfied (state : CoreState) (boundary : Nat)
    (roots : List ScopedPublication.Row) (uses : List Nat) (ρ : Valuation) : Prop :=
  ScopedPublication.Satisfied (scopeSize state) (mappedBounds state)
    (captured state boundary) (captured state boundary)
    (roots.map (ScopedPublication.Row.rename (physicalClass state))) uses ρ

theorem publication_base {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) {boundary roots uses ρ}
    (solved : PublicationSatisfied state boundary roots uses ρ) :
    (resolvedBounds state).Satisfied ρ := by
  rw [resolved_eq_physical history, ← owned_clauses]
  intro clause member
  rcases List.mem_map.mp member with ⟨b, hb, rfl⟩
  exact solved _ (.base b hb)

theorem edge_bound {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) {k : Kind} {i j : Nat}
    (found : edge (resolvedBounds state) k i j = true) :
    ∃ b, b ∈ ownedBounds state ∧ b.row = (⟨k, i⟩ : ScopedPublication.Row) ∧
      (⟨k, j⟩ : ScopedPublication.Row) ∈ ScopedPublication.vars b.body ∧
      b.clause = ⟨k, .var i, .var j⟩ := by
  rw [resolved_eq_physical history, ← owned_clauses] at found
  rcases List.any_eq_true.mp found with ⟨clause, member, found⟩
  rcases List.mem_map.mp member with ⟨b, hb, rfl⟩
  have negative := (owned_upper history hb).1
  cases b with
  | mk kind owner side body =>
    cases side with
    | positive => cases negative
    | negative =>
      cases body <;> try simp [Bound.clause, clauseEdge] at found
      rename_i target
      change decide (kind = k ∧ owner = i ∧ target = j) = true at found
      rcases of_decide_eq_true found with ⟨rfl, rfl, rfl⟩
      exact ⟨⟨kind, owner, .negative, .var target⟩, hb, rfl, by simp [ScopedPublication.vars], rfl⟩

theorem capture_backward {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) {boundary k i j}
    (path : BirthLevelSCC.Reach (fun a b => edge (resolvedBounds state) k a b = true) i j)
    (active : captured state boundary k j = true) : captured state boundary k i = true := by
  rw [captured_eq history] at active ⊢
  exact decide_eq_true (Nat.lt_of_lt_of_le (of_decide_eq_true active) (reach_level history path))

/-- Every edge of the path is supplied by an actual owner copy. A path to an
active endpoint cannot pass through a stopped owner, by the derived closure. -/
theorem path_publication {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) {boundary roots uses ρ use}
    (solved : PublicationSatisfied state boundary roots uses ρ) (hu : use ∈ uses)
    {k i j}
    (path : BirthLevelSCC.Reach (fun a b => edge (resolvedBounds state) k a b = true) i j) :
    PublicationReach state boundary roots ⟨k, i⟩ → captured state boundary k j = true →
    PublicationReach state boundary roots ⟨k, j⟩ ∧
      Sub (ρ k (ScopedPublication.fresh (scopeSize state) (captured state boundary) use k i))
        (ρ k (ScopedPublication.fresh (scopeSize state) (captured state boundary) use k j)) := by
  induction path with
  | refl => intro reach _; exact ⟨reach, .refl _⟩
  | @cons i middle j first rest ih =>
    intro reach active
    have ownerActive := capture_backward history (.cons first rest) active
    have middleActive := capture_backward history rest active
    rcases edge_bound history first with ⟨b, hb, row, dep, clause⟩
    have ownerReach : PublicationReach state boundary roots b.row := by simpa only [row] using reach
    have guard : b.row.active (captured state boundary) = true := by
      simpa only [row, ScopedPublication.Row.active] using ownerActive
    have next : PublicationReach state boundary roots ⟨k, middle⟩ :=
      .step b hb ownerReach guard _ dep
    have copied := solved _ (.copy b hb use hu ownerReach guard)
    rw [clause] at copied
    have firstSub : Sub
        (ρ k (ScopedPublication.fresh (scopeSize state) (captured state boundary) use k i))
        (ρ k (ScopedPublication.fresh (scopeSize state) (captured state boundary) use k middle)) := by
      simpa only [Constraint.rename, Constraint.Satisfied, Term.rename, Term.subst] using copied
    have tail := ih next active
    exact ⟨tail.1, .trans firstSub tail.2⟩

theorem physicalClass_eq {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) :
    physicalClass state = quotient (scopeSize state) (resolvedBounds state) := by
  funext k i
  simp only [physicalClass, stateQuotient, resolve_identity history]

theorem class_connected {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) (k : Kind) (i : Nat) :
    connected (scopeSize state) (resolvedBounds state) k i (physicalClass state k i) = true := by
  rw [physicalClass_eq history]
  exact quotient_connected _ _ _ _

/-- This also covers future coordinates: the total quotient fixes them. -/
theorem equal_classes_connected {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) {k : Kind} {i j : Nat}
    (same : physicalClass state k i = physicalClass state k j) :
    connected (scopeSize state) (resolvedBounds state) k i j = true := by
  rw [physicalClass_eq history] at same
  by_cases hi : i < scopeSize state <;> by_cases hj : j < scopeSize state
  · exact (quotient_eq_iff hi hj).mp same
  · rw [quotient_future (Nat.le_of_not_gt hj)] at same
    have inside := quotient_in_scope (store := resolvedBounds state) (k := k) hi
    omega
  · rw [quotient_future (Nat.le_of_not_gt hi)] at same
    have inside := quotient_in_scope (store := resolvedBounds state) (k := k) hj
    omega
  · rw [quotient_future (Nat.le_of_not_gt hi), quotient_future (Nat.le_of_not_gt hj)] at same
    subst j
    exact connected_refl _ _ _ _

theorem reachable_class_factorization {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) {boundary roots uses ρ use}
    (solved : PublicationSatisfied state boundary roots uses ρ) (hu : use ∈ uses)
    {k i} (reach : PublicationReach state boundary roots ⟨k, i⟩) :
    Equivalent
      (ρ k (ScopedPublication.fresh (scopeSize state) (captured state boundary) use k i))
      (ρ k (ScopedPublication.fresh (scopeSize state) (captured state boundary) use k
        (physicalClass state k i))) := by
  have paths := Bool.and_eq_true_iff.mp (class_connected history k i)
  have forward := BirthLevelSCC.finiteReach_sound _ paths.1
  have backward := BirthLevelSCC.finiteReach_sound _ paths.2
  cases active : captured state boundary k i with
  | false =>
    have inactive : captured state boundary k (physicalClass state k i) = false := by
      rw [capture_class_uniform history, active]
    rw [ScopedPublication.fresh_inactive active, ScopedPublication.fresh_inactive inactive]
    exact connected_solution (publication_base history solved) (class_connected history k i)
  | true =>
    have targetActive : captured state boundary k (physicalClass state k i) = true := by
      rw [capture_class_uniform history, active]
    have first := path_publication history solved hu forward reach targetActive
    exact ⟨first.2, (path_publication history solved hu backward first.1 active).2⟩

/-- One original publication solution factors the full query at every requested
use. Inactive anchors use the SAME base valuation across all those uses. -/
theorem query_factorization {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) {boundary uses ρ}
    {k : Kind} (query : Term k)
    (solved : PublicationSatisfied state boundary (queryRoots query) uses ρ)
    (use : Nat) (hu : use ∈ uses) :
    Equivalent
      ((query.rename (ScopedPublication.fresh (scopeSize state) (captured state boundary) use)).subst ρ)
      (((query.rename (physicalClass state)).rename
        (ScopedPublication.fresh (scopeSize state) (captured state boundary) use)).subst ρ) := by
  simp only [Term.rename_subst]
  apply subst_equivalent_vars
  intro k i member
  exact reachable_class_factorization history solved hu (query_covered state boundary query _ member)

theorem reach_same_class {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) {boundary roots uses ρ use}
    (solved : PublicationSatisfied state boundary roots uses ρ) (hu : use ∈ uses)
    {k i j} (reach : PublicationReach state boundary roots ⟨k, i⟩)
    (same : physicalClass state k i = physicalClass state k j)
    (active : captured state boundary k j = true) :
    PublicationReach state boundary roots ⟨k, j⟩ := by
  have path := BirthLevelSCC.finiteReach_sound _
    (Bool.and_eq_true_iff.mp (equal_classes_connected history same)).1
  exact (path_publication history solved hu path reach active).1

/-- Quotient reachability is lifted through actual SCC paths of owners. No
publication-equivalence or root-coverage premise is supplied. -/
theorem mapped_reach_lift {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) {boundary roots uses ρ use}
    (solved : PublicationSatisfied state boundary roots uses ρ) (hu : use ∈ uses)
    {r : ScopedPublication.Row}
    (reach : ScopedPublication.Reach (mappedBounds state) (captured state boundary)
      (roots.map (ScopedPublication.Row.rename (physicalClass state))) r) :
    ∃ original, PublicationReach state boundary roots original ∧
      original.rename (physicalClass state) = r := by
  induction reach with
  | root r member =>
    rcases List.mem_map.mp member with ⟨original, hm, rfl⟩
    exact ⟨original, .root original hm, rfl⟩
  | step mapped member prior active r dependency ih =>
    rcases List.mem_map.mp member with ⟨b, hb, rfl⟩
    rcases ih with ⟨⟨kind, index⟩, reached, same⟩
    have kindEq : kind = b.kind := congrArg ScopedPublication.Row.kind same
    subst kind
    have sameIndex : physicalClass state b.kind index = physicalClass state b.kind b.owner :=
      congrArg ScopedPublication.Row.index same
    have ownerActive : captured state boundary b.kind b.owner = true := by
      change captured state boundary b.kind (physicalClass state b.kind b.owner) = true at active
      rwa [capture_class_uniform history] at active
    have ownerReach : PublicationReach state boundary roots b.row :=
      reach_same_class history solved hu reached sameIndex ownerActive
    rw [Bound.rename, ScopedPublication.vars_rename] at dependency
    rcases List.mem_map.mp dependency with ⟨original, hm, rfl⟩
    exact ⟨original, .step b hb ownerReach ownerActive original hm, rfl⟩

theorem mapped_owner_reach {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) {boundary roots uses ρ use}
    (solved : PublicationSatisfied state boundary roots uses ρ) (hu : use ∈ uses)
    (b : Bound)
    (reach : ScopedPublication.Reach (mappedBounds state) (captured state boundary)
      (roots.map (ScopedPublication.Row.rename (physicalClass state))) (b.rename (physicalClass state)).row)
    (active : (b.rename (physicalClass state)).row.active (captured state boundary) = true) :
    PublicationReach state boundary roots b.row ∧ b.row.active (captured state boundary) = true := by
  rcases mapped_reach_lift history solved hu reach with ⟨⟨kind, index⟩, reached, same⟩
  have kindEq : kind = b.kind := congrArg ScopedPublication.Row.kind same
  subst kind
  have sameIndex : physicalClass state b.kind index = physicalClass state b.kind b.owner :=
    congrArg ScopedPublication.Row.index same
  have ownerActive : captured state boundary b.kind b.owner = true := by
    change captured state boundary b.kind (physicalClass state b.kind b.owner) = true at active
    rwa [capture_class_uniform history] at active
  exact ⟨reach_same_class history solved hu reached sameIndex ownerActive, ownerActive⟩

theorem reached_term_factorization {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) {boundary roots uses ρ use}
    (solved : PublicationSatisfied state boundary roots uses ρ) (hu : use ∈ uses)
    {k : Kind} (term : Term k)
    (covered : ∀ r, r ∈ ScopedPublication.vars term → PublicationReach state boundary roots r) :
    Equivalent
      ((term.rename (ScopedPublication.fresh (scopeSize state) (captured state boundary) use)).subst ρ)
      (((term.rename (physicalClass state)).rename
        (ScopedPublication.fresh (scopeSize state) (captured state boundary) use)).subst ρ) := by
  simp only [Term.rename_subst]
  apply subst_equivalent_vars
  intro k i member
  exact reachable_class_factorization history solved hu (covered _ member)

theorem bound_clause_covered {state : CoreState} {boundary roots} (b : Bound)
    (member : b ∈ ownedBounds state) (reach : PublicationReach state boundary roots b.row)
    (active : b.row.active (captured state boundary) = true) :
    (∀ r, r ∈ ScopedPublication.vars b.clause.lower → PublicationReach state boundary roots r) ∧
    (∀ r, r ∈ ScopedPublication.vars b.clause.upper → PublicationReach state boundary roots r) := by
  have owner : ∀ r, r ∈ ScopedPublication.vars (Term.var b.owner : Term b.kind) →
      PublicationReach state boundary roots r := by
    intro r member
    have same : r = b.row := by simpa [ScopedPublication.vars, Bound.row] using member
    exact same ▸ reach
  have body : ∀ r, r ∈ ScopedPublication.vars b.body → PublicationReach state boundary roots r :=
    fun r dependency => .step b member reach active r dependency
  cases b with
  | mk kind index side term =>
    cases side with
    | positive => exact ⟨body, owner⟩
    | negative => exact ⟨owner, body⟩

/-- The same original valuation satisfies the actual quotient publication;
owner copies are recovered from reached SCC members, not full-store copying. -/
theorem publication_pushforward {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) {boundary roots uses ρ}
    (solved : PublicationSatisfied state boundary roots uses ρ) :
    MappedSatisfied state boundary roots uses ρ := by
  intro clause published
  cases published with
  | base mapped member =>
    rcases List.mem_map.mp member with ⟨b, hb, rfl⟩
    rw [Bound.rename_clause]
    change (b.clause.rename (physicalClass state)).Satisfied ρ
    have base := publication_base history solved
    have lower := all_term_factorization (scopeSize state) (resolvedBounds state) ρ base b.clause.lower
    have upper := all_term_factorization (scopeSize state) (resolvedBounds state) ρ base b.clause.upper
    have original := solved _ (.base b hb)
    rw [← physicalClass_eq history] at lower upper
    simpa only [Bound.rename_clause, Constraint.rename, Constraint.Satisfied, Term.rename_subst] using
      (Sub.trans lower.2 (Sub.trans original upper.1))
  | copy mapped member use hu reach active =>
    rcases List.mem_map.mp member with ⟨b, hb, rfl⟩
    rw [Bound.rename_clause]
    change ((b.clause.rename (physicalClass state)).rename
      (ScopedPublication.fresh (scopeSize state) (captured state boundary) use)).Satisfied ρ
    have actual := mapped_owner_reach history solved hu b reach active
    have coverage := bound_clause_covered b hb actual.1 actual.2
    have lower := reached_term_factorization history solved hu b.clause.lower coverage.1
    have upper := reached_term_factorization history solved hu b.clause.upper coverage.2
    have original := solved _ (.copy b hb use hu actual.1 actual.2)
    simpa only [Bound.rename_clause, Constraint.rename, Constraint.Satisfied, Term.rename_subst] using
      (Sub.trans lower.2 (Sub.trans original upper.1))

/-- This is R223's exact named normalized base, with its own reflexive filter.
It is not a syntactic equality with the copied publication relation. -/
theorem mapped_normalized_base {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) {boundary roots uses ρ}
    (solved : MappedSatisfied state boundary roots uses ρ) :
    (normalizedBounds state).Satisfied ρ := by
  apply (normalized_solution_iff (scopeSize state) (resolvedBounds state) ρ).mpr
  rw [← physicalClass_eq history]
  intro clause member
  rw [resolved_eq_physical history, ← owned_clauses] at member
  rcases List.mem_map.mp member with ⟨b, hb, rfl⟩
  have mapped := solved _ (.base (b.rename (physicalClass state)) (List.mem_map.mpr ⟨b, hb, rfl⟩))
  rw [Bound.rename_clause] at mapped
  exact (Constraint.rename_satisfied _ ρ b.clause).mp mapped

/-- One finite allocation bound is computed from the requested use identities. -/
def useCount (uses : List Nat) : Nat := uses.foldr Nat.max 0 + 1

theorem use_lt_count {uses : List Nat} {use : Nat} (member : use ∈ uses) : use < useCount uses := by
  induction uses with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | later
    · exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (ih later) (Nat.succ_le_succ (Nat.le_max_right _ _))

def pullback (state : CoreState) (boundary : Nat) (uses : List Nat) (ρ : Valuation) : Valuation :=
  fun k i => ρ k (Generalization.transport (scopeSize state) (useCount uses) 0
    (ScopedPublication.guardLevels (captured state boundary)) (physicalClass state) k i)

/-- The reverse direction derives inactive images and stopped closure from
history. All use blocks and all inactive anchors share one pulled valuation. -/
theorem publication_pullback {problem : CoreProblem} {state : CoreState}
    (valid : problem.inputValid = true) (history : UpperInsertionR229.History problem state)
    {boundary roots uses ρ} (solved : MappedSatisfied state boundary roots uses ρ) :
    PublicationSatisfied state boundary roots uses (pullback state boundary uses ρ) := by
  apply ScopedPublication.publication_solution_pullback (owned_bounded valid history)
    (q := physicalClass state) (count := useCount uses) (ρ := ρ)
  · intro k i _ inactive
    rwa [capture_class_uniform history]
  · exact mapped_stopped_closed history boundary
  · exact fun _ _ inactive => inactive
  · exact fun _ member => use_lt_count member
  · exact solved

/-- The shared pulled valuation fixes each inactive allocated anchor up to the
existing base SCC equivalence, uniformly over every requested fresh use. -/
theorem pullback_query {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) {boundary uses ρ}
    {k : Kind} (query : Term k) (allocated : problem.termAllocated query = true)
    (use : Nat) (hu : use ∈ uses) :
    ((query.rename (ScopedPublication.fresh (scopeSize state) (captured state boundary) use)).subst
      (pullback state boundary uses ρ)) =
    (((query.rename (physicalClass state)).rename
      (ScopedPublication.fresh (scopeSize state) (captured state boundary) use)).subst ρ) := by
  apply Generalization.fresh_term_pullback
  · apply ScopedPublication.guard_anchors
    intro k i _ inactive
    rwa [capture_class_uniform history]
  · exact use_lt_count hu
  · exact allocated_bounded history ((term_allocated_iff problem query).mp allocated)

/-- Constructive result on the computed query roots: the SAME valuation works
for every normalized use and both directions of structural Sub factorization. -/
theorem operational_publication_factorization {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) {boundary uses ρ}
    {k : Kind} (query : Term k)
    (solved : PublicationSatisfied state boundary (queryRoots query) uses ρ) :
    ∃ σ : Valuation, σ = ρ ∧
      MappedSatisfied state boundary (queryRoots query) uses σ ∧
      (normalizedBounds state).Satisfied σ ∧
      ∀ use, use ∈ uses → Equivalent
        ((query.rename (ScopedPublication.fresh (scopeSize state) (captured state boundary) use)).subst ρ)
        (((query.rename (physicalClass state)).rename
          (ScopedPublication.fresh (scopeSize state) (captured state boundary) use)).subst σ) := by
  have mapped := publication_pushforward history solved
  exact ⟨ρ, rfl, mapped, mapped_normalized_base history mapped,
    fun use hu => query_factorization history query solved use hu⟩

theorem class_minimum_level {problem : CoreProblem} {state : CoreState}
    (history : UpperInsertionR229.History problem state) {k : Kind} {i : Nat}
    (inside : i < scopeSize state) :
    classLevels state k (physicalClass state k i) = stateLevels state k i := by
  have canonical : Generalization.Canonical (scopeSize state) (physicalClass state) := by
    rw [physicalClass_eq history]
    exact quotient_canonical _ _
  have minimum := actual_class_minimum_at_fixed state k (physicalClass state k i)
    (canonical.1 k i inside) (canonical.2 k i inside)
  apply Nat.le_antisymm (minimum.1 i inside rfl)
  apply minimum.2
  intro j _ same
  have levelEq : stateLevels state k j = stateLevels state k i :=
    (class_levels_same history k j).symm.trans
      ((congrArg (stateLevels state k) same).trans (class_levels_same history k i))
  exact Nat.le_of_eq levelEq.symm

theorem use_guard_same_snapshot (state : CoreState) (boundary : Nat) :
    ScopedPublication.useGuard (captured state boundary) boundary (metadata state) =
      captured state boundary := by
  funext k i
  simp [ScopedPublication.useGuard, captured]

theorem normalized_roots_computed (state : CoreState) {k : Kind} (query : Term k) :
    (queryRoots query).map (ScopedPublication.Row.rename (physicalClass state)) =
      queryRoots (query.rename (physicalClass state)) :=
  (ScopedPublication.vars_rename _ _).symm

/-- A constructive diagonal interpretation of all independent copy blocks.
Only the original allocated coordinates are promised to remain literally fixed. -/
def diagonal (n : Nat) (ρ : Valuation) : Valuation :=
  fun k i => if i < n then ρ k i else ρ k ((i - n) % n)

theorem diagonal_anchor {n ρ k i} (inside : i < n) : diagonal n ρ k i = ρ k i := by
  simp [diagonal, inside]

theorem diagonal_fresh {n ρ flags use k i} (inside : i < n) :
    diagonal n ρ k (ScopedPublication.fresh n flags use k i) = ρ k i := by
  cases active : flags k i with
  | false => rw [ScopedPublication.fresh_inactive active, diagonal_anchor inside]
  | true =>
    rw [ScopedPublication.fresh_active active]
    simp only [diagonal, Nat.not_lt.mpr (Generalization.copyIndex_ge n use i), if_false,
      Generalization.copyIndex_row inside]

theorem diagonal_base_term {n ρ k} {term : Term k} (bounded : Generalization.Bounded n term) :
    term.subst (diagonal n ρ) = term.subst ρ :=
  Generalization.subst_congr_on n _ _ (fun _ _ inside => diagonal_anchor inside) bounded

theorem diagonal_fresh_term {n ρ flags use k} {term : Term k}
    (bounded : Generalization.Bounded n term) :
    (term.rename (ScopedPublication.fresh n flags use)).subst (diagonal n ρ) = term.subst ρ := by
  rw [Term.rename_subst]
  exact Generalization.subst_congr_on n _ _ (fun _ _ inside => diagonal_fresh inside) bounded

/-- No shared publication valuation is assumed: one is constructed from any
base solution and works simultaneously for every requested copy. -/
theorem publication_diagonal {problem : CoreProblem} {state : CoreState}
    (valid : problem.inputValid = true) (history : UpperInsertionR229.History problem state)
    {boundary roots uses ρ} (base : (physicalBounds state).Satisfied ρ) :
    PublicationSatisfied state boundary roots uses (diagonal (scopeSize state) ρ) := by
  intro clause published
  cases published with
  | base b member =>
    have bounded := b.clause_bounded (owned_bounded valid history b member)
    have old := base b.clause (by rw [← owned_clauses]; exact List.mem_map.mpr ⟨b, member, rfl⟩)
    change Sub (b.clause.lower.subst (diagonal (scopeSize state) ρ))
      (b.clause.upper.subst (diagonal (scopeSize state) ρ))
    rw [diagonal_base_term bounded.1, diagonal_base_term bounded.2]
    exact old
  | copy b member use hu reach active =>
    have bounded := b.clause_bounded (owned_bounded valid history b member)
    have old := base b.clause (by rw [← owned_clauses]; exact List.mem_map.mpr ⟨b, member, rfl⟩)
    change Sub
      ((b.clause.lower.rename (ScopedPublication.fresh (scopeSize state) (captured state boundary) use)).subst
        (diagonal (scopeSize state) ρ))
      ((b.clause.upper.rename (ScopedPublication.fresh (scopeSize state) (captured state boundary) use)).subst
        (diagonal (scopeSize state) ρ))
    rw [diagonal_fresh_term bounded.1, diagonal_fresh_term bounded.2]
    exact old

/-- Apply the construction to the original constraint list conserved at a
terminal R229 history, preserving the original query valuation at every use. -/
theorem terminal_solution_factorization {problem : CoreProblem} {state : CoreState}
    (valid : problem.inputValid = true) (history : UpperInsertionR229.History problem state)
    (terminal : state.pending = []) {boundary uses ρ} {k : Kind} (query : Term k)
    (allocated : problem.termAllocated query = true)
    (solved : problem.originalConstraints.Satisfied ρ) :
    ∃ σ : Valuation,
      MappedSatisfied state boundary (queryRoots query) uses σ ∧
      (normalizedBounds state).Satisfied σ ∧
      (∀ kind i, i < scopeSize state → captured state boundary kind i = false → σ kind i = ρ kind i) ∧
      ∀ use, use ∈ uses → Equivalent (query.subst ρ)
        (((query.rename (physicalClass state)).rename
          (ScopedPublication.fresh (scopeSize state) (captured state boundary) use)).subst σ) := by
  have base : (physicalBounds state).Satisfied ρ := by
    intro clause member
    exact solved clause ((terminal_store history terminal).1.mem_iff.mp member)
  have published : PublicationSatisfied state boundary (queryRoots query) uses
      (diagonal (scopeSize state) ρ) := publication_diagonal valid history base
  have mapped := publication_pushforward history published
  refine ⟨diagonal (scopeSize state) ρ, mapped, mapped_normalized_base history mapped,
    (fun _ _ inside _ => diagonal_anchor inside), ?_⟩
  intro use hu
  have factor := query_factorization history query published use hu
  rw [diagonal_fresh_term (allocated_bounded history ((term_allocated_iff problem query).mp allocated))] at factor
  exact factor

theorem terminal_publication_pullback {problem : CoreProblem} {state : CoreState}
    (valid : problem.inputValid = true) (history : UpperInsertionR229.History problem state)
    (terminal : state.pending = []) {boundary roots uses ρ}
    (solved : MappedSatisfied state boundary roots uses ρ) :
    PublicationSatisfied state boundary roots uses (pullback state boundary uses ρ) ∧
      problem.originalConstraints.Satisfied (pullback state boundary uses ρ) := by
  have published := publication_pullback valid history solved
  refine ⟨published, ?_⟩
  have base := publication_base history published
  intro clause member
  exact base clause ((terminal_store history terminal).2.mem_iff.mpr member)

theorem self_upper_history : UpperInsertionR229.History selfUpperProblem selfUpperState :=
  .step .initial self_upper_actual.2

theorem upper_only_history : UpperInsertionR229.History AbstractCore.upperOnlyProblem upperOnlyState :=
  .step .initial upper_only_actual_and_preserved.1

/-- Actual self-cycle application: no arbitrary physical-state certificate. -/
theorem self_upper_application {boundary uses ρ} {k : Kind} (query : Term k)
    (allocated : selfUpperProblem.termAllocated query = true)
    (solved : selfUpperProblem.originalConstraints.Satisfied ρ) :
    normalizedBounds selfUpperState = [] ∧
    ∃ σ : Valuation, MappedSatisfied selfUpperState boundary (queryRoots query) uses σ ∧
      (normalizedBounds selfUpperState).Satisfied σ ∧
      (∀ kind i, i < scopeSize selfUpperState → captured selfUpperState boundary kind i = false → σ kind i = ρ kind i) ∧
      ∀ use, use ∈ uses → Equivalent (query.subst ρ)
        (((query.rename (physicalClass selfUpperState)).rename
          (ScopedPublication.fresh (scopeSize selfUpperState) (captured selfUpperState boundary) use)).subst σ) := by
  exact ⟨self_upper_quotient_free.2.2,
    terminal_solution_factorization self_upper_actual.1 self_upper_history rfl query allocated solved⟩

/-- Actual upper-only application retains the external atom constraint. -/
theorem upper_only_application {boundary uses ρ} {k : Kind} (query : Term k)
    (allocated : AbstractCore.upperOnlyProblem.termAllocated query = true)
    (solved : AbstractCore.upperOnlyProblem.originalConstraints.Satisfied ρ) :
    normalizedBounds upperOnlyState = [⟨.value, .var 0, .atom 0⟩] ∧
    ∃ σ : Valuation, MappedSatisfied upperOnlyState boundary (queryRoots query) uses σ ∧
      (normalizedBounds upperOnlyState).Satisfied σ ∧
      (∀ kind i, i < scopeSize upperOnlyState → captured upperOnlyState boundary kind i = false → σ kind i = ρ kind i) ∧
      ∀ use, use ∈ uses → Equivalent (query.subst ρ)
        (((query.rename (physicalClass upperOnlyState)).rename
          (ScopedPublication.fresh (scopeSize upperOnlyState) (captured upperOnlyState boundary) use)).subst σ) := by
  exact ⟨upper_only_actual_and_preserved.2,
    terminal_solution_factorization (by rfl) upper_only_history rfl query allocated solved⟩

end YulangClosure.SimpleSub.UpperPublicationR230

/-! Complete authored-theorem audit surface. Execution belongs to Luna. -/

#check @YulangClosure.SimpleSub.UpperPublicationR230.owned_clauses
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.owned_clauses

#check @YulangClosure.SimpleSub.UpperPublicationR230.owned_view
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.owned_view

#check @YulangClosure.SimpleSub.UpperPublicationR230.owned_upper
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.owned_upper

#check @YulangClosure.SimpleSub.UpperPublicationR230.owned_bounded
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.owned_bounded

#check @YulangClosure.SimpleSub.UpperPublicationR230.bound_levels_closed
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.bound_levels_closed

#check @YulangClosure.SimpleSub.UpperPublicationR230.nonGeneric_false
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.nonGeneric_false

#check @YulangClosure.SimpleSub.UpperPublicationR230.captured_eq
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.captured_eq

#check @YulangClosure.SimpleSub.UpperPublicationR230.stopped_closed
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.stopped_closed

#check @YulangClosure.SimpleSub.UpperPublicationR230.edge_level
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.edge_level

#check @YulangClosure.SimpleSub.UpperPublicationR230.reach_level
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.reach_level

#check @YulangClosure.SimpleSub.UpperPublicationR230.connected_levels
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.connected_levels

#check @YulangClosure.SimpleSub.UpperPublicationR230.class_levels_same
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.class_levels_same

#check @YulangClosure.SimpleSub.UpperPublicationR230.capture_class_uniform
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.capture_class_uniform

#check @YulangClosure.SimpleSub.UpperPublicationR230.mapped_bound_levels_closed
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.mapped_bound_levels_closed

#check @YulangClosure.SimpleSub.UpperPublicationR230.mapped_stopped_closed
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.mapped_stopped_closed

#check @YulangClosure.SimpleSub.UpperPublicationR230.query_covered
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.query_covered

#check @YulangClosure.SimpleSub.UpperPublicationR230.subst_equivalent_vars
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.subst_equivalent_vars

#check @YulangClosure.SimpleSub.UpperPublicationR230.publication_base
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.publication_base

#check @YulangClosure.SimpleSub.UpperPublicationR230.edge_bound
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.edge_bound

#check @YulangClosure.SimpleSub.UpperPublicationR230.capture_backward
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.capture_backward

#check @YulangClosure.SimpleSub.UpperPublicationR230.path_publication
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.path_publication

#check @YulangClosure.SimpleSub.UpperPublicationR230.physicalClass_eq
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.physicalClass_eq

#check @YulangClosure.SimpleSub.UpperPublicationR230.class_connected
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.class_connected

#check @YulangClosure.SimpleSub.UpperPublicationR230.equal_classes_connected
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.equal_classes_connected

#check @YulangClosure.SimpleSub.UpperPublicationR230.reachable_class_factorization
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.reachable_class_factorization

#check @YulangClosure.SimpleSub.UpperPublicationR230.query_factorization
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.query_factorization

#check @YulangClosure.SimpleSub.UpperPublicationR230.reach_same_class
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.reach_same_class

#check @YulangClosure.SimpleSub.UpperPublicationR230.mapped_reach_lift
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.mapped_reach_lift

#check @YulangClosure.SimpleSub.UpperPublicationR230.mapped_owner_reach
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.mapped_owner_reach

#check @YulangClosure.SimpleSub.UpperPublicationR230.reached_term_factorization
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.reached_term_factorization

#check @YulangClosure.SimpleSub.UpperPublicationR230.bound_clause_covered
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.bound_clause_covered

#check @YulangClosure.SimpleSub.UpperPublicationR230.publication_pushforward
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.publication_pushforward

#check @YulangClosure.SimpleSub.UpperPublicationR230.mapped_normalized_base
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.mapped_normalized_base

#check @YulangClosure.SimpleSub.UpperPublicationR230.use_lt_count
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.use_lt_count

#check @YulangClosure.SimpleSub.UpperPublicationR230.publication_pullback
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.publication_pullback

#check @YulangClosure.SimpleSub.UpperPublicationR230.pullback_query
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.pullback_query

#check @YulangClosure.SimpleSub.UpperPublicationR230.operational_publication_factorization
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.operational_publication_factorization

#check @YulangClosure.SimpleSub.UpperPublicationR230.class_minimum_level
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.class_minimum_level

#check @YulangClosure.SimpleSub.UpperPublicationR230.use_guard_same_snapshot
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.use_guard_same_snapshot

#check @YulangClosure.SimpleSub.UpperPublicationR230.normalized_roots_computed
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.normalized_roots_computed

#check @YulangClosure.SimpleSub.UpperPublicationR230.diagonal_anchor
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.diagonal_anchor

#check @YulangClosure.SimpleSub.UpperPublicationR230.diagonal_fresh
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.diagonal_fresh

#check @YulangClosure.SimpleSub.UpperPublicationR230.diagonal_base_term
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.diagonal_base_term

#check @YulangClosure.SimpleSub.UpperPublicationR230.diagonal_fresh_term
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.diagonal_fresh_term

#check @YulangClosure.SimpleSub.UpperPublicationR230.publication_diagonal
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.publication_diagonal

#check @YulangClosure.SimpleSub.UpperPublicationR230.terminal_solution_factorization
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.terminal_solution_factorization

#check @YulangClosure.SimpleSub.UpperPublicationR230.terminal_publication_pullback
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.terminal_publication_pullback

#check @YulangClosure.SimpleSub.UpperPublicationR230.self_upper_history
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.self_upper_history

#check @YulangClosure.SimpleSub.UpperPublicationR230.upper_only_history
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.upper_only_history

#check @YulangClosure.SimpleSub.UpperPublicationR230.self_upper_application
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.self_upper_application

#check @YulangClosure.SimpleSub.UpperPublicationR230.upper_only_application
#print axioms YulangClosure.SimpleSub.UpperPublicationR230.upper_only_application
