import YulangClosure.SimpleSubConstraintSyntax

/-!
Forward solution transport across level-based fresh uses and retained quotients.

This formalizes the finite-use pullback direction of the native level/publication
argument. It does not assume a diagonal lift or principal coverage. A single
valuation transports the complete store, every use, shared anchors, and arbitrary
later client constraints. The numeric block allocation below is an explicit
fresh-name realization; Rust's actual allocation correspondence is separate.
The model copies the complete supplied store. Native reachable-high traversal,
captured-local/non-generic guards, retained bound closure and scope correspondence
must still be supplied before identifying it with actual freshenAbove.
-/
namespace YulangClosure.SimpleSub.Generalization

abbrev Levels := Kind → Nat → Nat

/-- Original rows occupy `[0,n)`; each use reserves a disjoint complete block.
Rows at or below the publication boundary keep their original identity. -/
def freshen (n boundary : Nat) (levels : Levels) (use : Nat) : Renaming :=
  fun k i => if levels k i ≤ boundary then i else n + use * n + i

def copyIndex (n use i : Nat) : Nat := n + use * n + i

@[simp] theorem freshen_anchor {n boundary levels use k i}
    (h : levels k i ≤ boundary) : freshen n boundary levels use k i = i := by
  simp [freshen, h]

@[simp] theorem freshen_eligible {n boundary levels use k i}
    (h : boundary < levels k i) :
    freshen n boundary levels use k i = copyIndex n use i := by
  simp [freshen, copyIndex, Nat.not_le.mpr h]

theorem copyIndex_ge (n use i : Nat) : n ≤ copyIndex n use i := by
  simp only [copyIndex]
  omega

theorem copyIndex_lt {n uses use i : Nat} (hu : use < uses) (hi : i < n) :
    copyIndex n use i < n * (uses + 1) := by
  have hm := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hu)
  simp only [Nat.succ_mul] at hm
  simp only [copyIndex, Nat.mul_add, Nat.mul_one, Nat.mul_comm n uses]
  omega

theorem copyIndex_row {n use i : Nat} (hi : i < n) :
    (copyIndex n use i - n) % n = i := by
  have he : copyIndex n use i - n = use * n + i := by
    simp [copyIndex, Nat.add_assoc]
  rw [he, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hi]

theorem copyIndex_use {n use i : Nat} (hi : i < n) :
    (copyIndex n use i - n) / n = use := by
  have hn : 0 < n := Nat.zero_lt_of_lt hi
  have he : copyIndex n use i - n = i + use * n := by
    unfold copyIndex
    omega
  rw [he, Nat.add_mul_div_right i use hn, Nat.div_eq_of_lt hi]
  simp

theorem copyIndex_injective {n u v i j : Nat} (hi : i < n) (hj : j < n)
    (h : copyIndex n u i = copyIndex n v j) : u = v ∧ i = j := by
  have hu := congrArg (fun x => (x - n) / n) h
  have hr := congrArg (fun x => (x - n) % n) h
  simpa only [copyIndex_use hi, copyIndex_use hj, copyIndex_row hi,
    copyIndex_row hj] using And.intro hu hr

theorem freshen_injective {n boundary levels use k i j}
    (hi : i < n) (hj : j < n)
    (h : freshen n boundary levels use k i = freshen n boundary levels use k j) :
    i = j := by
  by_cases hli : levels k i ≤ boundary <;> by_cases hlj : levels k j ≤ boundary
  · simpa [freshen, hli, hlj] using h
  · simp only [freshen, hli, hlj, ite_true, ite_false] at h
    omega
  · simp only [freshen, hli, hlj, ite_true, ite_false] at h
    omega
  · simp only [freshen, hli, hlj, ite_false] at h
    omega

theorem distinct_uses_disjoint {n boundary levels u v k i j}
    (hi : i < n) (hj : j < n) (hui : boundary < levels k i)
    (hvj : boundary < levels k j) (huv : u ≠ v) :
    freshen n boundary levels u k i ≠ freshen n boundary levels v k j := by
  rw [freshen_eligible hui, freshen_eligible hvj]
  intro h
  exact huv (copyIndex_injective hi hj h).1

/-- All original variables in a type are within the allocated finite scope. -/
def Bounded (n : Nat) {k} : Term k → Prop
  | .var i => i < n
  | .atom _ | .bottom | .top | .recordNil | .tupleNil | .variantNil => True
  | .union a b | .intersection a b => Bounded n a ∧ Bounded n b
  | .function a ae re r => Bounded n a ∧ Bounded n ae ∧ Bounded n re ∧ Bounded n r
  | .recordCons _ _ field tail | .tupleCons field tail | .variantCons _ field tail =>
      Bounded n field ∧ Bounded n tail

theorem subst_congr_on (n : Nat) (ρ σ : Valuation)
    (same : ∀ k i, i < n → ρ k i = σ k i) {k} {t : Term k}
    (bounded : Bounded n t) : t.subst ρ = t.subst σ := by
  induction t <;> simp_all [Bounded, Term.subst]

def ConstraintBounded (n : Nat) (c : Constraint) : Prop :=
  Bounded n c.lower ∧ Bounded n c.upper

def StoreBounded (n : Nat) (store : Store) : Prop :=
  ∀ c, c ∈ store → ConstraintBounded n c

/-- Every clause is copied for every requested use, with both endpoints sharing
the same map. Original constraints are retained too. -/
def usesStore (n boundary : Nat) (levels : Levels) (uses : List Nat) (store : Store) : Store :=
  store ++ uses.flatMap (fun use => store.map (Constraint.rename (freshen n boundary levels use)))

theorem usesStore_satisfied (n boundary : Nat) (levels : Levels)
    (uses : List Nat) (store : Store) (ρ : Valuation) :
    (usesStore n boundary levels uses store).Satisfied ρ ↔
      store.Satisfied ρ ∧ ∀ use, use ∈ uses →
        store.Satisfied (fun k i => ρ k (freshen n boundary levels use k i)) := by
  rw [usesStore, Store.satisfied_append]
  constructor
  · rintro ⟨hbase, huses⟩
    refine ⟨hbase, ?_⟩
    intro use hu
    apply (Store.quotient_pullback _ _ _).mp
    intro c hc
    exact huses c (List.mem_flatMap.mpr ⟨use, hu, hc⟩)
  · rintro ⟨hbase, huses⟩
    refine ⟨hbase, ?_⟩
    intro c hc
    rcases List.mem_flatMap.mp hc with ⟨use, hu, hc⟩
    exact (Store.quotient_pullback _ _ _).mpr (huses use hu) c hc

/-- Quotient transport for one shared finite allocation. Coordinates beyond all
use blocks are later client variables and remain literally fixed. -/
def transport (n count boundary : Nat) (after : Levels) (q : Renaming) : Renaming :=
  fun k i => if i < n then q k i
    else if i < n * (count + 1) then
      freshen n boundary after ((i - n) / n) k (q k ((i - n) % n))
    else i

@[simp] theorem transport_base {n count boundary after q k i} (hi : i < n) :
    transport n count boundary after q k i = q k i := by
  simp [transport, hi]

@[simp] theorem transport_future {n count boundary after q k i}
    (hi : n * (count + 1) ≤ i) : transport n count boundary after q k i = i := by
  have hn : n ≤ n * (count + 1) := by
    simp [Nat.mul_add]
  simp [transport, Nat.not_lt.mpr (Nat.le_trans hn hi), Nat.not_lt.mpr hi]

theorem transport_copy {n count boundary after q use k i}
    (hu : use < count) (hi : i < n) :
    transport n count boundary after q k (copyIndex n use i) =
      freshen n boundary after use k (q k i) := by
  simp only [transport, Nat.not_lt.mpr (copyIndex_ge n use i), ite_false,
    copyIndex_lt hu hi, ite_true, copyIndex_use hi, copyIndex_row hi]

/-- Lower-level captures remain lower-level under the actual row quotient.
This condition does not assert a diagonal lift or preservation of all solutions. -/
def PreservesAnchors (n boundary : Nat) (before after : Levels) (q : Renaming) : Prop :=
  ∀ k i, i < n → before k i ≤ boundary → after k (q k i) ≤ boundary

theorem anchors_of_level_nonincrease {n boundary before after q}
    (lowered : ∀ k i, i < n → after k (q k i) ≤ before k i) :
    PreservesAnchors n boundary before after q := by
  intro k i hi low
  exact Nat.le_trans (lowered k i hi) low

private def lowerLevel (levels : Nat → Nat) (select : Nat → Bool)
    (acc row : Nat) : Nat := if select row then min acc (levels row) else acc

private theorem lowerLevel_fold_le (levels : Nat → Nat) (select : Nat → Bool)
    (rows : List Nat) (acc : Nat) : rows.foldl (lowerLevel levels select) acc ≤ acc := by
  induction rows generalizing acc with
  | nil => exact Nat.le_refl _
  | cons row rest ih =>
    apply Nat.le_trans (ih _)
    simp only [lowerLevel]
    split
    · exact Nat.min_le_left _ _
    · exact Nat.le_refl _

private theorem lowerLevel_fold_member (levels : Nat → Nat) (select : Nat → Bool)
    {rows : List Nat} {row : Nat} (member : row ∈ rows) (selected : select row = true)
    (acc : Nat) : rows.foldl (lowerLevel levels select) acc ≤ levels row := by
  induction rows generalizing acc with
  | nil => cases member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | later
    · apply Nat.le_trans (lowerLevel_fold_le levels select rest _)
      simpa only [lowerLevel, selected, ite_true] using Nat.min_le_right acc (levels row)
    · exact ih later (lowerLevel levels select acc head)

/-- A seeded lower envelope for an arbitrary row map. For in-scope canonical
representatives it is the exact finite fiber minimum, proved below. Neither
interpretation establishes closure of stored bounds at the resulting levels. -/
def quotientLevels (n : Nat) (before : Levels) (q : Renaming) : Levels :=
  fun k representative => (List.range n).foldl
    (lowerLevel (before k) (fun i => decide (q k i = representative)))
    (before k representative)

theorem quotientLevels_le {n before q k i} (hi : i < n) :
    quotientLevels n before q k (q k i) ≤ before k i := by
  exact lowerLevel_fold_member (before k) (fun j => decide (q k j = q k i))
    (List.mem_range.mpr hi) (by simp) _

theorem quotientLevels_preserve_anchors (n boundary : Nat) (before : Levels) (q : Renaming) :
    PreservesAnchors n boundary before (quotientLevels n before q) q := by
  apply anchors_of_level_nonincrease
  intro k i hi
  exact quotientLevels_le hi

/-- Actual canonical representatives stay in the allocated original row scope
and are fixed by canonicalization. An arbitrary renaming need not satisfy this. -/
def Canonical (n : Nat) (q : Renaming) : Prop :=
  (∀ k i, i < n → q k i < n) ∧ (∀ k i, i < n → q k (q k i) = q k i)

private theorem lowerLevel_fold_lower_bound (levels : Nat → Nat) (select : Nat → Bool)
    (rows : List Nat) (bound acc : Nat) (initial : bound ≤ acc)
    (allRows : ∀ row, row ∈ rows → select row = true → bound ≤ levels row) :
    bound ≤ rows.foldl (lowerLevel levels select) acc := by
  induction rows generalizing acc with
  | nil => exact initial
  | cons head rest ih =>
    apply ih
    · unfold lowerLevel
      split
      · rename_i selected
        exact Nat.le_min.mpr ⟨initial, allRows head List.mem_cons_self selected⟩
      · exact initial
    · intro row member selected
      exact allRows row (List.mem_cons_of_mem _ member) selected

def FiberMinimum (n : Nat) (before : Levels) (q : Renaming)
    (k : Kind) (representative minimum : Nat) : Prop :=
  (∀ i, i < n → q k i = representative → minimum ≤ before k i) ∧
    ∀ bound, (∀ i, i < n → q k i = representative → bound ≤ before k i) → bound ≤ minimum

theorem quotientLevels_is_minimum {n before q k representative}
    (inScope : representative < n) (fixed : q k representative = representative) :
    FiberMinimum n before q k representative (quotientLevels n before q k representative) := by
  constructor
  · intro i hi same
    simpa only [same] using (quotientLevels_le (before := before) (q := q) (k := k) hi)
  · intro bound lower
    apply lowerLevel_fold_lower_bound
    · exact lower representative inScope fixed
    · intro row member selected
      exact lower row (List.mem_range.mp member) (by simpa using selected)

theorem canonical_quotient_minimum {n before q} (canonical : Canonical n q)
    (k : Kind) (i : Nat) (hi : i < n) :
    FiberMinimum n before q k (q k i) (quotientLevels n before q k (q k i)) :=
  quotientLevels_is_minimum (canonical.1 k i hi) (canonical.2 k i hi)

theorem canonical_post_use_bounded {n count boundary after q use k i}
    (canonical : Canonical n q) (hu : use < count) (hi : i < n) :
    freshen n boundary after use k (q k i) < n * (count + 1) := by
  have hq := canonical.1 k i hi
  by_cases low : after k (q k i) ≤ boundary
  · rw [freshen_anchor low]
    have hn : n ≤ n * (count + 1) := by simp [Nat.mul_add]
    exact Nat.lt_of_lt_of_le hq hn
  · rw [freshen_eligible (Nat.lt_of_not_ge low)]
    exact copyIndex_lt hu hq

theorem canonical_post_uses_disjoint {n boundary after q u v k i j}
    (canonical : Canonical n q) (hi : i < n) (hj : j < n)
    (eligibleI : boundary < after k (q k i)) (eligibleJ : boundary < after k (q k j))
    (different : u ≠ v) :
    freshen n boundary after u k (q k i) ≠ freshen n boundary after v k (q k j) :=
  distinct_uses_disjoint (canonical.1 k i hi) (canonical.1 k j hj) eligibleI eligibleJ different

theorem transport_freshen {n count boundary before after q use k i}
    (anchors : PreservesAnchors n boundary before after q)
    (hu : use < count) (hi : i < n) :
    transport n count boundary after q k (freshen n boundary before use k i) =
      freshen n boundary after use k (q k i) := by
  by_cases low : before k i ≤ boundary
  · rw [freshen_anchor low, transport_base hi,
      freshen_anchor (anchors k i hi low)]
  · rw [freshen_eligible (Nat.lt_of_not_ge low)]
    exact transport_copy hu hi

theorem base_term_pullback {n count boundary after q k} {t : Term k}
    (bounded : Bounded n t) (ρ : Valuation) :
    t.subst (fun k i => ρ k (transport n count boundary after q k i)) =
      (t.rename q).subst ρ := by
  rw [Term.rename_subst]
  apply subst_congr_on n _ _ _ bounded
  intro k i hi
  rw [transport_base hi]

theorem fresh_term_pullback {n count boundary before after q use k} {t : Term k}
    (anchors : PreservesAnchors n boundary before after q)
    (hu : use < count) (bounded : Bounded n t) (ρ : Valuation) :
    (t.rename (freshen n boundary before use)).subst
        (fun k i => ρ k (transport n count boundary after q k i)) =
      ((t.rename q).rename (freshen n boundary after use)).subst ρ := by
  simp only [Term.rename_subst]
  apply subst_congr_on n _ _ _ bounded
  intro k i hi
  rw [transport_freshen anchors hu hi]

/-- One pulled-back valuation satisfies the entire pre-quotient store and all
finite independent uses. No per-clause or per-use witness is chosen. -/
theorem quotient_uses_sound {n count boundary before after q uses store}
    (bounded : StoreBounded n store)
    (anchors : PreservesAnchors n boundary before after q)
    (useBounds : ∀ use, use ∈ uses → use < count)
    (ρ : Valuation)
    (solved : (usesStore n boundary after uses (store.map (Constraint.rename q))).Satisfied ρ) :
    (usesStore n boundary before uses store).Satisfied
      (fun k i => ρ k (transport n count boundary after q k i)) := by
  rw [usesStore_satisfied] at solved ⊢
  constructor
  · intro c hc
    have h := solved.1 (c.rename q) (List.mem_map.mpr ⟨c, hc, rfl⟩)
    have hb := bounded c hc
    simpa only [Constraint.Satisfied, Constraint.rename,
      base_term_pullback hb.1, base_term_pullback hb.2] using h
  · intro use hu c hc
    have h := solved.2 use hu (c.rename q) (List.mem_map.mpr ⟨c, hc, rfl⟩)
    have hb := bounded c hc
    change Sub
      (c.lower.subst (fun k i => ρ k (transport n count boundary after q k
        (freshen n boundary before use k i))))
      (c.upper.subst (fun k i => ρ k (transport n count boundary after q k
        (freshen n boundary before use k i))))
    have lower := fresh_term_pullback anchors (useBounds use hu) hb.1 ρ
    have upper := fresh_term_pullback anchors (useBounds use hu) hb.2 ρ
    simp only [Term.rename_subst] at lower upper
    rw [lower, upper]
    simpa only [Constraint.Satisfied, Constraint.rename, Term.rename_subst] using h

/-- Arbitrary later constraints and roots share that same transport. Future
client variable identities are fixed by `transport_future`. -/
theorem quotient_uses_with_clients {n count boundary before after q uses store}
    (bounded : StoreBounded n store)
    (anchors : PreservesAnchors n boundary before after q)
    (useBounds : ∀ use, use ∈ uses → use < count)
    (clients : Store) (ρ : Valuation)
    (solved : ((usesStore n boundary after uses (store.map (Constraint.rename q))) ++
      clients.map (Constraint.rename (transport n count boundary after q))).Satisfied ρ) :
    ((usesStore n boundary before uses store) ++ clients).Satisfied
      (fun k i => ρ k (transport n count boundary after q k i)) := by
  rw [Store.satisfied_append] at solved ⊢
  exact ⟨quotient_uses_sound bounded anchors useBounds ρ solved.1,
    (Store.quotient_pullback _ _ _).mp solved.2⟩

theorem lowered_quotient_uses_with_clients {n count boundary before q uses store}
    (bounded : StoreBounded n store)
    (useBounds : ∀ use, use ∈ uses → use < count)
    (clients : Store) (ρ : Valuation)
    (solved : ((usesStore n boundary (quotientLevels n before q) uses
        (store.map (Constraint.rename q))) ++
      clients.map (Constraint.rename (transport n count boundary (quotientLevels n before q) q))).Satisfied ρ) :
    ((usesStore n boundary before uses store) ++ clients).Satisfied
      (fun k i => ρ k (transport n count boundary (quotientLevels n before q) q k i)) := by
  exact quotient_uses_with_clients bounded (quotientLevels_preserve_anchors n boundary before q)
    useBounds clients ρ solved

/-- For a genuine canonical quotient the seeded construction is the exact
class minimum, and all post-use coordinates remain below the future-client
region. The same valuation simultaneously reflects the complete clause store. -/
theorem minimum_quotient_uses_with_clients {n count boundary before q uses store}
    (canonical : Canonical n q) (bounded : StoreBounded n store)
    (useBounds : ∀ use, use ∈ uses → use < count)
    (clients : Store) (ρ : Valuation)
    (solved : ((usesStore n boundary (quotientLevels n before q) uses
        (store.map (Constraint.rename q))) ++
      clients.map (Constraint.rename (transport n count boundary (quotientLevels n before q) q))).Satisfied ρ) :
    (((usesStore n boundary before uses store) ++ clients).Satisfied
      (fun k i => ρ k (transport n count boundary (quotientLevels n before q) q k i))) ∧
    (∀ k i, i < n → FiberMinimum n before q k (q k i) (quotientLevels n before q k (q k i))) ∧
    (∀ use, use ∈ uses → ∀ k i, i < n →
      freshen n boundary (quotientLevels n before q) use k (q k i) < n * (count + 1)) := by
  refine ⟨lowered_quotient_uses_with_clients bounded useBounds clients ρ solved,
    canonical_quotient_minimum canonical, ?_⟩
  intro use member k i hi
  exact canonical_post_use_bounded canonical (useBounds use member) hi

/-- The two uses allocate distinct eligible coordinates, and a later quotient
may consistently map both to one shared lower-level anchor. Future client
coordinates remain fixed. This is forward soundness, not reverse coverage. -/
theorem two_uses_one_anchor :
    let levels : Levels := fun _ i => i
    let q : Renaming := fun _ _ => 0
    freshen 2 0 levels 0 .value 1 = 3 ∧
    freshen 2 0 levels 1 .value 1 = 5 ∧
    transport 2 2 0 (quotientLevels 2 levels q) q .value 3 = 0 ∧
    transport 2 2 0 (quotientLevels 2 levels q) q .value 5 = 0 ∧
    transport 2 2 0 (quotientLevels 2 levels q) q .value 6 = 6 := by
  decide

/-- Raising a captured row into the eligible region would invalidate the
commuting square. Anchor preservation is a real condition, not a consequence
of an arbitrary canonical row map. -/
theorem raising_anchor_breaks_transport :
    let before : Levels := fun _ _ => 0
    let after : Levels := fun _ i => i
    let q : Renaming := fun _ i => if i = 0 then 1 else 0
    transport 2 1 0 after q .value (freshen 2 0 before 0 .value 0) ≠
      freshen 2 0 after 0 .value (q .value 0) := by
  decide

end YulangClosure.SimpleSub.Generalization
