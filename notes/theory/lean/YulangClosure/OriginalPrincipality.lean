import YulangClosure.SimpleSubGeneralizationSoundness

/-!
An exact algebraic boundary for the ORIGINAL principality obligation.

The original obligation is `2026-10-13-intrusion-source-preservation-proof.md`
sections 1, 3 and 5, with the immutable-birth-level correction of 2026-10-24.
It requires a source-derived JOINT scoped strategy across generalization and
all lawful uses, not preservation of arbitrary old solver assignments.

This module does not assert that obligation or define a replacement source
language. It constructs the exact reverse-coverage criterion for the existing
finite-use native algebra: a pre-quotient model must be constant on the fibers
of the ONE whole-use transport. A canonical quotient gives an explicit descent;
there are no separately chosen per-use or per-clause witnesses. All constructors
of `SimpleSub.Term`, its two kinds and the four Function ports remain present.

The source rule supplying such a fiber-compatible strategy for every actually
qualifying occurrence, the original semantic Call/effect/evidence families,
recursive type interpretation, and actual freshenAbove correspondence remain
open. This is not a source-qualified counterexample or whole-Yulang theorem.
-/
namespace YulangClosure.SimpleSub.OriginalPrincipality

open Generalization

/-- Canonical finite-use transport is a retraction on the complete coordinate
space. This includes unused allocation slots and every later client variable. -/
theorem transport_idempotent {n count boundary after q}
    (canonical : Canonical n q) (k : Kind) (i : Nat) :
    transport n count boundary after q k
        (transport n count boundary after q k i) =
      transport n count boundary after q k i := by
  by_cases base : i < n
  · rw [transport_base base, transport_base (canonical.1 k i base)]
    exact canonical.2 k i base
  · by_cases block : i < n * (count + 1)
    · have hn : 0 < n := by
        cases n with
        | zero => simp at block
        | succ n => exact Nat.zero_lt_succ n
      have hi : n ≤ i := Nat.le_of_not_gt base
      have rowBound : (i - n) % n < n := Nat.mod_lt _ hn
      have useBound : (i - n) / n < count := by
        apply (Nat.div_lt_iff_lt_mul hn).mpr
        have bound : i < count * n + n := by
          simpa only [Nat.mul_add, Nat.mul_one, Nat.mul_comm n count] using block
        omega
      have repr : copyIndex n ((i - n) / n) ((i - n) % n) = i := by
        have division := Nat.mod_add_div' (i - n) n
        unfold copyIndex
        omega
      rw [← repr, transport_copy useBound rowBound]
      by_cases low : after k (q k ((i - n) % n)) ≤ boundary
      · rw [freshen_anchor low,
          transport_base (canonical.1 k _ rowBound), canonical.2 k _ rowBound]
      · rw [freshen_eligible (Nat.lt_of_not_ge low),
          transport_copy useBound (canonical.1 k _ rowBound),
          canonical.2 k _ rowBound]
        exact freshen_eligible (Nat.lt_of_not_ge low)
    · rw [transport_future (Nat.le_of_not_gt block),
        transport_future (Nat.le_of_not_gt block)]

/-- This predicate tests equality of the entire assigned type at every pair of
coordinates identified by the actual transport; it does not select witnesses. -/
def FiberConstant (map : Renaming) (valuation : Valuation) : Prop :=
  ∀ k i j, map k i = map k j → valuation k i = valuation k j

/-- One shared quotient valuation exists precisely when the original valuation
is constant on transport fibers. The reverse direction constructs it as the
same valuation on canonical representatives, without choice. -/
theorem joint_descent_iff_fiber_constant {n count boundary after q}
    (canonical : Canonical n q) (ρ : Valuation) :
    (∃ σ : Valuation, ∀ k i,
      σ k (transport n count boundary after q k i) = ρ k i) ↔
      FiberConstant (transport n count boundary after q) ρ := by
  constructor
  · rintro ⟨σ, same⟩ k i j equal
    rw [← same k i, ← same k j, equal]
  · intro constant
    refine ⟨ρ, ?_⟩
    intro k i
    exact constant k _ _ (transport_idempotent canonical k i)

/-- Fiber constancy makes the quotient pullback literally the original ONE
valuation, including both effect coordinates and all future client variables. -/
theorem pullback_eq_self {n count boundary after q}
    (canonical : Canonical n q) (ρ : Valuation)
    (constant : FiberConstant (transport n count boundary after q) ρ) :
    (fun k i => ρ k (transport n count boundary after q k i)) = ρ := by
  funext k i
  exact constant k _ _ (transport_idempotent canonical k i)

/-- All roots and every structural child retain their interpretation under the
same descended valuation. Optional bits, labels, tags and order are unchanged. -/
theorem root_descent {map : Renaming} {ρ σ : Valuation}
    (same : ∀ k i, σ k (map k i) = ρ k i) {k} (root : Term k) :
    (root.rename map).subst σ = root.subst ρ := by
  rw [Term.rename_subst]
  have equal : (fun k i => σ k (map k i)) = ρ := by
    funext k i
    exact same k i
  rw [equal]

/-- Exact reverse transport, assuming only the explicit algebraic fiber
criterion in addition to the existing finite-store/anchor preconditions.
It changes neither the native store nor the original source domain. -/
theorem quotient_uses_complete_on_fiber {n count boundary before after q uses store}
    (canonical : Canonical n q) (bounded : StoreBounded n store)
    (anchors : PreservesAnchors n boundary before after q)
    (useBounds : ∀ use, use ∈ uses → use < count)
    (clients : Store) (ρ : Valuation)
    (constant : FiberConstant (transport n count boundary after q) ρ)
    (solved : ((usesStore n boundary before uses store) ++ clients).Satisfied ρ) :
    ((usesStore n boundary after uses (store.map (Constraint.rename q))) ++
      clients.map (Constraint.rename (transport n count boundary after q))).Satisfied ρ := by
  have fixed := pullback_eq_self canonical ρ constant
  rw [Store.satisfied_append] at solved ⊢
  refine ⟨?_, ?_⟩
  · rw [usesStore_satisfied] at solved
    rw [usesStore_satisfied]
    constructor
    · intro c hc
      rcases List.mem_map.mp hc with ⟨old, member, rfl⟩
      have evidence := solved.1.1 old member
      have bounds := bounded old member
      have lower := base_term_pullback (count := count) (boundary := boundary)
        (after := after) (q := q) bounds.1 ρ
      have upper := base_term_pullback (count := count) (boundary := boundary)
        (after := after) (q := q) bounds.2 ρ
      rw [fixed] at lower upper
      simpa only [Constraint.Satisfied, Constraint.rename, ← lower, ← upper] using evidence
    · intro use inUses c hc
      rcases List.mem_map.mp hc with ⟨old, member, rfl⟩
      have evidence := solved.1.2 use inUses old member
      have bounds := bounded old member
      have lower := fresh_term_pullback anchors (useBounds use inUses) bounds.1 ρ
      have upper := fresh_term_pullback anchors (useBounds use inUses) bounds.2 ρ
      rw [fixed] at lower upper
      simp only [Term.rename_subst] at lower upper
      change Sub
        (old.lower.subst (fun k i => ρ k (freshen n boundary before use k i)))
        (old.upper.subst (fun k i => ρ k (freshen n boundary before use k i))) at evidence
      change Sub
        ((old.lower.rename q).subst (fun k i => ρ k (freshen n boundary after use k i)))
        ((old.upper.rename q).subst (fun k i => ρ k (freshen n boundary after use k i)))
      simpa only [Term.rename_subst, ← lower, ← upper] using evidence
  · apply (Store.quotient_pullback _ _ _).mpr
    simpa only [fixed] using solved.2

/-- Exact solution-set correspondence, rather than all-model preservation.
`observe` is one predicate of the WHOLE valuation, so correlated public roots
and shared anchors are not replaced by independent marginal witnesses.
No source-generated fiber model is assumed or manufactured here. -/
theorem joint_solution_coverage_iff {n count boundary before after q uses store}
    (canonical : Canonical n q) (bounded : StoreBounded n store)
    (anchors : PreservesAnchors n boundary before after q)
    (useBounds : ∀ use, use ∈ uses → use < count)
    (clients : Store) (observe : Valuation → Prop) :
    (∃ σ : Valuation,
      ((usesStore n boundary after uses (store.map (Constraint.rename q))) ++
        clients.map (Constraint.rename (transport n count boundary after q))).Satisfied σ ∧
      observe (fun k i => σ k (transport n count boundary after q k i))) ↔
    (∃ ρ : Valuation,
      ((usesStore n boundary before uses store) ++ clients).Satisfied ρ ∧
      FiberConstant (transport n count boundary after q) ρ ∧ observe ρ) := by
  constructor
  · rintro ⟨σ, solved, observed⟩
    refine ⟨(fun k i => σ k (transport n count boundary after q k i)),
      quotient_uses_with_clients bounded anchors useBounds clients σ solved, ?_, observed⟩
    intro k i j equal
    change σ k (transport n count boundary after q k i) =
      σ k (transport n count boundary after q k j)
    rw [equal]
  · rintro ⟨ρ, solved, constant, observed⟩
    refine ⟨ρ, quotient_uses_complete_on_fiber canonical bounded anchors useBounds
      clients ρ constant solved, ?_⟩
    simpa only [pullback_eq_self canonical ρ constant] using observed

/-- The concrete two-use map already in Generalization really identifies
independently allocated rows 3 and 5. Different assignments on those rows
cannot be represented by one quotient valuation. This is an algebraic
counterexample to arbitrary-model descent, NOT a Yulang source counterexample. -/
theorem two_use_disagreement_blocks_joint_descent (ρ : Valuation)
    (different : ρ .value 3 ≠ ρ .value 5) :
    ¬ ∃ σ : Valuation, ∀ k i,
      σ k (transport 2 2 0
        (quotientLevels 2 (fun _ i => i) (fun _ _ => 0)) (fun _ _ => 0) k i) = ρ k i := by
  rintro ⟨σ, same⟩
  have first := same .value 3
  have second := same .value 5
  have maps := two_uses_one_anchor
  dsimp only at maps
  rw [maps.2.2.1] at first
  rw [maps.2.2.2.1] at second
  exact different (first.symm.trans second)


namespace TwoUseExample

/-- A real many-to-one row map: parent 2 and copy 1 are identified. At the
outer publication boundary 0, their minimum level 1 is still eligible. -/
def quotient : Renaming := fun _ i => if i = 2 then 1 else i

def before : Levels := fun _ i => i

def after : Levels := quotientLevels 3 before quotient

def map : Renaming := transport 3 2 0 after quotient

/-- Both Function effect ports and nontrivial optional-record, tuple and variant
payloads belong to the same retained constraint store. No constructor is erased. -/
def package (input output : Nat) : Term .value :=
  .function (.var input) (.var input) (.var output)
    (.recordCons 7 true (.tupleCons (.var output) .tupleNil)
      (.recordCons 9 false (.variantCons 3 (.var output) .variantNil) .recordNil))

def store : Store :=
  [⟨.value, .var 2, .var 1⟩,
   ⟨.effect, .var 2, .var 1⟩,
   ⟨.value, package 1 2, package 2 1⟩]

/-- Rows 4/5 are the first use, 7/8 the second; row 9 is an independent future
client. Both value and effect kinds share this simultaneous assignment rule. -/
def valuation : Valuation := fun _ i =>
  if i = 4 ∨ i = 5 then .atom 0
  else if i = 7 ∨ i = 8 then .atom 1
  else if i = 9 then .union (.atom 0) (.atom 1)
  else .atom 2

def clients : Store :=
  [⟨.value, .var 4, .var 9⟩,
   ⟨.value, .var 7, .var 9⟩,
   ⟨.effect, .union (.var 4) (.var 7), .var 9⟩]

theorem canonical : Canonical 3 quotient := by
  constructor <;> intro k i hi
  · have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases cases with rfl | rfl | rfl <;> simp [quotient]
  · have cases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases cases with rfl | rfl | rfl <;> rfl

theorem bounded : StoreBounded 3 store := by
  simp [StoreBounded, store, ConstraintBounded, Bounded, package]

theorem use_bounds : ∀ use, use ∈ ([0, 1] : List Nat) → use < 2 := by
  intro use member
  have cases : use = 0 ∨ use = 1 := by simpa using member
  rcases cases with rfl | rfl <;> decide

theorem valuation_fixed (k : Kind) (i : Nat) : valuation k (map k i) = valuation k i := by
  by_cases early : i < 9
  · have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨
      i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · have late : 3 * (2 + 1) ≤ i := by omega
    exact congrArg (valuation k) (transport_future late)

theorem constant : FiberConstant map valuation := by
  intro k i j equal
  exact (valuation_fixed k i).symm.trans
    ((congrArg (valuation k) equal).trans (valuation_fixed k j))

theorem base_satisfied : store.Satisfied valuation := by
  simp [store, Store.satisfied_cons, Constraint.Satisfied, package,
    Term.subst, valuation, Sub.refl]

theorem uses_satisfied : (usesStore 3 0 before [0, 1] store).Satisfied valuation := by
  rw [usesStore_satisfied]
  refine ⟨base_satisfied, ?_⟩
  intro use member
  have cases : use = 0 ∨ use = 1 := by simpa using member
  rcases cases with rfl | rfl <;>
    simp [store, Store.satisfied_cons, Constraint.Satisfied, package,
      Term.subst, valuation, freshen, before, Sub.refl]

theorem clients_satisfied : clients.Satisfied valuation := by
  simp only [clients, Store.satisfied_cons, Store.satisfied_nil, Constraint.Satisfied,
    Term.subst, valuation]
  refine ⟨?_, ?_, ?_, True.intro⟩
  · exact .unionLeft _ _
  · exact .unionRight _ _
  · exact .refl _

/-- One explicit pre-quotient valuation satisfies the complete retained base
store, both independently freshened stores, and a distinct future client. -/
theorem before_satisfied :
    ((usesStore 3 0 before [0, 1] store) ++ clients).Satisfied valuation :=
  (Store.satisfied_append _ _ _).mpr ⟨uses_satisfied, clients_satisfied⟩

/-- Constructive reverse coverage for this concrete non-injective quotient.
All hypotheses of the general theorem are discharged. The SAME explicit
valuation gives every store/client clause and every public-root equation.
The two uses retain distinct assignments, in both variable kinds. -/
theorem constructive_two_use_descent :
    ∃ σ : Valuation,
      ((usesStore 3 0 after [0, 1] (store.map (Constraint.rename quotient))) ++
        clients.map (Constraint.rename map)).Satisfied σ ∧
      (∀ k (root : Term k), (root.rename map).subst σ = root.subst valuation) ∧
      σ .value 4 = .atom 0 ∧ σ .value 7 = .atom 1 ∧
      σ .effect 4 = .atom 0 ∧ σ .effect 7 = .atom 1 ∧
      σ .value 9 = .union (.atom 0) (.atom 1) ∧
      quotient .value 1 = quotient .value 2 ∧ (1 : Nat) ≠ 2 := by
  refine ⟨valuation, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩
  · exact quotient_uses_complete_on_fiber canonical bounded
      (quotientLevels_preserve_anchors 3 0 before quotient) use_bounds
      clients valuation constant before_satisfied
  · intro k root
    exact root_descent valuation_fixed root

end TwoUseExample

end YulangClosure.SimpleSub.OriginalPrincipality
