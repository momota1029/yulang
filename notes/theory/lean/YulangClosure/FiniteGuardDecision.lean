import YulangClosure.GuardedValueGraph
import Init.Data.List.FinRange

/-! Constructive finite transparent-graph decision. Research syntax only.
No rank, termination oracle, classical choice, or whole-graph acyclicity is input. -/
namespace YulangClosure.GuardedValueGraph.FiniteDecision

/-- Exact number of transparent edges before a concrete terminal node. -/
inductive Ends (g : Graph R) : R → Nat → Prop where
  | done (r) : (g r).next = none → Ends g r 0
  | step : (g r).next = some s → Ends g s k → Ends g r (k + 1)

def height (g : Graph R) : Nat → R → Nat
  | 0, _ => 0
  | fuel + 1, r => match (g r).next with
    | none => 0
    | some s => height g fuel s + 1

theorem ends_height {g : Graph R} {r : R} {k : Nat} (h : Ends g r k) :
    ∀ fuel, k ≤ fuel → height g fuel r = k := by
  induction h with
  | done r hn =>
      intro fuel _
      cases fuel <;> simp [height, hn]
  | @step r s k hs he ih =>
      intro fuel hk
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [height, hs]
          rw [ih fuel (by omega)]

theorem ends_observes {g : Graph R} {r : R} {k : Nat} (h : Ends g r k) :
    ∃ node, Observes g r node := by
  induction h with
  | done r hn => exact ⟨g r, .done r hn⟩
  | step hs _ ih =>
      obtain ⟨node, ho⟩ := ih
      exact ⟨node, .step hs ho⟩

theorem path_trans {g : Graph R} {r s t : R}
    (h : TransparentPath g r s) (h' : TransparentPath g s t) :
    TransparentPath g r t := by
  induction h with
  | edge hs => exact .cons hs h'
  | cons hs _ ih => exact .cons hs (ih h')

/-- Delete one occurrence using the supplied decidable equality. The local
lemmas avoid classical dependencies in the library erase equivalences. -/
def eraseOne [DecidableEq A] (a : A) : List A → List A
  | [] => []
  | b :: bs => if b = a then bs else b :: eraseOne a bs

theorem eraseOne_mem [DecidableEq A] {a x : A} {ys : List A}
    (hne : x ≠ a) (hx : x ∈ ys) : x ∈ eraseOne a ys := by
  induction ys with
  | nil => cases hx
  | cons b bs ih =>
      by_cases h : b = a
      · simp only [eraseOne, h, ite_true]
        rcases List.mem_cons.mp hx with he | ht
        · exact False.elim (hne (he.trans h))
        · exact ht
      · simp only [eraseOne, h, ite_false]
        rcases List.mem_cons.mp hx with he | ht
        · exact List.mem_cons.mpr (.inl he)
        · exact List.mem_cons.mpr (.inr (ih ht))

theorem eraseOne_length [DecidableEq A] {a : A} {ys : List A}
    (ha : a ∈ ys) : (eraseOne a ys).length + 1 = ys.length := by
  induction ys with
  | nil => cases ha
  | cons b bs ih =>
      by_cases h : b = a
      · simp only [eraseOne, h, ite_true, List.length_cons]
      · have ht : a ∈ bs := by
          rcases List.mem_cons.mp ha with he | ht
          · exact False.elim (h he.symm)
          · exact ht
        simp only [eraseOne, h, ite_false, List.length_cons]
        have hi := ih ht
        omega

/-- Constructive finite-list bound, with no imported erase equivalence. -/
theorem nodup_length_le [DecidableEq A] {xs ys : List A}
    (hd : xs.Nodup) (hs : xs ⊆ ys) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons a xs ih =>
      rw [List.nodup_cons] at hd
      have ha : a ∈ ys := hs (List.mem_cons_self ..)
      have hsub : xs ⊆ eraseOne a ys := by
        intro x hx
        have hxa : x ≠ a := fun h => hd.1 (h ▸ hx)
        exact eraseOne_mem hxa (hs (List.mem_cons_of_mem _ hx))
      have hi := ih hd.2 hsub
      have hl := eraseOne_length ha
      simp only [List.length_cons]
      omega

theorem finite_list_bound {xs : List (Fin n)} (hd : xs.Nodup) :
    xs.length ≤ n := by
  have h := nodup_length_le (ys := List.finRange n) hd
    (fun x _ => List.mem_finRange x)
  simpa using h

/-- A finite, possibly empty prefix leading from the requested root. -/
inductive Reaches (g : Graph R) : R → R → Prop where
  | here (r) : Reaches g r r
  | step : (g r).next = some s → Reaches g s t → Reaches g r t

/-- Explicit membership decision uses only the supplied equality decision,
avoiding order-package instances with unrelated classical proof dependencies. -/
def memberDecidable [DecidableEq A] (x : A) : (xs : List A) → Decidable (x ∈ xs)
  | [] => isFalse (by intro h; cases h)
  | a :: xs =>
      if h : x = a then isTrue (List.mem_cons.mpr (.inl h))
      else match memberDecidable x xs with
      | isTrue ht => isTrue (List.mem_cons.mpr (.inr ht))
      | isFalse ht => isFalse (by
          intro hm
          rcases List.mem_cons.mp hm with he | he
          · exact h he
          · exact ht he)

/-- Both branches return a concrete endpoint. The cycle is nonempty and is
reachable from the requested start, even when there is an initial tail. -/
inductive WalkResult (g : FiniteGraph n) (r : Fin n) (fuel : Nat) : Type where
  | terminal (distance : Nat) (vertex : Fin n) :
      distance < fuel → Ends g r distance → (g vertex).next = none →
      Observes g r (g vertex) → WalkResult g r fuel
  | cycle (vertex : Fin n) : TransparentPath g vertex vertex →
      Reaches g r vertex → WalkResult g r fuel

/-- Every saved vertex has a nonempty path to the current vertex. Repetition
therefore constructs a cycle, including after a nonempty tail. -/
def walkAux (g : FiniteGraph n) (fuel : Nat) :
    (seen : List (Fin n)) → (r : Fin n) →
    seen.Nodup → seen.length + fuel = n →
    (∀ s, s ∈ seen → TransparentPath g s r) → WalkResult g r fuel :=
  match fuel with
  | 0 => fun seen r hd hsize hp =>
      letI : Decidable (r ∈ seen) := memberDecidable r seen
      if hm : r ∈ seen then .cycle r (hp r hm) (.here r)
      else False.elim (by
        have hb := finite_list_bound (List.nodup_cons.mpr ⟨hm, hd⟩)
        simp only [List.length_cons] at hb
        omega)
  | fuel + 1 => fun seen r hd hsize hp =>
      letI : Decidable (r ∈ seen) := memberDecidable r seen
      if hm : r ∈ seen then .cycle r (hp r hm) (.here r)
      else match hn : (g r).next with
      | none => .terminal 0 r (Nat.zero_lt_succ _) (.done r hn) hn (.done r hn)
      | some s =>
          let hd' : (r :: seen).Nodup := List.nodup_cons.mpr ⟨hm, hd⟩
          let hp' : ∀ t, t ∈ r :: seen → TransparentPath g t s := by
            intro t ht
            rcases List.mem_cons.mp ht with he | ht
            · subst t; exact .edge hn
            · exact path_trans (hp t ht) (.edge hn)
          match walkAux g fuel (r :: seen) s hd' (by simp only [List.length_cons]; omega) hp' with
          | .terminal k vertex hk he ht ho =>
              .terminal (k + 1) vertex (by omega) (.step hn he) ht (.step hn ho)
          | .cycle c hc reachable => .cycle c hc (.step hn reachable)

def walk (g : FiniteGraph n) (r : Fin n) : WalkResult g r n :=
  walkAux g n [] r (by simp) (by simp) (by intro s hs; cases hs)

def NoCycle (g : Graph R) : Prop := ∀ r, ¬ TransparentPath g r r

def AllEnd (g : FiniteGraph n) : Prop := ∀ r, ∃ k, k < n ∧ Ends g r k

theorem allEnd_of_noCycle {g : FiniteGraph n} (hc : NoCycle g) : AllEnd g := by
  intro r
  cases walk g r with
  | terminal k _ hk he _ _ => exact ⟨k, hk, he⟩
  | cycle c hp _ => exact False.elim (hc c hp)

/-- Rank is computed uniformly by n steps of the actual successor function.
The proof input provides no numeric ranks and is not used computationally. -/
def guardOfAllEnd (g : FiniteGraph n) (he : AllEnd g) : Guarded g where
  rank := height g n
  ceiling := n
  bound := by
    intro r
    obtain ⟨k, hk, hr⟩ := he r
    rw [ends_height hr n (by omega)]
    exact hk
  decrease := by
    intro r s hs
    obtain ⟨k, hk, hr⟩ := he r
    have er := ends_height hr n (by omega)
    cases hr with
    | done r hn => rw [hn] at hs; cases hs
    | @step r t k ht htail =>
        have ets : t = s := Option.some.inj (ht.symm.trans hs)
        subst t
        have es := ends_height htail n (by omega)
        change height g n s < height g n r
        rw [er, es]
        omega

def guardOfNoCycle (g : FiniteGraph n) (hc : NoCycle g) : Guarded g :=
  guardOfAllEnd g (allEnd_of_noCycle hc)

theorem guarded_iff_noCycle (g : FiniteGraph n) :
    Nonempty (Guarded g) ↔ NoCycle g := by
  constructor
  · intro ⟨guard⟩ r hp
    exact no_transparent_cycle guard r hp
  · intro hc
    exact ⟨guardOfNoCycle g hc⟩

/-- Canonical observation now needs only the finite cycle criterion. -/
theorem finite_reference_canonical {g : FiniteGraph n} {xi : Fin n → Ty}
    (hg : WellTyped g xi) (hc : NoCycle g) (r : Fin n) :
    ∃ node, Observes g r node ∧ Canonical (xi r) node :=
  reference_canonical hg (guardOfNoCycle g hc) r

theorem finite_no_bottom {g : FiniteGraph n} {xi : Fin n → Ty}
    (hg : WellTyped g xi) (hc : NoCycle g) (r : Fin n) : xi r ≠ .bottom :=
  no_bottom_reference hg (guardOfNoCycle g hc) r

inductive ScanResult (g : FiniteGraph n) (xs : List (Fin n)) : Type where
  | terminals : (∀ r, r ∈ xs → ∃ k, k < n ∧ Ends g r k) → ScanResult g xs
  | cycle (vertex : Fin n) : TransparentPath g vertex vertex → ScanResult g xs

def scan (g : FiniteGraph n) : (xs : List (Fin n)) → ScanResult g xs
  | [] => .terminals (by intro r hr; cases hr)
  | r :: xs => match walk g r with
    | .cycle c hc _ => .cycle c hc
    | .terminal k _ hk he _ _ => match scan g xs with
      | .cycle c hc => .cycle c hc
      | .terminals hs => .terminals (by
          intro s hmem
          rcases List.mem_cons.mp hmem with heq | hmem
          · subst s; exact ⟨k, hk, he⟩
          · exact hs s hmem)

inductive GuardDecision (g : FiniteGraph n) : Type where
  | guarded : Guarded g → GuardDecision g
  | cycle (vertex : Fin n) : TransparentPath g vertex vertex → GuardDecision g

/-- Total finite algorithm, with either a computed certificate or explicit cycle.
The empty graph requires no start vertex and returns a certificate. -/
def decideGuard (g : FiniteGraph n) : GuardDecision g :=
  match scan g (List.finRange n) with
  | .cycle c hc => .cycle c hc
  | .terminals hs => .guarded (guardOfAllEnd g (fun r => hs r (List.mem_finRange r)))

def noCycleDecidable (g : FiniteGraph n) : Decidable (NoCycle g) :=
  match decideGuard g with
  | .guarded guard => isTrue (fun r hp => no_transparent_cycle guard r hp)
  | .cycle c hc => isFalse (fun h => h c hc)

/-- Project only new-to-new transparent edges. An old target is terminal for
this local check, since allocate never introduces old-to-new edges. -/
def freshGraph (fresh : Fin n → Node (Sum R (Fin n))) : FiniteGraph n := fun s =>
  match (fresh s).next with
  | some (.inr t) => .alias t
  | _ => .unit

theorem freshGraph_edge (fresh : Fin n → Node (Sum R (Fin n))) (s t : Fin n) :
    (freshGraph fresh s).next = some t ↔ (fresh s).next = some (.inr t) := by
  unfold freshGraph
  cases hn : (fresh s).next with
  | none => simp [Node.next]
  | some target => cases target <;> simp [Node.next]

/-- Local criterion: exactly fresh-internal transparent cycles are forbidden. -/
def FreshNoCycle (fresh : Fin n → Node (Sum R (Fin n))) : Prop :=
  NoCycle (freshGraph fresh)

def allocateFiniteGuard {g : Graph R} (guard : Guarded g)
    (fresh : Fin n → Node (Sum R (Fin n))) (hc : FreshNoCycle fresh) :
    Guarded (allocate g fresh) :=
  let localGuard := guardOfNoCycle (freshGraph fresh) hc
  allocate_guard guard fresh localGuard.rank localGuard.ceiling localGuard.bound
    (fun s t he => localGuard.decrease s t ((freshGraph_edge fresh s t).mpr he))

/-- The original rec extension conclusion, with supplied local ranks, ceiling,
bounds and decreases removed. The original node/body typing premises remain. -/
theorem finite_rec_extension {g : Graph R} {xi : R → Ty} {nu : Fin n → Ty}
    (hg : WellTyped g xi) (guard : Guarded g)
    (fresh : Fin n → Node (Sum R (Fin n)))
    (hf : ∀ s, NodeTyped (joinTy xi nu) (fresh s) (nu s))
    (hc : FreshNoCycle fresh)
    {body : Term R (Fin n)} {a : Ty} (hb : Typed xi nu body a) :
    WellTyped (allocate g fresh) (joinTy xi nu) ∧
    (∀ r, ∃ node, Observes (allocate g fresh) r node ∧ Canonical (joinTy xi nu r) node) ∧
    Typed (joinTy xi nu) emptyTy (closeBody body) a := by
  have ht := allocate_typed hg fresh hf
  exact ⟨ht, reference_canonical ht (allocateFiniteGuard guard fresh hc), closeBody_typed hb⟩

/-- If the entire old graph is finite, its supplied rank disappears as well. -/
theorem finite_rec_extension_from_cycles {g : FiniteGraph m} {xi : Fin m → Ty}
    {nu : Fin n → Ty} (hg : WellTyped g xi) (hcOld : NoCycle g)
    (fresh : Fin n → Node (Sum (Fin m) (Fin n)))
    (hf : ∀ s, NodeTyped (joinTy xi nu) (fresh s) (nu s))
    (hcFresh : FreshNoCycle fresh)
    {body : Term (Fin m) (Fin n)} {a : Ty} (hb : Typed xi nu body a) :
    WellTyped (allocate g fresh) (joinTy xi nu) ∧
    (∀ r, ∃ node, Observes (allocate g fresh) r node ∧ Canonical (joinTy xi nu r) node) ∧
    Typed (joinTy xi nu) emptyTy (closeBody body) a :=
  finite_rec_extension hg (guardOfNoCycle g hcOld) fresh hf hcFresh hb

/-- The projection is an exact supplier of real allocated transparent paths. -/
theorem fresh_path_allocation {g : Graph R}
    {fresh : Fin n → Node (Sum R (Fin n))} {s t : Fin n}
    (h : TransparentPath (freshGraph fresh) s t) :
    TransparentPath (allocate g fresh) (.inr s) (.inr t) := by
  induction h with
  | edge he =>
      apply TransparentPath.edge
      exact (freshGraph_edge fresh _ _).mp he
  | cons he _ ih =>
      apply TransparentPath.cons _ ih
      exact (freshGraph_edge fresh _ _).mp he

/-- Given the original old certificate, the finite local cycle test is also
necessary, so it is not a stronger sufficient condition introduced for proofs. -/
theorem allocate_guard_iff {g : Graph R} (guard : Guarded g)
    (fresh : Fin n → Node (Sum R (Fin n))) :
    Nonempty (Guarded (allocate g fresh)) ↔ FreshNoCycle fresh := by
  constructor
  · intro ⟨post⟩ s hs
    exact no_transparent_cycle post (.inr s) (fresh_path_allocation hs)
  · intro hc
    exact ⟨allocateFiniteGuard guard fresh hc⟩

theorem noCycle_of_terminal {g : FiniteGraph n}
    (ht : ∀ r, (g r).next = none) : NoCycle g := by
  have he : AllEnd g := by
    intro r
    exact ⟨0, by have := r.isLt; omega, .done r (ht r)⟩
  intro r hp
  exact no_transparent_cycle (guardOfAllEnd g he) r hp

/-- Arbitrarily long chains, including the maximal n-edge chain on n+1 nodes.
This supplies the exact distance, not an assumed rank or termination fact. -/
def countdown (n : Nat) : FiniteGraph (n + 1) := fun r =>
  match hv : r.val with
  | 0 => .unit
  | k + 1 => .alias ⟨k, by have := r.isLt; omega⟩

theorem countdown_ends (n : Nat) (r : Fin (n + 1)) :
    Ends (countdown n) r r.val := by
  have aux : ∀ k (hk : k < n + 1), Ends (countdown n) ⟨k, hk⟩ k := by
    intro k
    induction k with
    | zero => intro hk; exact .done _ rfl
    | succ k ih =>
        intro hk
        exact .step rfl (ih (by omega))
  exact aux r.val r.isLt

theorem countdown_noCycle (n : Nat) : NoCycle (countdown n) := by
  intro r hp
  have he : AllEnd (countdown n) := fun s => ⟨s.val, s.isLt, countdown_ends n s⟩
  exact no_transparent_cycle (guardOfAllEnd _ he) r hp

theorem countdown_exact_height (n : Nat) (r : Fin (n + 1)) :
    height (countdown n) (n + 1) r = r.val :=
  ends_height (countdown_ends n r) (n + 1) (Nat.le_of_lt r.isLt)

def selfCycle : FiniteGraph 1 := fun r => .alias r

theorem selfCycle_rejected : ¬ NoCycle selfCycle := by
  intro hc
  exact hc 0 (.edge rfl)

def cycleWithTail : FiniteGraph 3 := fun r =>
  if r.val = 0 then .alias 1 else .alias 2

theorem tail_reaches_cycle : TransparentPath cycleWithTail 0 2 :=
  .cons rfl (.edge rfl)

theorem tail_cycle_explicit : TransparentPath cycleWithTail 2 2 := .edge rfl

theorem tail_cycle_rejected : ¬ NoCycle cycleWithTail :=
  fun hc => hc 2 tail_cycle_explicit

/-- Whole-graph cycles through data fields remain admissible to the guard test.
No recursive type equation or typing claim is fabricated for this pair. -/
def dataSelfCycle : FiniteGraph 1 := fun r => .pair r r

theorem dataSelfCycle_allowed : NoCycle dataSelfCycle :=
  noCycle_of_terminal (fun _ => rfl)

def sharedTerminal : FiniteGraph 3 := fun r =>
  if r.val = 0 then .unit else .alias 0

theorem sharedTerminal_ends (r : Fin 3) :
    ∃ k, k < 3 ∧ Ends sharedTerminal r k := by
  by_cases h : r.val = 0
  · exact ⟨0, by omega, .done r (by simp [sharedTerminal, h, Node.next])⟩
  · exact ⟨1, by omega, .step (by simp [sharedTerminal, h, Node.next]) (.done 0 rfl)⟩

def sharedTerminal_guard : Guarded sharedTerminal :=
  guardOfAllEnd sharedTerminal sharedTerminal_ends

/-- Both actual lambda bodies call the opposite fresh graph reference. -/
def finiteMutualLambda : FiniteGraph 2 := fun r =>
  .lam .unit .unit (.app (.ref (if r.val = 0 then 1 else 0)) (.var none))

theorem finiteMutualLambda_typed :
    WellTyped finiteMutualLambda (fun _ => .arrow .unit .unit) := by
  intro r
  exact NodeTyped.lam (Typed.app (Typed.ref _) (Typed.var none))

theorem finiteMutualLambda_noCycle : NoCycle finiteMutualLambda :=
  noCycle_of_terminal (fun _ => rfl)

def finiteMutualLambda_guard : Guarded finiteMutualLambda :=
  guardOfNoCycle finiteMutualLambda finiteMutualLambda_noCycle

/-- Fresh-to-old transparent references are accepted without a local rank input,
even when the old reference sort is infinite. -/
def oldAliasFresh (old : R) : Fin 1 → Node (Sum R (Fin 1)) :=
  fun _ => .alias (.inl old)

theorem oldAliasFresh_noCycle (old : R) : FreshNoCycle (oldAliasFresh old) :=
  noCycle_of_terminal (fun _ => rfl)

def oldAliasAllocation_guard {g : Graph R} (guard : Guarded g) (old : R) :
    Guarded (allocate g (oldAliasFresh old)) :=
  allocateFiniteGuard guard (oldAliasFresh old) (oldAliasFresh_noCycle old)

/-- A graph with zero nodes has a computed certificate without a root oracle. -/
def zeroGraph : FiniteGraph 0 := fun r => Fin.elim0 r

def zeroGraph_guard : Guarded zeroGraph :=
  guardOfNoCycle zeroGraph (fun r => Fin.elim0 r)

end YulangClosure.GuardedValueGraph.FiniteDecision
