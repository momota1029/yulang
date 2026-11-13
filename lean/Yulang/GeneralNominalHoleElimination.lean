import Yulang.GeneralNominalHoleMaterialization

/-! The substitution-budget calculation, separated from the open producer
invariant. An elimination consumes one present hole and substitutes one finite
term throughout the inventory; administrative observations are separate. -/
namespace Yulang.GeneralNominalHoleElimination
open GeneralNominalOriginTerms GeneralNominalRecursiveInspection
open GeneralNominalSharedEnumeration

def substitute (hole : Nat) (replacement : Expr Nat) (name : Nat) : Expr Nat :=
  if name = hole then replacement else .leaf name

def replace (hole : Nat) (replacement : Expr Nat) (term : Expr Nat) : Expr Nat :=
  term.bind (substitute hole replacement)

def Closed (holes : List Nat) (term : Expr Nat) : Prop :=
  ∀ name ∈ term.leaves, name ∈ holes

theorem replacement_closed (old : Closed holes term)
    (replacement : Closed (holes.erase hole) value) : Closed (holes.erase hole) (replace hole value term) := by
  intro name member
  obtain ⟨prior,present,member⟩ := (leaves_bind term (substitute hole value) name).mp member
  by_cases equal : prior = hole
  · apply replacement name
    simpa only [substitute,equal,ite_true] using member
  · have same : name = prior := by simpa [substitute,equal,Expr.leaves] using member
    subst name
    exact (List.mem_erase_of_ne equal).mpr (old prior present)

theorem replacement_bounded (old : Bounded holes tests depth term)
    (replacement : Bounded (holes.erase hole) tests extra value) :
    Bounded holes tests (depth+extra) (replace hole value term) := by
  have enlarge : ∀ expression bound, Bounded (holes.erase hole) tests bound expression →
      Bounded holes tests bound expression := by
    intro expression bound valid
    induction valid with
    | leaf name depth present => exact .leaf name depth (List.mem_of_mem_erase present)
    | node test children member bounded ih => exact .node test children member ih
  exact bounded_bind old (substitute hole value) (by
    intro name present
    by_cases same : name = hole
    · simpa only [substitute,same,ite_true] using enlarge value extra replacement
    · simpa only [substitute,same,ite_false] using Bounded.leaf name extra present)

structure Inventory where
  holes : List Nat
  terms : List (Expr Nat)
  depth : Nat

def eliminate (before : Inventory) (hole : Nat) (value : Expr Nat) (extra : Nat) : Inventory :=
  ⟨before.holes.erase hole,before.terms.map (replace hole value),before.depth+extra⟩

def Valid (tests : List Test) (state : Inventory) : Prop :=
  state.holes.Nodup ∧ ∀ term ∈ state.terms, Closed state.holes term ∧ Bounded state.holes tests state.depth term

theorem eliminate_valid (valid : Valid tests before) (_present : hole ∈ before.holes)
    (closed : Closed (before.holes.erase hole) value)
    (bounded : Bounded (before.holes.erase hole) tests extra value) :
    Valid tests (eliminate before hole value extra) := by
  refine ⟨valid.1.erase hole,?_⟩
  intro term member
  obtain ⟨old,present,rfl⟩ := List.mem_map.mp member
  have prior := valid.2 old present
  refine ⟨replacement_closed prior.1 closed,?_⟩
  have raw := replacement_bounded prior.2 bounded
  have restrict : ∀ expression depth, Bounded before.holes tests depth expression →
      Closed (before.holes.erase hole) expression → Bounded (before.holes.erase hole) tests depth expression := by
    intro expression depth bounded
    induction bounded with
    | leaf name depth member => exact fun closed => .leaf name depth (closed name (by simp [Expr.leaves]))
    | node test children member bounded ih =>
        intro closed
        refine .node test children member (fun index => ih index ?_)
        intro name present
        apply closed name
        simp only [Expr.leaves,List.mem_flatten,List.mem_ofFn]
        exact ⟨_,⟨index,rfl⟩,present⟩
  exact restrict _ _ raw (replacement_closed prior.1 closed)

inductive Trace (tests : List Test) (growth : Nat → Nat) : Inventory → Inventory → Nat → Prop
  | refl (state) : Trace tests growth state state 0
  | next (hole : Nat) (value : Expr Nat) : hole ∈ before.holes →
      Closed (before.holes.erase hole) value →
      Bounded (before.holes.erase hole) tests (growth before.depth) value →
      Trace tests growth (eliminate before hole value (growth before.depth)) after count →
      Trace tests growth before after (count+1)

def budget (growth : Nat → Nat) : Nat → Nat → Nat
  | 0,depth => depth
  | count+1,depth => budget growth count (depth+growth depth)

theorem budget_succ (growth : Nat → Nat) (count depth : Nat) :
    budget growth (count+1) depth = budget growth count depth + growth (budget growth count depth) := by
  induction count generalizing depth with
  | zero => rfl
  | succ count ih => exact ih (depth+growth depth)

theorem budget_mono (growth : Nat → Nat) (depth : Nat) (smaller : first ≤ last) :
    budget growth first depth ≤ budget growth last depth := by
  induction smaller with
  | refl => exact Nat.le_refl _
  | @step last smaller ih =>
      rw [budget_succ]
      exact Nat.le_trans ih (Nat.le_add_right _ _)

theorem bounded_enlarge (bound : Bounded first tests depth term) (included : first ⊆ last) :
    Bounded last tests depth term := by
  induction bound with
  | leaf name depth member => exact .leaf name depth (included member)
  | node test children member bounds ih => exact .node test children member ih

theorem trace_count (trace : Trace tests growth before after count) :
    count + after.holes.length = before.holes.length := by
  induction trace with
  | refl => simp
  | next hole value present closed bounded path ih =>
      have length := List.length_erase_of_mem present
      have positive := List.length_pos_of_mem present
      simp only [eliminate] at ih
      omega

theorem trace_depth (trace : Trace tests growth before after count) :
    after.depth = budget growth count before.depth := by
  induction trace with
  | refl => rfl
  | next hole value present closed bounded path ih => exact ih

theorem trace_holes (trace : Trace tests growth before after count) : after.holes ⊆ before.holes := by
  induction trace with
  | refl => exact fun _ member => member
  | next hole value present closed bounded path ih =>
      exact fun _ member => List.mem_of_mem_erase (ih member)

theorem trace_valid (trace : Trace tests growth before after count) (valid : Valid tests before) : Valid tests after := by
  induction trace with
  | refl => exact valid
  | next hole value present closed bounded path ih => exact ih (eliminate_valid valid present closed bounded)

theorem trace_budget (trace : Trace tests growth before after count) (valid : Valid tests before) :
    count ≤ before.holes.length ∧ after.depth = budget growth count before.depth ∧
      ∀ term ∈ after.terms, term ∈ enumerate after.holes tests (budget growth count before.depth) := by
  refine ⟨by have countBound := trace_count trace; omega,trace_depth trace,?_⟩
  intro term member
  rw [← trace_depth trace]
  exact bounded_enumerated ((trace_valid trace valid).2 term member).2

/-- Both the finite leaf list and iteration count in this conclusion are
fixed by the starting inventory. Real source production remains a separate bridge. -/
theorem conditional_budget (trace : Trace tests growth before after count) (valid : Valid tests before) :
    count ≤ before.holes.length ∧ after.depth ≤ budget growth before.holes.length before.depth ∧
      ∀ term ∈ after.terms,
        term ∈ enumerate before.holes tests (budget growth before.holes.length before.depth) := by
  have countBound := (trace_budget trace valid).1
  have depthBound : after.depth ≤ budget growth before.holes.length before.depth := by
    rw [trace_depth trace]
    exact budget_mono growth before.depth countBound
  refine ⟨countBound,depthBound,?_⟩
  intro term member
  exact bounded_enumerated (bounded_mono
    (bounded_enlarge ((trace_valid trace valid).2 term member).2 (trace_holes trace)) depthBound)

end Yulang.GeneralNominalHoleElimination
