import Yulang.FiniteBooleanReachability

/-!
# Computed descent for the immediate part of a structural cast plan

A finite plan may contain recursive function wrappers. Immediate edges stop
at a wrapper; its argument and result plans are roots for a subsequent call.
The Boolean checker computes absence of immediate cycles. The rank is the
number of reachable plan nodes, derived from that same graph, not supplied
by a caller. Source variance derivation must connect its permitted plans to
this check; this module does not assume that arbitrary metadata does so.
-/

namespace Yulang.CommonDeclaredCastCostGraph

open FiniteBooleanReachability (Path entry closure)

inductive Node (n : Nat) where
  | keep
  | leaf
  | product (parts : List (Fin n))
  | variant (branches : List (Fin n))
  | nominal (body : Fin n)
  | function (argument result : Fin n)
  deriving DecidableEq, Repr

def Node.immediate : Node n → List (Fin n)
  | .keep | .leaf | .function _ _ => []
  | .product parts | .variant parts => parts
  | .nominal body => [body]

abbrev Plan (n : Nat) := Fin n → Node n

def edge (plan : Plan n) (source target : Fin n) : Bool :=
  decide (target ∈ (plan source).immediate)

def reached (plan : Plan n) (source : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun target => entry (closure (edge plan)) source target

@[simp] theorem mem_reached (plan : Plan n) (source target : Fin n) :
    target ∈ reached plan source ↔ Path (edge plan) source target := by
  simp [reached, FiniteBooleanReachability.closure_exact]

def Acyclic (plan : Plan n) : Prop :=
  ∀ source target, target ∈ (plan source).immediate → ¬ Path (edge plan) target source

def check (plan : Plan n) : Bool :=
  let paths := closure (edge plan)
  (List.finRange n).all fun source =>
    (plan source).immediate.all fun target => !entry paths target source

/-- The executable finite check iff an independent finite-path judgment.
Function argument/result references are deliberately not immediate edges. -/
theorem check_exact (plan : Plan n) : check plan = true ↔ Acyclic plan := by
  simp [check, Acyclic, FiniteBooleanReachability.closure_exact, Bool.eq_false_iff]

def rank (plan : Plan n) (node : Fin n) : Nat := (reached plan node).length

theorem rank_le (plan : Plan n) (node : Fin n) : rank plan node ≤ n := by
  simpa [rank, reached] using List.length_filter_le
    (fun target => entry (closure (edge plan)) node target) (List.finRange n)

/-- Every actual immediate child has a smaller computed rank whenever the
finite checker accepts. No rank, fuel or data-size premise is supplied. -/
theorem rank_decreases (plan : Plan n) (accepted : check plan = true)
    (source target : Fin n) (child : target ∈ (plan source).immediate) :
    rank plan target < rank plan source := by
  have acyclic := (check_exact plan).mp accepted
  have step : edge plan source target = true := by simpa [edge] using child
  have absent : source ∉ reached plan target := by
    intro present
    exact acyclic source target child ((mem_reached plan target source).mp present)
  have distinct : (source :: reached plan target).Nodup :=
    List.nodup_cons.mpr ⟨absent, (List.nodup_finRange n).filter _⟩
  have included : source :: reached plan target ⊆ reached plan source := by
    intro node member
    rcases List.mem_cons.mp member with rfl | later
    · exact (mem_reached plan _ _).mpr (.nil _)
    · exact (mem_reached plan source node).mpr
        (.cons step ((mem_reached plan target node).mp later))
  have sizes := distinct.length_le_of_subset included
  simp only [List.length_cons] at sizes
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) sizes

end Yulang.CommonDeclaredCastCostGraph
