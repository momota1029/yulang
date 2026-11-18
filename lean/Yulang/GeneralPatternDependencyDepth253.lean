import Yulang.GeneralPatternAdditiveDepth253
namespace Yulang.GeneralPatternDependencyDepth253
open GeneralDeclarationPatterns GeneralPatternAdditiveDepth253

/-- A topological readback construction: each new output may use source terms
and earlier outputs. Weights record actual template depths, not an assumed
source-depth bound. Producing this order from a source trace is a separate goal. -/
inductive Build (source : List Pattern) : List Pattern → List Nat → Prop
 | nil : Build source [] []
 | output (older : Build source outputs weights) (body : Pattern) (capture : Nat → Pattern)
   (dependencies : ∀ name, capture name ∈ source ++ outputs) :
   Build source (body.subst capture :: outputs) (depth body :: weights)

theorem sum_bound (built : Build source outputs weights) :
 ∀ term ∈ outputs, depth term ≤ depths source + weights.sum := by
 induction built with
 | nil => intro term member; cases member
 | @output outputs weights older body capture dependencies ih =>
   have captureBound : ∀ name, depth (capture name) ≤ depths source + weights.sum := by
     intro name
     rcases List.mem_append.mp (dependencies name) with original | prior
     · have bounded := member_depth source _ original
       omega
     · exact ih _ prior
   have newest := subst_depth body capture (depths source + weights.sum) captureBound
   intro term member
   rcases List.mem_cons.mp member with rfl | prior
   · simp only [List.sum_cons]; omega
   · have bounded := ih term prior
     simp only [List.sum_cons]; omega

theorem lengths (built : Build source outputs weights) : outputs.length = weights.length := by
 induction built with
 | nil => rfl
 | output older body capture dependencies ih => simp only [List.length_cons,ih]

theorem sum_le_uniform (weights : List Nat) (bound : Nat)
 (bounded : ∀ weight ∈ weights, weight ≤ bound) : weights.sum ≤ weights.length * bound := by
 induction weights with
 | nil => simp
 | cons first rest ih =>
   have one := bounded first (List.mem_cons_self ..)
   have tail := ih (fun weight member => bounded weight (List.mem_cons_of_mem _ member))
   simp only [List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
   omega

/-- A coarse corollary of path-wise addition: at most N topologically ordered
output nodes with template depth at most T give sourceDepth + N*T. Finite
owners alone do not furnish such an order, nor one output per owner. -/
theorem uniform_bound (built : Build source outputs weights) (bound : Nat)
 (bounded : ∀ weight ∈ weights, weight ≤ bound) (term : Pattern) (member : term ∈ outputs) :
 depth term ≤ depths source + outputs.length * bound := by
 have result := sum_bound built term member
 have total := sum_le_uniform weights bound bounded
 rw [←lengths built] at total
 omega

/-- Positive constructor gain around a cycle contradicts finite depth. The
strict premise matters: an alias-only cycle has zero gain and is not refuted. -/
theorem no_positive_cycle (depths : Nat → Nat) (first middle : Nat)
 (forward : depths first < depths middle) (back : depths middle ≤ depths first) : False := by omega

theorem alias_cycle_possible : ∃ depths : Nat → Nat, depths 0 ≤ depths 1 ∧ depths 1 ≤ depths 0 :=
 ⟨fun _ => 0,Nat.le_refl 0,Nat.le_refl 0⟩
end Yulang.GeneralPatternDependencyDepth253
