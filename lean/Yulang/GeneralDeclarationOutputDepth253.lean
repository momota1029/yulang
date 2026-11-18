import Yulang.GeneralDeclarationProducerRank253
import Yulang.GeneralPatternAdditiveDepth253
namespace Yulang.GeneralDeclarationOutputDepth253
open GeneralDeclarations GeneralDeclarationPatterns GeneralPatternAdditiveDepth253

/-- Only variables occurring in the template require a depth bound. -/
theorem subst_supported (term : Pattern) (capture : Nat → Pattern) (bound : Nat)
 (bounded : ∀ name ∈ term.variables, depth (capture name) ≤ bound) :
 depth (term.subst capture) ≤ depth term + bound := by
 let restricted : Nat → Pattern := fun name => if name ∈ term.variables then capture name else .var 0
 have same : term.subst capture = term.subst restricted := subst_congr term capture restricted (by
   intro name member
   simp only [restricted,member,ite_true])
 rw [same]
 apply subst_depth
 intro name
 by_cases member : name ∈ term.variables
 · simpa only [restricted,member,ite_true] using bounded name member
 · simp only [restricted,member,ite_false,depth]
   exact Nat.zero_le _

/-- Associated RHSs may read both input variables and produced output-only
binders. Their maximum replaces the incorrect input-only substitution premise. -/
theorem associated_bound (checked : DeclarationChecked constructors roles declaration)
 (equation : Equation) (member : equation ∈ declaration.associated)
 (capture : Nat → Pattern) (inputBound outputBound : Nat)
 (inputs : ∀ name ∈ declaration.inputNames, depth (capture name) ≤ inputBound)
 (outputs : ∀ name ∈ declaration.outputNames, depth (capture name) ≤ outputBound) :
 depth ((normalize equation.rhs).subst capture) ≤ depth (normalize equation.rhs) + max inputBound outputBound := by
 apply subst_supported
 intro name used
 rcases checked.scope.2.1 equation member name used with input | output
 · exact Nat.le_trans (inputs name input) (Nat.le_max_left _ _)
 · exact Nat.le_trans (outputs name output) (Nat.le_max_right _ _)

/-- When the designated child interpretations have a uniform bound, Produced
supplies the missing binder bound. This remains a declaration-semantic premise,
not an assertion that every source trace already has such child readbacks. -/
theorem produced_bound (checked : DeclarationChecked constructors roles declaration)
 (associated : Associated) (capture : Nat → Pattern)
 (satisfied : SatisfiesOutputs associated declaration capture) (bound : Nat)
 (children : ∀ clause ∈ declaration.requirements, ∀ equation ∈ clause.outputs,
   depth (associated clause.role (substArgs capture (normalizeArgs clause.arguments)) equation.name) ≤ bound) :
 ∀ name ∈ declaration.outputNames, depth (capture name) ≤ bound := by
 intro name member
 obtain ⟨clause,present,equation,produces,_,_,value⟩ :=
   GeneralDeclarationProducerRank253.binder_producer checked associated capture satisfied name member
 rw [value]
 exact children clause present equation produces

theorem associated_from_children (checked : DeclarationChecked constructors roles declaration)
 (equation : Equation) (member : equation ∈ declaration.associated)
 (associated : Associated) (capture : Nat → Pattern)
 (satisfied : SatisfiesOutputs associated declaration capture) (inputBound childBound : Nat)
 (inputs : ∀ name ∈ declaration.inputNames, depth (capture name) ≤ inputBound)
 (children : ∀ clause ∈ declaration.requirements, ∀ equation ∈ clause.outputs,
   depth (associated clause.role (substArgs capture (normalizeArgs clause.arguments)) equation.name) ≤ childBound) :
 depth ((normalize equation.rhs).subst capture) ≤ depth (normalize equation.rhs) + max inputBound childBound :=
 associated_bound checked equation member capture inputBound childBound inputs
   (produced_bound checked associated capture satisfied childBound children)
end Yulang.GeneralDeclarationOutputDepth253
