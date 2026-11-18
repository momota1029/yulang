import Yulang.GeneralDeclarations
namespace Yulang.GeneralDeclarationProducerRank253
open GeneralDeclarations GeneralDeclarationPatterns

def mass (terms : List Pattern) : Nat := Roles.argsSize (counted terms)

/-- Checked declaration calls on instantiated syntax. This is deliberately
not the journal Step relation: it omits scheduling, aliasing and refreshes. -/
def Child (constructors : Constructors) (roles : Roles.RoleDecls)
 (child parent : List Pattern) : Prop :=
 ∃ declaration, DeclarationChecked constructors roles declaration ∧
 ∃ clause ∈ declaration.requirements, ∃ capture : Nat → Pattern,
 parent = substArgs capture declaration.head ∧ child = substArgs capture clause.arguments

theorem child_mass (call : Child constructors roles child parent) : mass child < mass parent := by
 obtain ⟨declaration,checked,clause,member,capture,rfl,rfl⟩ := call
 exact (checked.captureStable clause member capture).1

theorem accessible (constructors : Constructors) (roles : Roles.RoleDecls) (parent : List Pattern) :
 Acc (Child constructors roles) parent := by
 generalize size : mass parent = n
 induction n using Nat.strongRecOn generalizing parent with
 | ind n ih =>
   apply Acc.intro
   intro child call
   exact ih (mass child) (by rw [←size]; exact child_mass call) child rfl

/-- A source-rule-derived well-founded relation for declaration computation.
It is not termination of the replacement journal or resolution scheduler. -/
theorem calls_wellFounded (constructors : Constructors) (roles : Roles.RoleDecls) :
 WellFounded (Child constructors roles) := ⟨accessible constructors roles⟩

theorem child_inputs_independent (checked : DeclarationChecked constructors roles declaration)
 (clause : Clause) (member : clause ∈ declaration.requirements) (first last : Nat → Pattern)
 (sameInputs : CapturesAgree declaration first last) :
 substArgs first (normalizeArgs clause.arguments) = substArgs last (normalizeArgs clause.arguments) :=
 substArgs_congr _ first last (fun name used => sameInputs name (checked.scope.1 clause member name used))

/-- Each output-only binder comes from a designated strictly smaller checked
call. The supplied Associated interpretation is arbitrary; no operational
readback, source realization or choice of selected declaration is assumed here. -/
theorem binder_producer (checked : DeclarationChecked constructors roles declaration)
 (associated : Associated) (capture : Nat → Pattern)
 (outputs : SatisfiesOutputs associated declaration capture)
 (name : Nat) (member : name ∈ declaration.outputNames) :
 ∃ clause ∈ declaration.requirements, ∃ equation ∈ clause.outputs,
 equation.rhs = .var name ∧
 mass (substArgs capture clause.arguments) < mass (substArgs capture declaration.head) ∧
 capture name = associated clause.role (substArgs capture (normalizeArgs clause.arguments)) equation.name := by
 obtain ⟨binder,present,same⟩ := List.mem_map.mp member
 obtain ⟨clause,child,_,equation,equationMember,_,producer⟩ := checked.produced binder present
 have value := outputs clause child equation equationMember
 rw [producer,Pattern.subst] at value
 refine ⟨clause,child,equation,equationMember,?_,(checked.captureStable clause child capture).1,?_⟩
 · simpa only [same] using producer
 · simpa only [same] using value
end Yulang.GeneralDeclarationProducerRank253
