import Yulang.GeneralDeclarations

/-!
# Lossless child demands under an interval capture

Bare where clauses survive even when they have no named equations. Compound
inputs and named RHS expressions retain materialization requests; allocating
their source identities is not a proof that ordinary constraints realize them.
No candidate filtering, dictionary selection or resolver is used.
-/
namespace Yulang.GeneralDeclarationDemands

open GeneralDeclarationPatterns
open GeneralDeclarations
open GeneralSourceState (Demand Interval Output)

structure Capture where
  inputs : Nat → Interval
  /-- Ordinary identities reserved for output-only binders, not interval centres.
  Allocation freshness and sharing constraints are obligations for item 3. -/
  outputs : Nat → Nat

structure Allocation (roles : Roles.RoleDecls) (clause : Clause) where
  arguments : Fin (roles clause.role).arity → Interval
  outputs : Nat → Nat

def inputInterval (capture : Capture) (allocated : Interval) (pattern : Pattern) : Interval :=
  match normalize pattern with
  | .var name => capture.inputs name
  | _ => allocated

def outputTarget (declaration : Declaration) (capture : Capture) (allocate : Nat → Nat)
    (equation : Equation) : Nat :=
  match normalize equation.rhs with
  | .var name => if name ∈ declaration.outputNames then capture.outputs name else allocate equation.id
  | _ => allocate equation.id

def childDemand (declaration : Declaration) (clause : Clause) (valid : clause.Signature roles)
    (capture : Capture) (allocation : Allocation roles clause) : Demand roles where
  role := clause.role
  arguments := fun index => inputInterval capture (allocation.arguments index)
    (clause.arguments[index.val]'(by rw [valid.1]; exact index.isLt))
  outputs := clause.outputs.map fun equation =>
    ⟨equation.name, outputTarget declaration capture allocation.outputs equation⟩
  declared := by
    intro output member
    obtain ⟨equation, present, rfl⟩ := List.mem_map.mp member
    exact valid.2 equation present

structure InputRequest where
  position : Nat
  pattern : Pattern
  endpoints : Interval

structure OutputRequest where
  equation : Nat
  name : Nat
  pattern : Pattern
  target : Nat

structure Emission (roles : Roles.RoleDecls) where
  invocation : Nat
  declaration : Nat
  clause : Nat
  capture : Capture
  demand : Demand roles
  inputs : List InputRequest
  outputs : List OutputRequest

def emit (invocation : Nat) (declaration : Declaration) (clause : Clause)
    (valid : clause.Signature roles) (capture : Capture) (allocation : Allocation roles clause) : Emission roles :=
  let demand := childDemand declaration clause valid capture allocation
  { invocation := invocation
    declaration := declaration.id
    clause := clause.id
    capture := capture
    demand := demand
    inputs := List.ofFn fun index : Fin (roles clause.role).arity =>
      ⟨index.val, clause.arguments[index.val]'(by rw [valid.1]; exact index.isLt), demand.arguments index⟩
    outputs := clause.outputs.map fun equation =>
      ⟨equation.id, equation.name, equation.rhs, outputTarget declaration capture allocation.outputs equation⟩ }

def emitAll (invocation : Nat) (declaration : Declaration)
    (valid : declaration.Signature roles) (capture : Capture)
    (allocate : (clause : Clause) → Allocation roles clause) : List (Emission roles) :=
  declaration.requirements.attach.map fun clause =>
    emit invocation declaration clause.val (valid.2.2.2 clause.val clause.property) capture (allocate clause.val)

theorem emitAll_identities (invocation : Nat) (declaration : Declaration)
    (valid : declaration.Signature roles) (capture : Capture)
    (allocate : (clause : Clause) → Allocation roles clause) :
    (emitAll invocation declaration valid capture allocate).map
      (fun result => (result.invocation, result.declaration, result.clause)) =
        declaration.requirements.map (fun clause => (invocation, declaration.id, clause.id)) := by
  simp [emitAll, emit, List.map_map]

theorem emitAll_length (invocation : Nat) (declaration : Declaration)
    (valid : declaration.Signature roles) (capture : Capture)
    (allocate : (clause : Clause) → Allocation roles clause) :
    (emitAll invocation declaration valid capture allocate).length = declaration.requirements.length := by
  simp [emitAll]

theorem child_outputs_exact (declaration : Declaration) (clause : Clause)
    (valid : clause.Signature roles) (capture : Capture) (allocation : Allocation roles clause)
    (output : Output) :
    output ∈ (childDemand declaration clause valid capture allocation).outputs ↔
      ∃ equation ∈ clause.outputs, output =
        ⟨equation.name, outputTarget declaration capture allocation.outputs equation⟩ := by
  simp only [childDemand, List.mem_map]
  constructor <;> rintro ⟨equation, present, same⟩ <;> exact ⟨equation, present, same.symm⟩

theorem generated_output_target (declaration : Declaration) (capture : Capture) (allocate : Nat → Nat)
    (equation : Equation) (name : Nat) (generated : name ∈ declaration.outputNames)
    (rhs : equation.rhs = .var name) :
    outputTarget declaration capture allocate equation = capture.outputs name := by
  simp [outputTarget, rhs, normalize, generated]

/-- This checks source identity linkage only. The retained requests must also
be realized by item 3 before using the emitted child for classification. -/
theorem child_linked (state : GeneralSourceState.State) (declaration : Declaration) (clause : Clause)
    (valid : clause.Signature roles) (capture : Capture) (allocation : Allocation roles clause)
    (arguments : ∀ index, ∃ pair ∈ state.intervals,
      (state.source pair.1, state.source pair.2) =
        (childDemand declaration clause valid capture allocation).arguments index)
    (outputs : ∀ equation ∈ clause.outputs, ∃ slot,
      state.source slot = outputTarget declaration capture allocation.outputs equation) :
    GeneralSourceState.Linked state (childDemand declaration clause valid capture allocation) := by
  refine ⟨arguments, ?_⟩
  intro output member
  obtain ⟨equation, present, rfl⟩ := (child_outputs_exact declaration clause valid capture allocation output).mp member
  exact outputs equation present

/-- Conservative lazy applicability policy. Every unnamed role position waits,
including when no implementation is visible. Minimizing this set for wildcard
heads remains the documented owner question; this is not claimed minimal. -/
def needed (roles : Roles.RoleDecls) (demand : Demand roles) : GeneralSourceState.Needed demand :=
  fun index => index ∈ List.finRange (roles demand.role).arity

theorem every_input_needed (demand : Demand roles) (index : Fin (roles demand.role).arity) :
    needed roles demand index := List.mem_finRange index

theorem unknown_input_pending (state : GeneralSourceState.State) (demand : Demand roles)
    (index : Fin (roles demand.role).arity)
    (unknown : ¬ GeneralSourceState.Known state (demand.arguments index).1) :
    GeneralSourceState.RootPending state demand (needed roles demand) :=
  ⟨index, every_input_needed demand index, unknown⟩

end Yulang.GeneralDeclarationDemands
