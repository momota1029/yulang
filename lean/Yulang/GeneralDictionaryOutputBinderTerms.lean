import Yulang.GeneralDictionaryAssociatedProvenance
import Yulang.GeneralDictionaryEquationRecording

/-!
# Actual explicit output-only RHS variables as ordinary source terms

This executable partial interpretation is grounded in real RHS provenance and
output-only capture identities. `none` means unsupported/deferred, not rejected.
It neither chooses an input interval centre nor interprets a positional default.
-/
namespace Yulang.GeneralDictionaryOutputBinderTerms
open GeneralDeclarations GeneralDeclarationPatterns GeneralDeclarationDemands
open GeneralDictionaryAssociatedProvenance (Body Supplies)
open GeneralSourceState (State Demand Assignment Models Output)
open GeneralDictionaryStateEquations
open Core.PresenceGeneration (TyTerm)

variable {roles : Roles.RoleDecls} {state : State} {demand : Demand roles}

/-- Independent, restricted interpretation of a real explicit equation. -/
def Denotes (roles : Roles.RoleDecls) (declaration : Declaration) (capture : Capture)
    (name : Nat) (term : TyTerm Nat) : Prop :=
  ∃ equation binder, Supplies roles declaration name (.explicit equation) ∧
    normalize equation.rhs = .var binder ∧ binder ∈ declaration.outputNames ∧
    term = .var (capture.outputs binder)

def bodyTerm (declaration : Declaration) (capture : Capture) : Body → Option (TyTerm Nat)
  | .explicit equation =>
    match normalize equation.rhs with
    | .var binder => if binder ∈ declaration.outputNames then some (.var (capture.outputs binder)) else none
    | _ => none
  | .default _ _ _ => none

def lookup (roles : Roles.RoleDecls) (declaration : Declaration) (capture : Capture)
    (name : Nat) : Option (TyTerm Nat) :=
  (GeneralDictionaryAssociatedProvenance.lookup roles declaration name).bind (bodyTerm declaration capture)

private theorem bodyTerm_exact (declaration : Declaration) (capture : Capture)
    (body : Body) (term : TyTerm Nat) :
    bodyTerm declaration capture body = some term ↔
      ∃ equation binder, body = .explicit equation ∧ normalize equation.rhs = .var binder ∧
        binder ∈ declaration.outputNames ∧ term = .var (capture.outputs binder) := by
  cases body with
  | default role name rhs => simp [bodyTerm]
  | explicit equation =>
    simp only [Body.explicit.injEq]
    unfold bodyTerm
    cases normalized : normalize equation.rhs <;> simp [normalized]
    next name =>
      by_cases member : name ∈ declaration.outputNames <;> simp [member, eq_comm]

/-- Exactness: every successful term comes from an actual explicit output binder,
and every such source equation is found. Associated-name uniqueness is explicit. -/
theorem lookup_exact (roles : Roles.RoleDecls) (declaration : Declaration) (capture : Capture)
    (unique : (declaration.associated.map Equation.name).Nodup) (name : Nat) (term : TyTerm Nat) :
    lookup roles declaration capture name = some term ↔ Denotes roles declaration capture name term := by
  unfold lookup Denotes
  rw [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨body, found, computed⟩
    obtain ⟨equation, binder, rfl, rhs, member, same⟩ := (bodyTerm_exact _ _ _ _).mp computed
    exact ⟨equation, binder, (GeneralDictionaryAssociatedProvenance.lookup_exact _ _ unique _ _).mp found,
      rhs, member, same⟩
  · rintro ⟨equation, binder, supplied, rhs, member, same⟩
    exact ⟨.explicit equation,
      (GeneralDictionaryAssociatedProvenance.lookup_exact _ _ unique _ _).mpr supplied,
      (bodyTerm_exact _ _ _ _).mpr ⟨equation, binder, rfl, rhs, member, same⟩⟩

theorem denotes_functional (roles : Roles.RoleDecls) (declaration : Declaration) (capture : Capture)
    (unique : (declaration.associated.map Equation.name).Nodup) (name : Nat)
    (first last : TyTerm Nat) (one : Denotes roles declaration capture name first)
    (two : Denotes roles declaration capture name last) : first = last :=
  Option.some.inj (((lookup_exact _ _ _ unique _ _).mpr one).symm.trans
    ((lookup_exact _ _ _ unique _ _).mpr two))

/-- A checked producer is an actual clause/output equation, not an invented role
projection. Its emitted target is precisely the computed RHS source identity. -/
theorem denotes_has_producer (checked : DeclarationChecked constructors roles declaration)
    (capture : Capture) (name : Nat) (term : TyTerm Nat)
    (denoted : Denotes roles declaration capture name term)
    (allocate : (clause : Clause) → Allocation roles clause) :
    ∃ clause, ∃ present : clause ∈ declaration.requirements, ∃ equation ∈ clause.outputs,
      term = .var (outputTarget declaration capture (allocate clause).outputs equation) ∧
      ⟨equation.name, outputTarget declaration capture (allocate clause).outputs equation⟩ ∈
        (childDemand declaration clause (checked.signature.2.2.2 clause present) capture (allocate clause)).outputs := by
  obtain ⟨_, binder, _, _, member, same⟩ := denoted
  obtain ⟨binding, bindingPresent, bindingName⟩ := List.mem_map.mp member
  obtain ⟨clause, present, _, equation, output, _, producer⟩ := checked.produced binding bindingPresent
  have target := generated_output_target declaration capture (allocate clause).outputs equation
    binding.name (List.mem_map.mpr ⟨binding, bindingPresent, rfl⟩) producer
  refine ⟨clause, present, equation, output, ?_, ?_⟩
  · rw [target, bindingName]; exact same
  · exact (child_outputs_exact _ _ _ _ _ _).mpr ⟨equation, output, rfl⟩

/-- Retain every occurrence and target, including failed interpretations. -/
def outputs (roles : Roles.RoleDecls) (declaration : Declaration) (capture : Capture)
    (demand : Demand roles) : List (Output × Option (TyTerm Nat)) :=
  demand.outputs.map fun output => (output, lookup roles declaration capture output.name)

theorem outputs_sources (roles : Roles.RoleDecls) (declaration : Declaration) (capture : Capture)
    (demand : Demand roles) : (outputs roles declaration capture demand).map Prod.fst = demand.outputs := by
  simp [outputs, List.map_map, Function.comp_def]

/-- No arbitrary output interpretation relation remains here. Head terms and
source slots are still inputs; successful lookup must hold at every occurrence. -/
def Interpreted (declaration : Declaration) (capture : Capture) (located : Located state demand) : Prop :=
  ∀ index, lookup roles declaration capture (demand.outputs[index]).name =
    some (located.equations.output index)

/-- All final models satisfy the *computed* actual RHS, after actual recording.
This does not assert that a final model exists. -/
theorem recorded_output_denotes (declaration : Declaration) (capture : Capture)
    (unique : (declaration.associated.map Equation.name).Nodup)
    (located : Located state demand) (interpreted : Interpreted declaration capture located)
    (assignment : Assignment) (model : Models (GeneralDictionaryEquationRecording.record located) assignment)
    (index : Fin demand.outputs.length) :
    Denotes roles declaration capture (demand.outputs[index]).name (located.equations.output index) ∧
      Common.Equivalent (assignment (demand.outputs[index]).target).1
        ((located.equations.output index).eval Common.model assignment) := by
  exact ⟨(lookup_exact _ _ _ unique _ _).mp (interpreted index),
    ((GeneralDictionaryEquationRecording.record_models located assignment).mp model).2.2 index⟩

/-- Source producer and root constraint are joined without assuming a generic
term-instance predicate. Producer selection/evidence is still a separate task. -/
theorem recorded_output_producer (checked : DeclarationChecked constructors roles declaration)
    (capture : Capture) (located : Located state demand)
    (interpreted : Interpreted declaration capture located)
    (allocate : (clause : Clause) → Allocation roles clause)
    (assignment : Assignment) (model : Models (GeneralDictionaryEquationRecording.record located) assignment)
    (index : Fin demand.outputs.length) :
    ∃ clause, ∃ present : clause ∈ declaration.requirements, ∃ equation ∈ clause.outputs,
      ⟨equation.name, outputTarget declaration capture (allocate clause).outputs equation⟩ ∈
        (childDemand declaration clause (checked.signature.2.2.2 clause present) capture (allocate clause)).outputs ∧
      Common.Equivalent (assignment (demand.outputs[index]).target).1
        (assignment (outputTarget declaration capture (allocate clause).outputs equation)).1 := by
  have result := recorded_output_denotes declaration capture checked.identified.2.2.1 located
    interpreted assignment model index
  obtain ⟨clause, present, equation, output, term, generated⟩ :=
    denotes_has_producer checked capture _ _ result.1 allocate
  refine ⟨clause, present, equation, output, generated, ?_⟩
  rw [term] at result
  exact result.2

end Yulang.GeneralDictionaryOutputBinderTerms
