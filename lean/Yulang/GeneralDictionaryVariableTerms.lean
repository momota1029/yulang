import Yulang.GeneralDictionaryBinderLocations

/-!
# Explicit variable RHSs with unambiguous captured source identities

Output-only binders keep their existing interpretation. An input binder is
accepted only when both captured endpoint identities are literally equal.
Unequal intervals, compound terms and defaults remain deferred. This performs
no midpoint choice and does not establish correctness of the supplied capture.
-/
namespace Yulang.GeneralDictionaryVariableTerms
open GeneralDeclarations GeneralDeclarationPatterns GeneralDeclarationDemands
open GeneralDictionaryAssociatedProvenance (Body Supplies)
open GeneralDictionaryStateEquations
open GeneralDictionaryBinderLocations (Inputs locateTerm locateTerm_lifts)
open GeneralSourceState (State Demand Assignment Models)
open Core.PresenceGeneration (TyTerm)
variable {roles : Roles.RoleDecls} {state : State} {demand : Demand roles}

/-- Independent actual RHS provenance, with disjoint output and input cases. -/
def Denotes (roles : Roles.RoleDecls) (declaration : Declaration) (capture : Capture)
    (name : Nat) (term : TyTerm Nat) : Prop :=
  ∃ equation binder, Supplies roles declaration name (.explicit equation) ∧
    normalize equation.rhs = .var binder ∧
    ((binder ∈ declaration.outputNames ∧ term = .var (capture.outputs binder)) ∨
      (binder ∉ declaration.outputNames ∧ binder ∈ declaration.inputNames ∧
        (capture.inputs binder).1 = (capture.inputs binder).2 ∧
        term = .var (capture.inputs binder).1))

def bodyTerm (declaration : Declaration) (capture : Capture) : Body → Option (TyTerm Nat)
  | .explicit equation =>
    match normalize equation.rhs with
    | .var binder =>
      if binder ∈ declaration.outputNames then some (.var (capture.outputs binder))
      else if binder ∈ declaration.inputNames ∧
          (capture.inputs binder).1 = (capture.inputs binder).2 then
        some (.var (capture.inputs binder).1)
      else none
    | _ => none
  | .default _ _ _ => none

def lookup (roles : Roles.RoleDecls) (declaration : Declaration) (capture : Capture)
    (name : Nat) : Option (TyTerm Nat) :=
  (GeneralDictionaryAssociatedProvenance.lookup roles declaration name).bind (bodyTerm declaration capture)

private theorem bodyTerm_exact (declaration : Declaration) (capture : Capture)
    (body : Body) (term : TyTerm Nat) :
    bodyTerm declaration capture body = some term ↔
      ∃ equation binder, body = .explicit equation ∧ normalize equation.rhs = .var binder ∧
      ((binder ∈ declaration.outputNames ∧ term = .var (capture.outputs binder)) ∨
        (binder ∉ declaration.outputNames ∧ binder ∈ declaration.inputNames ∧
          (capture.inputs binder).1 = (capture.inputs binder).2 ∧
          term = .var (capture.inputs binder).1)) := by
  cases body with
  | default role name rhs => simp [bodyTerm]
  | explicit equation =>
    simp only [Body.explicit.injEq]
    unfold bodyTerm
    cases normalized : normalize equation.rhs <;> simp [normalized]
    next binder =>
      by_cases output : binder ∈ declaration.outputNames
      · simp [output, eq_comm]
      · by_cases input : binder ∈ declaration.inputNames <;>
          by_cases same : (capture.inputs binder).1 = (capture.inputs binder).2 <;>
          simp [output, input, same, eq_comm]

theorem lookup_exact (roles : Roles.RoleDecls) (declaration : Declaration) (capture : Capture)
    (unique : (declaration.associated.map Equation.name).Nodup) (name : Nat) (term : TyTerm Nat) :
    lookup roles declaration capture name = some term ↔ Denotes roles declaration capture name term := by
  unfold lookup Denotes
  rw [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨body, found, computed⟩
    obtain ⟨equation, binder, rfl, rhs, source⟩ := (bodyTerm_exact _ _ _ _).mp computed
    exact ⟨equation, binder,
      (GeneralDictionaryAssociatedProvenance.lookup_exact _ _ unique _ _).mp found, rhs, source⟩
  · rintro ⟨equation, binder, supplied, rhs, source⟩
    exact ⟨.explicit equation,
      (GeneralDictionaryAssociatedProvenance.lookup_exact _ _ unique _ _).mpr supplied,
      (bodyTerm_exact _ _ _ _).mpr ⟨equation, binder, rfl, rhs, source⟩⟩

/-- Existing successful output-only interpretation is preserved unchanged. -/
theorem output_lookup_preserved (roles : Roles.RoleDecls) (declaration : Declaration)
    (capture : Capture) (unique : (declaration.associated.map Equation.name).Nodup)
    (name : Nat) (term : TyTerm Nat)
    (found : GeneralDictionaryOutputBinderTerms.lookup roles declaration capture name = some term) :
    lookup roles declaration capture name = some term := by
  obtain ⟨equation, binder, supplied, rhs, output, same⟩ :=
    (GeneralDictionaryOutputBinderTerms.lookup_exact roles declaration capture unique name term).mp found
  exact (lookup_exact roles declaration capture unique name term).mpr
    ⟨equation, binder, supplied, rhs, Or.inl ⟨output, same⟩⟩

def Interpreted (declaration : Declaration) (capture : Capture) (located : Located state demand) : Prop :=
  ∀ index, lookup roles declaration capture (demand.outputs[index]).name =
    some (located.equations.output index)

def compile (state : State) (roles : Roles.RoleDecls) (declaration : Declaration)
    (capture : Capture) (name : Nat) : Option (TyTerm (Fin state.slots)) :=
  (lookup roles declaration capture name).bind (locateTerm state)

theorem compile_interpreted (state : State) (roles : Roles.RoleDecls) (declaration : Declaration)
    (capture : Capture) (name : Nat) (term : TyTerm (Fin state.slots))
    (found : compile state roles declaration capture name = some term) :
    lookup roles declaration capture name = some (liftType state term) := by
  obtain ⟨source, original, localized⟩ := Option.bind_eq_some_iff.mp found
  rw [locateTerm_lifts state source term localized]
  exact original

/-- All output occurrences are compiled; no output vector is an input. -/
def build (declaration : Declaration) (capture : Capture) (inputs : Inputs state demand) :
    Option (Located state demand) :=
  if complete : ∀ index : Fin demand.outputs.length,
      (compile state roles declaration capture (demand.outputs[index]).name).isSome = true then
    some { lower := inputs.lower
           upper := inputs.upper
           head := inputs.head
           target := inputs.target
           arguments := inputs.arguments
           targets := inputs.targets
           output := fun index => (compile state roles declaration capture (demand.outputs[index]).name).get (complete index) }
  else none

theorem build_interpreted (declaration : Declaration) (capture : Capture)
    (inputs : Inputs state demand) (located : Located state demand)
    (built : build declaration capture inputs = some located) : Interpreted declaration capture located := by
  unfold build at built
  split at built
  next complete =>
    cases built
    intro index
    apply compile_interpreted
    exact (Option.some_get (complete index)).symm
  next incomplete => cases built

theorem build_head (declaration : Declaration) (capture : Capture)
    (inputs : Inputs state demand) (located : Located state demand)
    (built : build declaration capture inputs = some located) : located.head = inputs.head := by
  unfold build at built
  split at built
  · cases built; rfl
  · cases built

theorem build_output_denotes (declaration : Declaration) (capture : Capture)
    (unique : (declaration.associated.map Equation.name).Nodup)
    (inputs : Inputs state demand) (located : Located state demand)
    (built : build declaration capture inputs = some located)
    (index : Fin demand.outputs.length) :
    Denotes roles declaration capture (demand.outputs[index]).name (located.equations.output index) :=
  (lookup_exact roles declaration capture unique _ _).mp
    (build_interpreted declaration capture inputs located built index)

theorem built_output_models (declaration : Declaration) (capture : Capture)
    (unique : (declaration.associated.map Equation.name).Nodup)
    (inputs : Inputs state demand) (located : Located state demand)
    (built : build declaration capture inputs = some located)
    (assignment : Assignment) (model : Models (GeneralDictionaryEquationRecording.record located) assignment)
    (index : Fin demand.outputs.length) :
    Denotes roles declaration capture (demand.outputs[index]).name (located.equations.output index) ∧
      Common.Equivalent (assignment (demand.outputs[index]).target).1
        ((located.equations.output index).eval Common.model assignment) := by
  exact ⟨build_output_denotes declaration capture unique inputs located built index,
    ((GeneralDictionaryEquationRecording.record_models located assignment).mp model).2.2 index⟩

end Yulang.GeneralDictionaryVariableTerms
