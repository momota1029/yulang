import Yulang.GeneralRegistryReordering

/-!
# Associated RHS provenance for actual general declarations

Explicit implementation equations and role defaults have different syntaxes
and variable scopes. Retain that distinction rather than interpreting either
as an ordinary Common term. Lookup chooses explicit equations before defaults,
without matching a head, choosing an interval center, or invoking a resolver.
The output map retains each source occurrence and target, including repeats.
-/
namespace Yulang.GeneralDictionaryAssociatedProvenance
open GeneralDeclarations GeneralRegistryReordering
open GeneralSourceState (Demand Output)

/-- Explicit variables are declaration/capture names. Default variables remain
positional role parameters. Neither constructor performs substitution. -/
inductive Body where
  | explicit (equation : Equation)
  | default (role name : Nat) (rhs : Roles.Term)
  deriving Repr, DecidableEq

/-- Independent provenance judgment; explicit membership is not list lookup.
The default branch requires the absence of every explicit equation of this name. -/
inductive Supplies (roles : Roles.RoleDecls) (declaration : Declaration)
    (name : Nat) : Body → Prop where
  | explicit (equation : Equation) (present : equation ∈ declaration.associated)
      (named : equation.name = name) : Supplies roles declaration name (.explicit equation)
  | default (rhs : Roles.Term)
      (absent : ∀ equation ∈ declaration.associated, equation.name ≠ name)
      (declared : (roles declaration.role).assoc name = some (some rhs)) :
      Supplies roles declaration name (.default declaration.role name rhs)

def lookup (roles : Roles.RoleDecls) (declaration : Declaration) (name : Nat) : Option Body :=
  match declaration.associated.find? (fun equation => equation.name == name) with
  | some equation => some (.explicit equation)
  | none => ((roles declaration.role).assoc name).join.map (.default declaration.role name)

private theorem find_exact (equations : List Equation)
    (unique : (equations.map Equation.name).Nodup) (name : Nat) (equation : Equation) :
    equations.find? (fun equation => equation.name == name) = some equation ↔
      equation ∈ equations ∧ equation.name = name := by
  induction equations with
  | nil => simp
  | cons first rest ih =>
    have pair := List.nodup_cons.mp unique
    by_cases same : first.name = name
    · simp only [List.find?, same, beq_self_eq_true, Option.some.injEq]
      constructor
      · intro equal; subst equation; exact ⟨by simp, same⟩
      · rintro ⟨present, named⟩
        rcases List.mem_cons.mp present with equal | member
        · exact equal.symm
        · exact False.elim (pair.1 (List.mem_map.mpr ⟨equation, member, named.trans same.symm⟩))
    · have different : (first.name == name) = false := by simp [same]
      simp only [List.find?, different]
      rw [ih pair.2]
      constructor
      · rintro ⟨member, named⟩; exact ⟨List.mem_cons_of_mem _ member, named⟩
      · rintro ⟨present, named⟩
        rcases List.mem_cons.mp present with equal | member
        · subst equation; exact False.elim (same named)
        · exact ⟨member, named⟩

private theorem find_none (equations : List Equation) (name : Nat) :
    equations.find? (fun equation => equation.name == name) = none ↔
      ∀ equation ∈ equations, equation.name ≠ name := by
  simp [List.find?_eq_none]

/-- Executable lookup is exactly the independent provenance judgment. Only
associated-name uniqueness is needed, not a candidate or model assumption. -/
theorem lookup_exact (roles : Roles.RoleDecls) (declaration : Declaration)
    (unique : (declaration.associated.map Equation.name).Nodup) (name : Nat) (body : Body) :
    lookup roles declaration name = some body ↔ Supplies roles declaration name body := by
  constructor
  · intro found
    unfold lookup at found
    split at found
    next equation selected =>
      have pair := (find_exact _ unique name equation).mp selected
      cases found
      exact .explicit equation pair.1 pair.2
    next selected =>
      have absent := (find_none _ name).mp selected
      cases declared : (roles declaration.role).assoc name with
      | none => simp [declared] at found
      | some value =>
        cases value with
        | none => simp [declared] at found
        | some rhs =>
          simp [declared] at found
          subst body
          exact .default rhs absent declared
  · intro supplied
    cases supplied with
    | explicit equation present named =>
      simp [lookup, (find_exact _ unique name equation).mpr ⟨present, named⟩]
    | default rhs absent declared =>
      simp [lookup, (find_none _ name).mpr absent, declared]

/-- Every declared name is supplied by the implementation or its role default.
This is syntactic coverage, not evaluation or ordinary-constraint entailment. -/
theorem declared_covered (roles : Roles.RoleDecls) (declaration : Declaration)
    (signature : declaration.Signature roles) (name : Nat)
    (declared : ∃ value, (roles declaration.role).assoc name = some value) :
    ∃ body, Supplies roles declaration name body := by
  classical
  by_cases explicit : ∃ equation ∈ declaration.associated, equation.name = name
  · obtain ⟨equation, present, named⟩ := explicit
    exact ⟨_, .explicit equation present named⟩
  · obtain ⟨value, present⟩ := declared
    have coverage := signature.2.2.1 name value present
    rcases coverage with supplied | defaulted
    · exact False.elim (explicit supplied)
    · cases value with
      | none => simp at defaulted
      | some rhs =>
        refine ⟨_, .default rhs ?_ present⟩
        intro equation member named
        exact explicit ⟨equation, member, named⟩

theorem supplies_unique (roles : Roles.RoleDecls) (declaration : Declaration)
    (unique : (declaration.associated.map Equation.name).Nodup) (name : Nat)
    (first last : Body) (one : Supplies roles declaration name first)
    (two : Supplies roles declaration name last) : first = last := by
  exact Option.some.inj (((lookup_exact roles declaration unique name first).mpr one).symm.trans
    ((lookup_exact roles declaration unique name last).mpr two))

/-- Reordering where clauses does not alter either the selected explicit RHS or
its fallback default. Roles and their positional binder conventions stay fixed. -/
theorem lookup_reorders (roles : Roles.RoleDecls) (order : DeclarationReorders first last)
    (name : Nat) : lookup roles first name = lookup roles last name := by
  simp only [lookup, order.associated, order.role]

theorem supplies_reorders (roles : Roles.RoleDecls) (order : DeclarationReorders first last)
    (name : Nat) (body : Body) : Supplies roles first name body ↔ Supplies roles last name body := by
  constructor
  · intro supplied
    cases supplied with
    | explicit equation present named =>
      exact .explicit equation (order.associated ▸ present) named
    | default rhs absent declared =>
      have absent' : ∀ equation ∈ last.associated, equation.name ≠ name := order.associated ▸ absent
      have declared' : (roles last.role).assoc name = some (some rhs) := order.role ▸ declared
      simpa only [order.role] using Supplies.default rhs absent' declared'
  · intro supplied
    cases supplied with
    | explicit equation present named =>
      exact .explicit equation (order.associated.symm ▸ present) named
    | default rhs absent declared =>
      have absent' : ∀ equation ∈ first.associated, equation.name ≠ name := order.associated.symm ▸ absent
      have declared' : (roles first.role).assoc name = some (some rhs) := order.role.symm ▸ declared
      simpa only [order.role] using Supplies.default rhs absent' declared'

/-- Keep failed lookups and the complete original output, not just its name.
No occurrence is deduplicated or silently omitted. -/
def outputs (roles : Roles.RoleDecls) (declaration : Declaration) (demand : Demand roles) :
    List (Output × Option Body) :=
  demand.outputs.map fun output => (output, lookup roles declaration output.name)

theorem outputs_length (roles : Roles.RoleDecls) (declaration : Declaration) (demand : Demand roles) :
    (outputs roles declaration demand).length = demand.outputs.length := by simp [outputs]

theorem outputs_sources (roles : Roles.RoleDecls) (declaration : Declaration) (demand : Demand roles) :
    (outputs roles declaration demand).map Prod.fst = demand.outputs := by simp [outputs, List.map_map, Function.comp_def]

theorem outputs_at (roles : Roles.RoleDecls) (declaration : Declaration) (demand : Demand roles)
    (index : Fin demand.outputs.length) :
    (outputs roles declaration demand)[index.val]'(by simp [outputs]) =
      (demand.outputs[index.val], lookup roles declaration (demand.outputs[index.val]).name) := by
  simp [outputs]

theorem outputs_complete (registry : Registry) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors registry.roles declaration)
    (demand : Demand registry.roles) (role : declaration.role = demand.role)
    (output : Output) (present : output ∈ demand.outputs) :
    ∃ body, (output, some body) ∈ outputs registry.roles declaration demand ∧
      Supplies registry.roles declaration output.name body := by
  have declared := demand.declared output present
  rw [← role] at declared
  obtain ⟨body, supplied⟩ := declared_covered registry.roles declaration checked.signature output.name declared
  refine ⟨body, ?_, supplied⟩
  apply List.mem_map.mpr
  refine ⟨output, present, ?_⟩
  simp only [(lookup_exact registry.roles declaration checked.identified.2.2.1 output.name body).mpr supplied]

theorem outputs_reorders (roles : Roles.RoleDecls) (order : DeclarationReorders first last)
    (demand : Demand roles) : outputs roles first demand = outputs roles last demand := by
  unfold outputs
  congr 1
  funext output
  rw [lookup_reorders roles order]

end Yulang.GeneralDictionaryAssociatedProvenance
