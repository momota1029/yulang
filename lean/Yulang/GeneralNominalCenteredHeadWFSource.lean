import Yulang.GeneralNominalCenteredHeadStepCanonicalExecutor

set_option backward.isDefEq.respectTransparency false

/-! Constructor interpretation coverage for every application in source
declarations and role defaults. Unused catalogue entries are unrestricted.
Defaults use resolved source constructor names, not the pattern count encoding. -/
namespace Yulang.GeneralNominalCenteredHeadWFSource
open GeneralDeclarations GeneralDeclarationPatterns GeneralRegistryReordering
open GeneralNominalInspection (Interpretation)

def ConstructorUse (catalogue : Constructors) (interpretation : Interpretation)
    (name arity : Nat) : Prop :=
  ∃ declaration, catalogue name = some declaration ∧ declaration.parameters.length = arity ∧
    ((∃ primitive, interpretation.primitives name = some primitive ∧
      declaration.parameters = primitive.parameters) ∨
    (interpretation.invariantNominal name = true ∧ declaration.parameters = List.replicate arity .type))

mutual
  def PatternCovered (catalogue : Constructors) (interpretation : Interpretation) : Pattern → Prop
    | .var _ => True
    | .app name arguments => ConstructorUse catalogue interpretation name arguments.length ∧
        PatternsCovered catalogue interpretation arguments
    | .record _ payload tail => PatternCovered catalogue interpretation payload ∧ PatternCovered catalogue interpretation tail
    | .variant _ payload => PatternCovered catalogue interpretation payload
    | .join first last => PatternCovered catalogue interpretation first ∧ PatternCovered catalogue interpretation last
  def PatternsCovered (catalogue : Constructors) (interpretation : Interpretation) : List Pattern → Prop
    | [] => True
    | first :: rest => PatternCovered catalogue interpretation first ∧ PatternsCovered catalogue interpretation rest
end

mutual
  def TermCovered (catalogue : Constructors) (interpretation : Interpretation) : Roles.Term → Prop
    | .var _ => True
    | .app name arguments => ConstructorUse catalogue interpretation name arguments.length ∧
        TermsCovered catalogue interpretation arguments
  def TermsCovered (catalogue : Constructors) (interpretation : Interpretation) : List Roles.Term → Prop
    | [] => True
    | first :: rest => TermCovered catalogue interpretation first ∧ TermsCovered catalogue interpretation rest
end

def DeclarationCovered (catalogue : Constructors) (interpretation : Interpretation) (declaration : Declaration) : Prop :=
  PatternsCovered catalogue interpretation declaration.head ∧
    (∀ clause ∈ declaration.requirements, PatternsCovered catalogue interpretation clause.arguments ∧
      ∀ equation ∈ clause.outputs, PatternCovered catalogue interpretation equation.rhs) ∧
    ∀ equation ∈ declaration.associated, PatternCovered catalogue interpretation equation.rhs

def DefaultsCovered (catalogue : Constructors) (interpretation : Interpretation) (roles : Roles.RoleDecls) : Prop :=
  ∀ role name body, (roles role).assoc name = some (some body) → TermCovered catalogue interpretation body

def Coverage (registry : Registry) (interpretation : Interpretation) : Prop :=
  (∀ declaration ∈ registry.declarations, DeclarationCovered registry.constructors interpretation declaration) ∧
    DefaultsCovered registry.constructors interpretation registry.roles

theorem constructor_arity (covered : ConstructorUse catalogue interpretation name arity) :
    ∃ declaration, catalogue name = some declaration ∧ declaration.parameters.length = arity := by
  obtain ⟨declaration,present,arityEq,_⟩ := covered
  exact ⟨declaration,present,arityEq⟩

theorem constructor_interpreted (covered : ConstructorUse catalogue interpretation name arity) :
    (∃ primitive, interpretation.primitives name = some primitive) ∨ interpretation.invariantNominal name = true := by
  obtain ⟨_,_,_,⟨primitive,found,_⟩ | ⟨nominal,_⟩⟩ := covered
  · exact Or.inl ⟨primitive,found⟩
  · exact Or.inr nominal

mutual
  theorem pattern_scoped (covered : PatternCovered catalogue interpretation pattern) : WellScoped catalogue pattern := by
    cases pattern with
    | var => trivial
    | app name arguments => exact ⟨constructor_arity covered.1,patterns_scoped covered.2⟩
    | record label payload tail => exact ⟨pattern_scoped covered.1,pattern_scoped covered.2⟩
    | variant tag payload => exact pattern_scoped (pattern := payload) covered
    | join first last => exact ⟨pattern_scoped covered.1,pattern_scoped covered.2⟩
  theorem patterns_scoped (covered : PatternsCovered catalogue interpretation patterns) : ArgsWellScoped catalogue patterns := by
    cases patterns with
    | nil => trivial
    | cons first rest => exact ⟨pattern_scoped covered.1,patterns_scoped covered.2⟩
end

theorem declaration_scoped (covered : DeclarationCovered catalogue interpretation declaration) :
    declaration.ConstructorScoped catalogue :=
  ⟨patterns_scoped covered.1,
    fun clause member => ⟨patterns_scoped (covered.2.1 clause member).1,
      fun equation present => pattern_scoped ((covered.2.1 clause member).2 equation present)⟩,
    fun equation present => pattern_scoped (covered.2.2 equation present)⟩

theorem default_covered (covered : Coverage registry interpretation)
    (declared : (registry.roles role).assoc name = some (some body)) :
    TermCovered registry.constructors interpretation body := covered.2 role name body declared

theorem declaration_reorders (order : DeclarationReorders first last) :
    DeclarationCovered catalogue interpretation first ↔ DeclarationCovered catalogue interpretation last := by
  unfold DeclarationCovered
  rw [order.head,order.associated]
  constructor
  · exact fun covered => ⟨covered.1,fun clause member => covered.2.1 clause (order.requirements.mem_iff.mpr member),covered.2.2⟩
  · exact fun covered => ⟨covered.1,fun clause member => covered.2.1 clause (order.requirements.mem_iff.mp member),covered.2.2⟩

theorem coverage_reorders (order : Reorders first last) (covered : Coverage first interpretation) : Coverage last interpretation := by
  constructor
  · intro declaration member
    obtain ⟨prior,visible,pair⟩ := reorders_visible_back order declaration member
    rw [← order.1]
    exact (declaration_reorders pair).mp (covered.1 prior visible)
  · rw [← order.1,← order.2.1]
    exact covered.2

end Yulang.GeneralNominalCenteredHeadWFSource
