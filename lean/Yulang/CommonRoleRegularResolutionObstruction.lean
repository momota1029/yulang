import Yulang.CommonRoleActualEvidence
import Yulang.CommonRoleRegularUndecidability

/-!
# The amended B4 regular-resolution contract is not decidable

This final boundary reads the actual stored declaration head, where list and
associated RHSs. Its only interpretation is the fixed int/pair/variant grammar.
All Common substitutions are quantified, including arbitrary recursive types
and rows. The concrete finite input format and ordinary tape computation are
fixed, and no solver-success, fuel, safety or termination premise is assumed.
-/

namespace Yulang.CommonRoleRegularResolutionObstruction

open CommonRoleComputation (Code Tree Halts)
open CommonRoleLinearClock (Pattern)
open CommonRoleActualEvidence (interpretTerm Dictionary Derives)
open CommonRoleRegularRegistry (registry environment roles)
open CommonRoleRegularWire (startGoal queryWire)
open CommonRoleTuringBridge (Machine Runs)
open CommonRoleTuringDelimited (initial)

/-- The approved semantic condition, applied to the actual stored head/RHS
fields. Head correspondence is pointwise Common equivalence under arbitrary
Common substitutions. Every RHS must have corresponding equivalent values. -/
def AssociatedDetermined (implementation : Roles.AssocImpl) : Prop :=
  ∀ σ τ : Nat → Common.Ty,
    (∀ term ∈ implementation.impl.head, ∃ first last,
      interpretTerm term σ = some first ∧ interpretTerm term τ = some last ∧
        Common.Equivalent first last) →
    ∀ name rhs, (name, rhs) ∈ implementation.assoc → ∃ first last,
      interpretTerm rhs σ = some first ∧ interpretTerm rhs τ = some last ∧
        Common.Equivalent first last

def HeadDeterminesAssociated (declarations : Roles.AssocEnv) : Prop :=
  ∀ implementation ∈ declarations.impls, AssociatedDetermined implementation

/-- This finite, decidable sufficient test reads the actual associated fields.
It is intentionally incomplete; its soundness is the needed declaration gate. -/
def checkAssociated (implementation : Roles.AssocImpl) : Bool :=
  implementation.assoc.all (fun body => decide (body.2 = Pattern.int.encode))

theorem checkAssociated_sound (implementation : Roles.AssocImpl)
    (accepted : checkAssociated implementation = true) : AssociatedDetermined implementation := by
  intro σ τ _ name rhs member
  have same : rhs = Pattern.int.encode :=
    of_decide_eq_true ((List.all_eq_true.mp accepted) (name, rhs) member)
  subst rhs
  exact ⟨.base .int, .base .int, rfl, rfl, Common.equivalent_refl _⟩

def checkEnvironment (declarations : Roles.AssocEnv) : Bool :=
  declarations.impls.all (fun implementation =>
    CheckedRoles.checkImpl implementation.impl && checkAssociated implementation)

theorem checkEnvironment_sound (declarations : Roles.AssocEnv)
    (accepted : checkEnvironment declarations = true) :
    Roles.WellFormed declarations.cores ∧ HeadDeterminesAssociated declarations := by
  have each := List.all_eq_true.mp accepted
  constructor
  · intro implementation member
    obtain ⟨annotated, present, rfl⟩ := List.mem_map.mp member
    exact (CheckedRoles.checkImpl_exact _).mp (Bool.and_eq_true_iff.mp (each annotated present)).1
  · intro implementation member
    exact checkAssociated_sound implementation (Bool.and_eq_true_iff.mp (each implementation member)).2

theorem environment_checked (code : Code) : checkEnvironment (environment code) = true := by
  apply List.all_eq_true.mpr
  intro implementation member
  obtain ⟨core, present, rfl⟩ := List.mem_map.mp member
  have checked := (CheckedRoles.checkImpl_exact core).mpr
    (CommonRoleRegularRegistry.declarations_wellFormed code core present)
  simpa [CommonRoleRegularRegistry.annotate, checkAssociated] using checked

/-- No additional precondition: every generated actual finite declaration
environment passes the executable check and the independent signature checks. -/
theorem amended_preconditions (code : Code) :
    Roles.WellFormed (environment code).cores ∧
      HeadDeterminesAssociated (environment code) ∧ Roles.AssocWellFormed (environment code) roles :=
  ⟨(checkEnvironment_sound _ (environment_checked code)).1,
    (checkEnvironment_sound _ (environment_checked code)).2,
    CommonRoleRegularRegistry.associated_wellFormed code⟩

theorem associated_equations (code : Code) (implementation : Roles.AssocImpl)
    (member : implementation ∈ (environment code).impls)
    (name : Nat) (rhs : Roles.Term) (body : (name, rhs) ∈ implementation.assoc)
    (assignment : Nat → Common.Ty) :
    name = 0 ∧ interpretTerm rhs assignment = some (.base .int) := by
  obtain ⟨core, _, rfl⟩ := List.mem_map.mp member
  have pair : (name, rhs) = (0, Pattern.int.encode) := by
    simpa [CommonRoleRegularRegistry.annotate] using body
  cases pair
  exact ⟨rfl, rfl⟩

theorem actual_derives_exact (code : Code) (input : Tree) :
    Derives (environment code).cores (startGoal code input).eval ↔ Halts code input := by
  rw [CommonRoleRegularRegistry.environment_cores, CommonRoleRegularWire.startGoal_denotes]
  exact (CommonRoleActualEvidence.derives_iff_special _ _ _).trans
    (CommonRoleRegularHalting.derives_exact code input)

/-- The independent dictionary judgment reads actual Roles.Impl fields and
retains the complete existing RoleDictionaries.Plan. Every recursive child
uses the identical visible environment; candidate uniqueness is part of the
dictionary constructor and follows here without an extra assumption. -/
theorem actual_dictionary_exact (code : Code) (input : Tree) :
    Nonempty (Dictionary (environment code).cores (startGoal code input).eval) ↔ Halts code input := by
  rw [CommonRoleRegularRegistry.environment_cores, CommonRoleRegularWire.startGoal_denotes]
  exact (CommonRoleActualEvidence.dictionary_iff_special _ _ _).trans
    (CommonRoleRegularHalting.dictionary_exact code input)

/-- A necessary success-bit fragment of the full amended contract, on a
concrete subfamily of its verified declarations and finite regular goals.
Only finite input syntax is supplied to the machine. -/
def TotalActualResolver (machine : Machine) : Prop :=
  ∀ code input, ∃ final,
    Runs machine (initial (queryWire code input)) final ∧
      (final.current = true ↔
        Nonempty (Dictionary (environment code).cores (startGoal code input).eval))

/-- E2: no finite tape algorithm decides even success of the real finite
dictionary judgment for all these checked, associated-determined registries.
A total selection/rejection/ambiguity resolver would decide this success bit. -/
theorem no_total_actual_regular_resolver : ¬ ∃ machine : Machine, TotalActualResolver machine := by
  rintro ⟨machine, classifies⟩
  apply CommonRoleRegularUndecidability.no_total_regular_dictionary_classifier
  refine ⟨machine, ?_⟩
  intro code input
  obtain ⟨final, executed, correct⟩ := classifies code input
  exact ⟨final, executed, correct.trans ((actual_dictionary_exact code input).trans
    (CommonRoleRegularHalting.dictionary_exact code input).symm)⟩

/-- The counterfamily satisfies both amended declaration premises by a real
declaration check, and actual associated scope/completeness independently. -/
theorem amended_registry_undecidable :
    (∀ code, checkEnvironment (environment code) = true ∧
      Roles.WellFormed (environment code).cores ∧
      HeadDeterminesAssociated (environment code) ∧ Roles.AssocWellFormed (environment code) roles) ∧
      ¬ ∃ machine : Machine, TotalActualResolver machine :=
  ⟨fun code => ⟨environment_checked code, amended_preconditions code⟩,
    no_total_actual_regular_resolver⟩

end Yulang.CommonRoleRegularResolutionObstruction
