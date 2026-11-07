import Yulang.CommonRoleWhereObstructions
import Yulang.CommonRoleAssociatedExactness

/-!
# The associated-head amendment does not determine where dictionaries

The registry is checked, satisfies the approved HeadDeterminesAssociated
condition, and has actual successful dictionary elaborations at two finite
ground goals. Their Common interpretations are equivalent, but their full
plans differ in the selected where-child implementation.

An exact extension preserving the existing full dictionaries cannot identify
those goals while retaining unique dictionary selection. This is not a
claim about nontermination or a negative result for bare role-status checking.
-/

namespace Yulang.CommonRoleWhereExactness

open CommonRoleAssociatedObstructions (Pattern groundHead)
open CommonRoleAssociatedExactness (Ground interpret)
open CommonRoleWhereObstructions
open RoleDictionaries (Plan)

def finiteGoal (argument : Pattern) : Roles.Goal := ⟨0, [argument.encode]⟩

/-- Preserve the real elaborator's complete successful dictionary outputs,
including each recursively selected implementation. -/
def PreservesComputedDictionary (select : Pattern → Option Plan) : Prop :=
  ∀ argument plan, Ground argument →
    RoleDictionaries.elaborate visible declarations_wellFormed (finiteGoal argument) =
      .resolved plan → select argument = some plan

/-- The same visible registry, role identity and Common argument type must
give the same complete dictionary. This compares only successful results. -/
def CommonExtensionalDictionary (select : Pattern → Option Plan) : Prop :=
  ∀ first last, Ground first → Ground last →
    Common.Equivalent (interpret first) (interpret last) →
    ∀ a b, select first = some a → select last = some b → a = b

/-- No function on finite descriptions can preserve both actual successful
dictionary elaborations and make dictionary selection respect Common equality.
All associated RHSs in this example are int, so the approved associated-head
amendment holds and does not exclude either witness. -/
theorem no_common_dictionary_registry_extension :
    ¬ ∃ select : Pattern → Option Plan,
      PreservesComputedDictionary select ∧ CommonExtensionalDictionary select := by
  rintro ⟨select, preserves, extensional⟩
  have first := preserves (groundHead .int) intPlan
    ⟨True.intro, True.intro, True.intro⟩ actual_int_elaboration
  have last := preserves (groundHead .bool) boolPlan
    ⟨True.intro, True.intro, True.intro⟩ actual_bool_elaboration
  exact plans_differ (extensional (groundHead .int) (groundHead .bool)
    ⟨True.intro, True.intro, True.intro⟩ ⟨True.intro, True.intro, True.intro⟩
    root_goals_equivalent intPlan boolPlan first last)

/-- A counterexample with all amended declaration premises discharged,
including the new check at declaration time and the independent old signature
and associated-body checks. Neither success nor head determination is supplied
as a free input to this theorem. -/
theorem amended_registry_counterexample :
    declarations.all CommonRoleHeadDetermination.Declaration.check = true ∧
    Roles.WellFormed visible ∧
    Roles.AssocWellFormed environment roles ∧
    CommonRoleHeadDetermination.RegistryHeadDeterminesAssociated declarations ∧
    Ground (groundHead .int) ∧ Ground (groundHead .bool) ∧
    ¬ ∃ select : Pattern → Option Plan,
      PreservesComputedDictionary select ∧ CommonExtensionalDictionary select :=
  ⟨combined_declaration_check_accepts, declarations_wellFormed, associated_wellFormed,
    head_determines_associated, ⟨True.intro, True.intro, True.intro⟩,
    ⟨True.intro, True.intro, True.intro⟩, no_common_dictionary_registry_extension⟩

end Yulang.CommonRoleWhereExactness
