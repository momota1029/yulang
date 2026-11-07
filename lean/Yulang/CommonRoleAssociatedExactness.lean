import Yulang.CommonRoleAssociatedObstructions

/-!
# No associated-evidence-preserving Common resolver under the current checks

This module extracts a necessary condition of B4, rather than replacing B4 by
a new same-named theorem. The finite record declaration and both witnesses
come from `CommonRoleAssociatedObstructions`. The obstruction preserves the actual
`Roles.assocOf` computation on two already accepted ground queries. Their
finite type arguments are interpreted in Common using the specified record
semantics. The companion module also constructs the existing independent
`Roles.AssocDerives` judgments and the actual dictionaries.

Even preserving these two old independent derivations is incompatible with
selecting one associated value per determined Common goal. This does not
assert that bare role success is undecidable, or that all finite qualified
constraint generation is impossible.
-/

namespace Yulang.CommonRoleAssociatedExactness

open CommonRoleAssociatedObstructions
open Common (Ty Equivalent)

def Ground : Pattern → Prop
  | .var _ => False
  | .int | .bool | .empty => True
  | .record _ payload rest => Ground payload ∧ Ground rest

def interpret (pattern : Pattern) : Ty := pattern.eval (fun _ => .bottom)

/-- Preserve the actual associated-type computation on ground finite queries
already accepted by the existing resolver. The computed RHS is explicit in
the premise; no transported Common evidence is assumed here. -/
def PreservesComputedAssociated (select : Pattern → Option Ty) : Prop :=
  ∀ hidden value, Ground hidden →
    Roles.assocOf environment roles declaration_wellFormed (rigidGoal hidden) 0 =
      some value.encode →
    ∃ selected, select (groundHead hidden) = some selected ∧
      Equivalent selected (interpret value)

/-- The specified semantic equality of goal arguments must also be respected
by the uniquely determined associated result of the same selected impl.
Only already-successful ground queries are compared. -/
def CommonExtensional (select : Pattern → Option Ty) : Prop :=
  ∀ first last, Ground first → Ground last →
    Equivalent (interpret first) (interpret last) →
    ∀ a b, select first = some a → select last = some b → Equivalent a b

/-- No extension of the *real* associated resolver to Common can both
preserve its computed results on the finite ground fragment and respect
Common equality. This uses only two successful queries, one checked impl,
one declared associated name, no where recursion and no arbitrary decoder.

The two contract clauses have separate sources: preservation of existing
associated evidence/computation, and spec 4.3/6.3 semantic type equality plus
head arguments determining one associated type. Neither is inferred just
from the ordinary equation-append law. -/
theorem no_common_associated_registry_extension :
    ¬ ∃ select : Pattern → Option Ty,
      PreservesComputedAssociated select ∧ CommonExtensional select := by
  rintro ⟨select, preserves, extensional⟩
  obtain ⟨first, firstSelected, firstMeaning⟩ :=
    preserves .int .int True.intro (first_order_associated .int)
  obtain ⟨last, lastSelected, lastMeaning⟩ :=
    preserves .bool .bool True.intro (first_order_associated .bool)
  have equalHeads : Equivalent (interpret (groundHead .int)) (interpret (groundHead .bool)) :=
    Common.equivalent_trans (ground_head_equivalent .int _)
      (Common.equivalent_symm (ground_head_equivalent .bool _))
  have same : Equivalent first last := extensional (groundHead .int) (groundHead .bool)
    ⟨True.intro, True.intro, True.intro⟩ ⟨True.intro, True.intro, True.intro⟩
    equalHeads first last firstSelected lastSelected
  exact int_not_bool (Common.equivalent_trans (Common.equivalent_symm firstMeaning)
    (Common.equivalent_trans same lastMeaning))

/-- The independent current declaration conditions and finite ground domain
hold for the counterexample; they are not hypotheses assumed of a caller. -/
theorem checked_registry_counterexample :
    CheckedRoles.checkDatabase environment.cores = true ∧
    Roles.WellFormed environment.cores ∧
    Roles.AssocWellFormed environment roles ∧
    Ground (groundHead .int) ∧ Ground (groundHead .bool) ∧
    ¬ ∃ select : Pattern → Option Ty,
      PreservesComputedAssociated select ∧ CommonExtensional select :=
  ⟨declaration_accepted, declaration_wellFormed, associated_wellFormed,
    ⟨True.intro, True.intro, True.intro⟩, ⟨True.intro, True.intro, True.intro⟩,
    no_common_associated_registry_extension⟩

end Yulang.CommonRoleAssociatedExactness
