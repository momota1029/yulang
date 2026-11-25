import Yulang.GeneralDeclarativeI65I74RoleDefaultMeaning420

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RoleDefault420
open GeneralDeclarativeI65
open GeneralDictionaryAssociatedProvenance (Body)

/-- The lexical environment of a default body depends only on the request's
ordered arguments. Different pre-output frames cannot invent a different
typed default tree once the original B6 occurrence address is fixed. -/
theorem same_original_default_plan_has_same_wire420
    {s : GeneralDeclarativeI65.State} {q : Request} {atlas : B6OccurrenceAtlas401 s}
    {f g : AuthoredBodyFrame393 s q} {i : Fin q.demand.outputs.length}
    {role name : Nat} {term : Roles.Term}
    (a : NamedMixedOutput401 atlas f i) (b : NamedMixedOutput401 atlas g i)
    (sameOrdinal : f.ordinal = g.ordinal)
    (one : a.body = .default role name term) (two : b.body = .default role name term) :
    Check408.encodeRhs a.rhs = Check408.encodeRhs b.rhs := by
  rcases a with ⟨body,_,plan,left,value,formed⟩
  rcases b with ⟨other,_,plan',right,value',formed'⟩
  dsimp only at one two ⊢
  subst body
  subst other
  have same : plan = plan' := Option.some.inj (left.symm.trans (sameOrdinal ▸ right))
  subst plan'
  have exactValue : value = value' := Option.some.inj (formed.symm.trans formed')
  rw [exactValue]

end Yulang.GeneralDeclarativeI65.I72.RoleDefault420
