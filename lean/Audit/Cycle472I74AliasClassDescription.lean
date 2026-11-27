import Yulang.GeneralDeclarativeI65I74AliasClassDescription472

namespace Yulang.GeneralDeclarativeI65.I72.ObservationAliasHead472.Audit
open ObservationRawAlias471 (ClassWire)
open GeneralNominalCenteredHeadMatExpressions (Expr)

private def raw (label : Nat) : GeneralDeclarativeHead320.State :=
  ⟨⟨[],[(7,8),(8,7)]⟩,[⟨7,.record 40 (.variable 7) (.primitive .emptyRecord [])⟩,
    ⟨8,.record label (.variable 8) (.primitive .emptyRecord [])⟩,⟨7,.variable 8⟩,⟨3,.variable 5⟩]⟩

private def cut : List410.ExactEscapeWire :=
  ⟨(List.range 10).map (fun i => if i == 7 || i == 8 then 1 else 0),[1,0]⟩

private def c7 : ClassWire := ⟨[(7,.same),(8,.forward 2)],cut⟩
private def c8 : ClassWire := ⟨[(8,.same),(7,.backward 2)],cut⟩

theorem actual_same_alias_class_reads_both_definitions_only_after_same_constructor_check :
    (readExactOwner (raw 40) [(7,c7),(8,c8)] 7 0 c7).isSome = true ∧
    (readExactOwner (raw 40) [(7,c7),(8,c8)] 7 1 c7).isSome = true ∧
    (readExactOwner (raw 41) [(7,c7),(8,c8)] 7 1 c7).isNone = true ∧
    (readExactOwner (raw 40) [] 7 1 c7).isNone = true := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩

#print axioms checked_alias_really_links_old_names
#print axioms checks_shape_is_literal_old_alias_congruence
#print axioms every_same_ordinary_fit_interprets_that_actual_owner_at_the_named_point
#print axioms actual_same_alias_class_reads_both_definitions_only_after_same_constructor_check
end Yulang.GeneralDeclarativeI65.I72.ObservationAliasHead472.Audit
