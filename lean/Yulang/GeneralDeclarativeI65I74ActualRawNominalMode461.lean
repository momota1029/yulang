import Yulang.GeneralDeclarativeI65I74PreviousStabilityFactorization461

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
open Core.PresenceGeneration (TyTerm)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeGraphRows321 (shapeOf)
open GeneralDeclarativeK2Graph321 (Shape)
open InlineStructuralPolicy458 (policy)
open WrittenPattern460

theorem old_closed_record_native_cannot_supply_nominal_shape
    {t : TyTerm Nat} {e : Expr} {k args}
    (read : RecordTrail455.closedRecordTerm t = some e) :
    shapeOf e ≠ some (.nominal k args) := by
  cases t <;> try simp [RecordTrail455.closedRecordTerm] at read
  case emptyRecord =>
    subst e
    simp [shapeOf,GeneralDeclarativeK2Graph321.arguments]
  case record label payload tail =>
    cases payload <;> try simp [RecordTrail455.closedRecordTerm] at read
    case var index =>
      obtain ⟨rest,_,rfl⟩ := read
      simp only [shapeOf,ne_eq,Option.map_eq_some_iff]
      rintro ⟨xs,_,wrong⟩
      cases wrong

theorem actual_earlier_nominal_raw_hop_reads_the_same_declared_unary_operator
    {s : CoreState} {root e key i c q used}
    (step : AuthenticatedHop458.AtStep s.current.ordinary (policy s)
      root e (.nominal key i) c q used) :
    i = 0 ∧ InlineNominalPoint458.HasMode s key := by
  obtain ⟨row,_,sh,_,shape,child,authority⟩ := step
  have someChild := child
  cases child with
  | nominal raw _ =>
    cases used with
    | false =>
      change InlineStructuralPolicy458.allows s root row (.nominal key i) c false at authority
      obtain ⟨older,what⟩ := authority
      cases older with
      | true =>
        rcases what with ⟨⟨label,bad,_⟩,_⟩
        cases bad
      | false =>
        change (RoutedNominalPoint456.nominalOps s).allowed root row at what
        rcases what with (named|typed)
        · rcases named with recordShape|extraShape
          · obtain ⟨_,_,_,term,_,_,compiled⟩ := recordShape
            exact (old_closed_record_native_cannot_supply_nominal_shape compiled shape).elim
          · obtain ⟨_,_,_,_,_,_,exact⟩ := extraShape
            cases row
            cases exact <;> simp [shapeOf] at shape
        · obtain ⟨placed⟩ := typed
          have loc := RoutedNominalPoint456.literal_covariant_point_child_is_only_original_ordinal456
            placed shape someChild
          simp only [RecordTraversal455.MixedQA.Address.nominal.injEq] at loc
          obtain ⟨rfl,rfl⟩ := loc.1
          exact ⟨rfl,placed.use,placed.mode,placed.table⟩
    | true =>
      change InlineStructuralPolicy458.NewAuthority s root row (.nominal key i) c at authority
      rcases authority with pair|field|nominal
      · rcases pair.1 with ⟨_,_,bad⟩ | ⟨_,_,bad⟩ <;> cases bad
      · obtain ⟨label,bad,_⟩ := field
        cases bad
      · obtain ⟨k,t,same,_,modes,_,_,_⟩ := nominal
        cases same
        exact ⟨rfl,modes⟩

end Yulang.GeneralDeclarativeI65.I72.EligibleFieldStart461
