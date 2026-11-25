import Yulang.GeneralDeclarativeI65I73RuleUnionPriority407

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Result Tree Summarizes)

/-- The repeated-only rule is already a genuine source case of the
where rule: a literal empty where list needs no variable child
or output placement to be manufactured. All event indices are unchanged. -/
theorem repeated_local_already_in_where407 {s q e needs}
    (old : repeatedSource403.elected s q e needs) :
    variableWhereSource403.elected s q e needs := by
  obtain ⟨empty,⟨read⟩,row⟩ := old
  have vacuous : LiteralVariableWhere403 e.frame.decl := by
    intro c found
    rw [read.noWhere] at found
    cases found
  exact ⟨empty,⟨⟨read.elected,read.retained,read.origin,read.sameFrame,read.sameHead,vacuous⟩⟩,row⟩

private theorem into_latest_elected407 {s q e needs}
    (here : variableWithNativeK2403.elected s q e needs) :
    authoredNativeSelectedSource405.elected s q e needs :=
  .inl (.inl here)

theorem R0_elected_already_two_entry_forms407 {s q e needs} :
    R0.elected s q e needs ↔
      variableSource403.elected s q e needs ∨ authoredNativeSelectedSource405.elected s q e needs := by
  constructor
  · rintro ⟨_,family,here⟩
    cases family with
    | variableOnly => exact .inl here
    | repeated =>
      have next := repeated_local_already_in_where407 here
      exact .inr (into_latest_elected407 ⟨next.1,next.2.1,.inl next.2.2⟩)
    | whereTree => exact .inr (into_latest_elected407 ⟨here.1,here.2.1,.inl here.2.2⟩)
    | nativeK2 => exact .inr (into_latest_elected407 here)
    | supported | supportedK2 | supportedAmbiguity => exact .inr (.inl here)
    | authoredNative => exact .inr here
  · intro proof
    exact proof.elim
      (fun caseA => ⟨variableSource403,.variableOnly,caseA⟩)
      (fun caseB => ⟨authoredNativeSelectedSource405,.authoredNative,caseB⟩)

theorem R0_other_already_two_entry_forms407 {s q verdict needs} :
    R0.other s q verdict needs ↔
      variableSource403.other s q verdict needs ∨ authoredNativeSelectedSource405.other s q verdict needs := by
  constructor
  · rintro ⟨_,family,here⟩
    cases family with
    | variableOnly => exact .inl here
    | repeated | whereTree => exact .inr (.inl (.inl ⟨here.1,.inl here.2⟩))
    | nativeK2 | supported => exact .inr (.inl (.inl here))
    | supportedK2 => exact .inr (.inl here)
    | supportedAmbiguity | authoredNative => exact .inr here
  · intro proof
    exact proof.elim
      (fun caseA => ⟨variableSource403,.variableOnly,caseA⟩)
      (fun caseB => ⟨authoredNativeSelectedSource405,.authoredNative,caseB⟩)

/-- Compact algebraic presentation of exactly the current set of local
inferences, useful for auditing checker dispatch. This is not a change
to R0, an independent rule family, or a disjunction of whole reports. -/
def R0TwoEntry407 : SourcePrimitives where
  elected := fun s q e needs =>
    variableSource403.elected s q e needs ∨ authoredNativeSelectedSource405.elected s q e needs
  other := fun s q v needs =>
    variableSource403.other s q v needs ∨ authoredNativeSelectedSource405.other s q v needs

private theorem rule_fields_own_ext407 (a b : SourcePrimitives)
    (e : a.elected = b.elected) (o : a.other = b.other) : a = b := by
  cases a
  cases b
  dsimp at *
  subst_vars
  rfl

theorem R0_exactly_two_entry_forms407 : R0 = R0TwoEntry407 := by
  have first : R0.elected = R0TwoEntry407.elected :=
    funext fun _ => funext fun _ => funext fun _ => funext fun _ => propext R0_elected_already_two_entry_forms407
  have second : R0.other = R0TwoEntry407.other :=
    funext fun _ => funext fun _ => funext fun _ => funext fun _ => propext R0_other_already_two_entry_forms407
  exact rule_fields_own_ext407 R0 R0TwoEntry407 first second

theorem two_entry_checker_targets_same_classifies407 {s q result} :
    Classifies R0TwoEntry407 s q result ↔ Classifies R0 s q result := by
  rw [← R0_exactly_two_entry_forms407]

end Yulang.GeneralDeclarativeI65.I72
