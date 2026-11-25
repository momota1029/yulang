import Yulang.GeneralDeclarativeI65I74NamedEntry409

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Named409
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern normalize)

private theorem two_rows_incompatible409 {s q d} (named : NamedHead s q d)
    (old : 2 ≤ (visible s.core q).length) : False := by
  simp [named.only] at old

private theorem bare_has_no_native_argument409 {s q d} (named : NamedHead s q d)
    {r : Declaration} (present : r ∈ visible s.core q) {written : Pattern}
    (old : r.head = [written]) {key inner} (child : normalize written = .app key [inner]) : False := by
  rw [named.only] at present
  cases List.mem_singleton.mp present
  have same := (List.cons.inj (old.symm.trans named.named)).1
  rw [same] at child
  have wire : Pattern.app named.key [] = Pattern.app key [inner] := child
  have arity := congrArg List.length (Pattern.app.inj wire).2
  cases arity

private theorem named_not_repeated409 {s q d v} (named : NamedHead s q d)
    (old : RepeatedOther403 s q v) : False := by
  cases old with
  | ambiguous _ count => exact two_rows_incompatible409 named count

private theorem named_not_ordinary_or_authored_k2409 {s q d v needs}
    (named : NamedHead s q d)
    (old : variableWithNativeK2403.other s q v needs) : False := by
  rcases old.2 with repeated|⟨_,row,visit,_⟩
  · exact named_not_repeated409 named repeated
  · exact bare_has_no_native_argument409 named visit.visibleRow visit.exactHead visit.dispatch

private theorem named_not_completed_native_k2409 {s q d v needs}
    (named : NamedHead s q d)
    (old : completedNativePrioritySource404.other s q v needs) : False := by
  rcases old with regular|⟨_,⟨visit⟩⟩
  · exact named_not_ordinary_or_authored_k2409 named regular
  · exact bare_has_no_native_argument409 named visit.entry.visibleRow visit.entry.exactHead visit.entry.dispatch

private theorem named_not_completed_ambiguity409 {s q d v needs}
    (named : NamedHead s q d)
    (old : completedChoiceSource404.other s q v needs) : False := by
  rcases old with regular|⟨_,⟨ambiguous⟩⟩
  · exact named_not_completed_native_k2409 named regular
  · exact two_rows_incompatible409 named ambiguous.two

/-- Adding the opaque well-founded name branch does not hide any previously
represented actual candidate-local K2 or ambiguity. Raw root K2 is
separate and unchanged (SourceTrace requires raw safety for all positives). -/
theorem bare_name_has_no_competing_prior_local_diagnostic409 {s q d v needs}
    (named : NamedHead s q d) :
    ¬R0.other s q v needs := by
  rintro ⟨rule,family,old⟩
  cases family with
  | variableOnly =>
    cases old.2 with
    | ambiguous _ count => exact two_rows_incompatible409 named count
  | repeated | whereTree => exact named_not_repeated409 named old.2
  | nativeK2 | supported => exact named_not_ordinary_or_authored_k2409 named old
  | supportedK2 => exact named_not_completed_native_k2409 named old
  | supportedAmbiguity | authoredNative => exact named_not_completed_ambiguity409 named old

theorem R1_raw_k2_priority409 {s q} (raw : RootCycle s q) :
    Classifies R1 s q .rejected ∧ ∀ d, ¬Classifies R1 s q (.selected d) :=
  ⟨root_k2_is_rejected_for_every_primitive_system raw,fun _ => root_k2_never_selects raw⟩

end Yulang.GeneralDeclarativeI65.I72.Named409
