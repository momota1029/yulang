import Yulang.GeneralNominalGroundProduction

/-! Substitution facts at the declaration syntax boundary. Raw encoding
commutes with substitution for all patterns. Normalization is handled
separately for the application fragment, without assuming open-tail laws. -/
namespace Yulang.GeneralPatternGroundSubstitution
open GeneralDeclarationPatterns

theorem covered_plain_names (pattern : Pattern) (covered : covered pattern = true)
    (found : GeneralCandidateInspection.plainNames pattern = some names) :
    ∃ name, pattern = .var name ∧ names = [name] := by
  cases pattern with
  | var name => exact ⟨name,rfl,Option.some.inj found |>.symm⟩
  | app | record | variant => cases found
  | join => cases covered

mutual
  theorem encode_subst (pattern : Pattern) (capture : Nat → Pattern) :
      (pattern.subst capture).encode = Roles.Term.subst (fun name => (capture name).encode) pattern.encode := by
    cases pattern with
    | var name => rfl
    | app key arguments =>
      simp only [Pattern.subst,Pattern.encode,Roles.Term.subst,encode_substArgs arguments capture]
    | record label payload tail =>
      simp only [Pattern.subst,Pattern.encode,Roles.Term.subst,Roles.substArgs,encode_subst payload capture,encode_subst tail capture]
    | variant tag payload =>
      simp only [Pattern.subst,Pattern.encode,Roles.Term.subst,Roles.substArgs,encode_subst payload capture]
    | join first last =>
      simp only [Pattern.subst,Pattern.encode,Roles.Term.subst,Roles.substArgs,encode_subst first capture,encode_subst last capture]
  theorem encode_substArgs (arguments : List Pattern) (capture : Nat → Pattern) :
      encodeArgs (substArgs capture arguments) = Roles.substArgs (fun name => (capture name).encode) (encodeArgs arguments) := by
    cases arguments with
    | nil => rfl
    | cons head tail =>
      simp only [substArgs,encodeArgs,Roles.substArgs,encode_subst head capture,encode_substArgs tail capture]
end

mutual
  def Applications : Pattern → Prop
    | .var _ => True
    | .app _ arguments => ApplicationArgs arguments
    | _ => False
  def ApplicationArgs : List Pattern → Prop
    | [] => True
    | head :: tail => Applications head ∧ ApplicationArgs tail
end

mutual
  theorem normalize_application (pattern : Pattern) (fragment : Applications pattern) : normalize pattern = pattern := by
    cases pattern with
    | var name => rfl
    | app key arguments => exact congrArg (Pattern.app key) (normalize_applicationArgs arguments fragment)
    | record | variant | join => cases fragment
  theorem normalize_applicationArgs (arguments : List Pattern) (fragment : ApplicationArgs arguments) :
      normalizeArgs arguments = arguments := by
    cases arguments with
    | nil => rfl
    | cons head tail =>
      simp only [normalizeArgs,normalize_application head fragment.1,normalize_applicationArgs tail fragment.2]
end

mutual
  theorem normalize_subst (pattern : Pattern) (fragment : Applications pattern) (capture : Nat → Pattern) :
      normalize (pattern.subst capture) = pattern.subst (fun name => normalize (capture name)) := by
    cases pattern with
    | var name => rfl
    | app key arguments => exact congrArg (Pattern.app key) (normalize_substArgs arguments fragment capture)
    | record | variant | join => cases fragment
  theorem normalize_substArgs (arguments : List Pattern) (fragment : ApplicationArgs arguments) (capture : Nat → Pattern) :
      normalizeArgs (substArgs capture arguments) = substArgs (fun name => normalize (capture name)) arguments := by
    cases arguments with
    | nil => rfl
    | cons head tail =>
      simp only [substArgs,normalizeArgs,normalize_subst head fragment.1 capture,normalize_substArgs tail fragment.2 capture]
end

theorem counted_substitution (arguments : List Pattern) (fragment : ApplicationArgs arguments) (capture : Nat → Pattern) :
    counted (substArgs capture arguments) =
      Roles.substArgs (fun name => (normalize (capture name)).encode) (encodeArgs arguments) := by
  unfold counted
  rw [normalize_substArgs arguments fragment capture,encode_substArgs]

theorem instantiated_mass (arguments : List Pattern) (fragment : ApplicationArgs arguments)
    (capture : Nat → Pattern) :
    GeneralNominalPatersonLineage.mass (substArgs capture arguments) =
      Roles.argsSize (Roles.substArgs (fun name => (normalize (capture name)).encode) (encodeArgs arguments)) := by
  unfold GeneralNominalPatersonLineage.mass
  rw [counted_substitution arguments fragment capture]

end Yulang.GeneralPatternGroundSubstitution
