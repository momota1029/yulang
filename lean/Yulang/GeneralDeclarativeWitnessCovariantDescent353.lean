import Yulang.GeneralDeclarativeWitnessTagHeader352

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCovariantDescent353
open GeneralDeclarationPatterns (Pattern StableSmaller counted substArgs normalizeArgs normalize merge variantRow
  rowPattern mergePayload encodeArgs)

def arm (tag box : Nat) (payload : Pattern) : Pattern := .variant tag (.app box [payload])

def two (tag box first last : Nat) : Pattern :=
  .join (arm tag box (.var first)) (arm tag box (.var last))

theorem merge_both (tag box : Nat) (a b : Pattern) :
    merge (arm tag box a) (arm tag box b) =
      if a = b then arm tag box a
      else .variant tag (.join (.app box [a]) (.app box [b])) := by
  by_cases same : a = b
  · subst b
    simp [merge]
  · have apart : [a] ≠ [b] := fun n => same (List.cons.inj n).1
    simp [merge,arm,apart,same,variantRow,rowPattern,mergePayload,Variants.Merged.normalize,
      Variants.Merged.Raw.insert]

theorem after_subst (tag box l r : Nat) (sub : Nat → Pattern) :
    normalize ((two tag box l r).subst sub) =
      merge (arm tag box (normalize (sub l))) (arm tag box (normalize (sub r))) := rfl

theorem either_strict (tag box l r : Nat) (choose : n = l ∨ n = r) :
    StableSmaller [two tag box l r] [.var n] := by
  intro sub
  have normalized : normalizeArgs (substArgs sub [two tag box l r]) =
      [merge (arm tag box (normalize (sub l))) (arm tag box (normalize (sub r)))] := by
    simp only [substArgs,normalizeArgs,after_subst]
  unfold GeneralDeclarationPatterns.Smaller counted
  rw [normalized,merge_both]
  simp only [substArgs,Pattern.subst,normalizeArgs]
  by_cases same : normalize (sub l) = normalize (sub r)
  · simp only [same,ite_true,arm,encodeArgs,Pattern.encode,Roles.argsSize,Roles.Term.size]
    rcases choose with rfl|rfl
    · rw [same]
      exact ⟨by omega,by intro q; simp [Roles.argsOccurrences,Roles.Term.occurrences]⟩
    · exact ⟨by omega,by intro q; simp [Roles.argsOccurrences,Roles.Term.occurrences]⟩
  · simp only [same,ite_false,encodeArgs,Pattern.encode,Roles.argsSize,Roles.Term.size]
    rcases choose with rfl|rfl <;> exact ⟨by omega,by intro q; simp [Roles.argsOccurrences,Roles.Term.occurrences]⟩

def exactShape (h c : List Pattern) : Bool :=
  match h,c with
  | [.join (.variant t (.app b [.var l])) (.variant u (.app e [.var r]))],[.var n] =>
    decide (t = u ∧ b = e ∧ (n = l ∨ n = r))
  | _,_ => false

theorem extra_sound {h c : List Pattern} (check : exactShape h c = true) : StableSmaller h c := by
  unfold exactShape at check
  split at check
  · obtain ⟨rfl,rfl,selected⟩ := of_decide_eq_true check
    exact either_strict _ _ _ _ selected
  · cases check

/-- Residual joins are not CountsCovered in C334. The additional
positive rule proves actual raw descent and verifies the conservative
constructor path in the particular jointly authorized box arm. -/
def descent (head child : List Pattern) : Bool :=
  GeneralDeclarativeWitnessTagHeader352.checkDescent head child ||
    (GeneralDeclarationPatterns.checkSmaller head child &&
      match head, child with
      | [.join (.variant t (.app b [.var l])) (.variant u (.app c [.var r]))],[.var _n] =>
        exactShape head child &&
          (CheckedRoles.checkCondition (GeneralDeclarationPatterns.lowerArgs [arm t b (.var l)]) ⟨0,counted child⟩ ||
           CheckedRoles.checkCondition (GeneralDeclarationPatterns.lowerArgs [arm u c (.var r)]) ⟨0,counted child⟩)
      | _,_ => false)

theorem descent_sound {h c : List Pattern} (proof : descent h c = true) :
    GeneralDeclarationPatterns.Smaller h c ∧ StableSmaller h c := by
  open GeneralDeclarativeWitnessProblem349 in
  rcases splitOr proof with base|more
  · exact ⟨(GeneralDeclarativeWitnessTagHeader352.descent base).2.1,
      (GeneralDeclarativeWitnessTagHeader352.descent base).2.2.2⟩
  · obtain ⟨size,shape⟩ := splitAnd more
    refine ⟨(GeneralDeclarationPatterns.checkSmaller_exact ..).mp size,?_⟩
    split at shape
    · exact extra_sound (splitAnd shape).1
    · cases shape

def legal (s : GeneralSourceMetadataBundle291.SourceBundle) (d : GeneralDeclarations.Declaration) : Bool :=
  open GeneralDeclarativeWitnessChecks349 in
  (GeneralDeclarativeWitnessSignature349.checks s.roles d && ids d) &&
  ((binds d && lexical d) && (names d && d.requirements.all (fun c => descent d.head c.arguments)))

end Yulang.GeneralDeclarativeWitnessCovariantDescent353
