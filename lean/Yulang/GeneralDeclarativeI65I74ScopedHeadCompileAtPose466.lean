import Yulang.GeneralDeclarativeI65I74PreparedHeadStart463
import Yulang.GeneralDeclarativeI65I74OriginalPhysicalPositions463

set_option backward.isDefEq.respectTransparency false
namespace Yulang.C466HeadCompileAtPose
open Yulang.GeneralDeclarativeI65
open Yulang.GeneralDeclarativeI65.I72.AuthoredInspectQuery456
open Yulang.GeneralDeclarativeI65.I72.PreparedDeclarations463
open Yulang.GeneralDeclarativeI65.I72.WrittenPattern460.PhysicalOrigin
open Yulang.GeneralDeclarationPatterns (Pattern normalize)
open Yulang.GeneralNominalCenteredHeadMatExpressions (Expr application translate translateMany)
open Yulang.GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open Yulang.GeneralSourceMetadataRows291 (interpretation)

/-- These are positions in the compiled query, never raw graph positions. -/
def codeStep : Expr → Pose → Option Expr
  | .primitive _ args, .app i | .nominal _ args, .app i => args[i]?
  | .record _ p _, .payload | .record _ _ p, .tail
  | .variant _ p, .variant | .join p _, .left | .join _ p, .right => some p
  | _, _ => none

def codeAt (e : Expr) : List Pose → Option Expr
  | [] => some e
  | a::as => (codeStep e a).bind fun e' => codeAt e' as

private theorem compile_args_here {s : State} {ps : List Pattern} {es : List Expr}
    (h : compileQueries s ps = some es) (i : Nat) :
    (ps[i]?).bind (compileQuery s) = es[i]? ∧ (ps[i]?).isSome = (es[i]?).isSome := by
  induction ps generalizing es i with
  | nil =>
    cases Option.some.inj h
    exact ⟨rfl,rfl⟩
  | cons p ps ih =>
    cases pCode : compileQuery s p with
    | none => simp [compileQueries,pCode,Option.bind] at h
    | some one =>
      cases rest : compileQueries s ps with
      | none => simp [compileQueries,pCode,rest,Option.bind] at h
      | some last =>
        have e : one::last = es := Option.some.inj (by simpa [compileQueries,pCode,rest,Option.bind] using h)
        subst es
        cases i with
        | zero => exact ⟨pCode,rfl⟩
        | succ i => exact ih rest i

private theorem app_has_literal_children {s : State} {k args out}
    (h : compileApply s k args = some out) :
    (∃ op, out = .primitive op args) ∨ ∃ label, out = .nominal label args := by
  cases (compile_apply_exact ..).mp h with
  | declaredPoint _ _ _ _ => exact .inr ⟨_,rfl⟩
  | legacy old =>
    unfold legacyApply application at old
    obtain ⟨decl,lookup,emit⟩ := Option.bind_eq_some_iff.mp old
    by_cases arity : decl.parameters.length = args.length
    · cases prim : (interpretation s.current.environment.source.snapshot).primitives k with
      | none =>
        by_cases agree : (interpretation s.current.environment.source.snapshot).invariantNominal k = true ∧
            decl.parameters = List.replicate args.length .type
        · have he : Expr.nominal decl.name args = out :=
            Option.some.inj (by simpa [arity,prim,agree] using emit)
          exact .inr ⟨_,he.symm⟩
        · simp [arity,prim,agree] at emit
      | some op =>
        by_cases agree : decl.parameters = op.parameters
        · have opArity : op.parameters.length = args.length := agree ▸ arity
          have he : Expr.primitive op args = out :=
            Option.some.inj (by simpa [arity,prim,agree,opArity] using emit)
          exact .inl ⟨_,he.symm⟩
        · simp [arity,prim,agree] at emit
    · simp [arity] at emit

theorem each_compiled_input_step_is_the_same_literal_step {s : State} {p : Pattern} {e : Expr}
    (accurate : compileQuery s p = some e) (a : Pose) :
    (sourceStep p a).bind (compileQuery s) = codeStep e a ∧
    (sourceStep p a).isSome = (codeStep e a).isSome := by
  cases p with
  | var n =>
    cases Option.some.inj accurate
    cases a <;> exact ⟨rfl,rfl⟩
  | app k args =>
    change (compileQueries s args).bind (compileApply s k) = some e at accurate
    obtain ⟨raw,read,emit⟩ := Option.bind_eq_some_iff.mp accurate
    rcases app_has_literal_children emit with ⟨key,rfl⟩ | ⟨key,rfl⟩
    all_goals cases a <;> first | (exact compile_args_here read _) | exact ⟨rfl,rfl⟩
  | record label p q =>
    obtain ⟨a₁,a₂,read₁,read₂,rfl⟩ := (option_pair_exact ..).mp accurate
    cases a <;> first | exact ⟨read₁,rfl⟩ | exact ⟨read₂,rfl⟩ | exact ⟨rfl,rfl⟩
  | variant tag p =>
    obtain ⟨a₁,read₁,rfl⟩ := Option.map_eq_some_iff.mp accurate
    cases a <;> first | exact ⟨read₁,rfl⟩ | exact ⟨rfl,rfl⟩
  | join p q =>
    obtain ⟨a₁,a₂,read₁,read₂,rfl⟩ := (option_pair_exact ..).mp accurate
    cases a <;> first | exact ⟨read₁,rfl⟩ | exact ⟨read₂,rfl⟩ | exact ⟨rfl,rfl⟩

theorem every_literal_compiled_pose_replays_exactly {s : State} {p : Pattern} {e : Expr}
    (accurate : compileQuery s p = some e) (as : List Pose) :
    (atSource p as).bind (compileQuery s) = codeAt e as := by
  induction as generalizing p e with
  | nil => exact accurate
  | cons a as ih =>
    simp only [atSource,codeAt]
    have atStep := each_compiled_input_step_is_the_same_literal_step accurate a
    cases source : sourceStep p a with
    | none =>
      simp only [source,Option.bind_none] at atStep
      simp [←atStep.1]
    | some next =>
      simp only [source,Option.bind_some,Option.isSome_some] at atStep
      cases compiled : compileQuery s next with
      | none =>
        have absence : codeStep e a = none := atStep.1.symm.trans compiled
        simp [absence] at atStep
      | some code =>
        have codeStepEq : codeStep e a = some code := atStep.1.symm.trans compiled
        simpa [codeStepEq,Option.bind] using ih compiled


def oldCompile (s : State) : Pattern → Option Expr :=
  translate (authoredRegistry s.current).constructors
    (interpretation s.current.environment.source.snapshot)

theorem original_head_keeps_every_literal_query_address
    {p : I72.Checker408.Problem} (h : OriginalHead p) (poses : List Pose) :
    (atSource (normalize h.original) poses).bind (compileQuery p.state.core) =
      codeAt h.code poses :=
  every_literal_compiled_pose_replays_exactly ((compile_query_exact ..).mpr h.compiled) poses

private theorem old_nonempty_arg {s : State} {ps : List Pattern} {es : List Expr}
    (h : translateMany (authoredRegistry s.current).constructors
      (interpretation s.current.environment.source.snapshot) ps = some es)
    {i : Nat} {child : Pattern} (atI : ps[i]? = some child) :
    ∃ z, oldCompile s child = some z := by
  induction ps generalizing es i with
  | nil => simp at atI
  | cons a q ih =>
    cases a' : oldCompile s a with
    | none => simp [oldCompile] at a'
              simp [translateMany,a',Option.bind] at h
    | some v =>
      cases opt : translateMany (authoredRegistry s.current).constructors
          (interpretation s.current.environment.source.snapshot) q with
      | none => simp [oldCompile] at a'
                simp [translateMany,a',opt,Option.bind] at h
      | some tail =>
        cases i with
        | zero =>
          have same : a = child := Option.some.inj atI
          exact ⟨v,same ▸ a'⟩
        | succ i => exact ih opt atI

private theorem old_step_success {s : State} {p q : Pattern} {e : Expr} {a : Pose}
    (h : oldCompile s p = some e) (atA : sourceStep p a = some q) :
    ∃ z, oldCompile s q = some z := by
  cases p with
  | var => cases a <;> cases atA
  | app k ps =>
    cases a <;> try cases atA
    change ((translateMany (authoredRegistry s.current).constructors
      (interpretation s.current.environment.source.snapshot) ps).bind (legacyApply s k)) = some e at h
    obtain ⟨res,compiled,emits⟩ := Option.bind_eq_some_iff.mp h
    exact old_nonempty_arg compiled atA
  | record l p t =>
    obtain ⟨x,y,one,two,eq⟩ := (option_pair_exact (oldCompile s p) (oldCompile s t)
      (Expr.record l) e).mp h
    cases a <;> try cases atA
    · exact ⟨x,one⟩
    · exact ⟨y,two⟩
  | variant tag p =>
    cases z : oldCompile s p with
    | none =>
      simp [oldCompile] at z
      simp [oldCompile,translate,z,Option.bind] at h
    | some out =>
      cases a <;> try cases atA
      exact ⟨out,z⟩
  | join p t =>
    obtain ⟨x,y,one,two,eq⟩ := (option_pair_exact (oldCompile s p) (oldCompile s t) Expr.join e).mp h
    cases a <;> try cases atA
    · exact ⟨x,one⟩
    · exact ⟨y,two⟩

theorem old_translation_success_has_no_untranslated_literal_subtree {s : State}
    {p q : Pattern} {e : Expr} (h : oldCompile s p = some e)
    {atP : List Pose} (loc : atSource p atP = some q) : ∃ z, oldCompile s q = some z := by
  induction atP generalizing p e with
  | nil =>
    have same : p = q := Option.some.inj loc
    exact ⟨e,same ▸ h⟩
  | cons a as ih =>
    have walk : (sourceStep p a).bind (fun sub => atSource sub as) = some q := loc
    obtain ⟨sub,one,rest⟩ := Option.bind_eq_some_iff.mp walk
    obtain ⟨out,printed⟩ := old_step_success h one
    exact ih printed rest

theorem a_modern_only_pose_obstructs_any_old_compilation_of_the_whole_source
    {s : State} {p q : Pattern} {pose : List Pose} (loc : atSource p pose = some q)
    (unavailable : oldCompile s q = none) : oldCompile s p = none := by
  cases printed : oldCompile s p with
  | none => rfl
  | some out =>
    obtain ⟨sub,good⟩ := old_translation_success_has_no_untranslated_literal_subtree printed loc
    rw [unavailable] at good
    cases good

theorem same_original_head_and_old_compiler_share_exact_literal_subtree
    {p : I72.Checker408.Problem} (h : OriginalHead p)
    (old : oldCompile p.state.core (normalize h.original) = some h.code)
    {sub : Pattern} {poses : List Pose} (site : atSource (normalize h.original) poses = some sub) :
    ∃ result, oldCompile p.state.core sub = some result ∧ codeAt h.code poses = some result := by
  obtain ⟨res,printed⟩ := old_translation_success_has_no_untranslated_literal_subtree old site
  have modern := compile_query_preserves_legacy p.state.core sub res printed
  have exactView := original_head_keeps_every_literal_query_address h poses
  rw [site] at exactView
  exact ⟨res,printed,exactView.symm.trans modern⟩


end Yulang.C466HeadCompileAtPose
