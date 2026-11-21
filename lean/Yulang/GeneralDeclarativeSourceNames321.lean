import Yulang.GeneralDeclarativeTraceNames321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeSourceNames321
open GeneralDeclarativeTraceNames321 (names namesMany Keys Modes trace_keys_modes)
open GeneralDeclarativeTrace321 (Trace Occurrence)
open GeneralDeclarationPatterns (Pattern variablesArgs)
open GeneralNominalCenteredHeadMatExpressions (Expr application translate translateMany)

theorem application_names (found : application c interp ctor args = some exp) :
    names exp = namesMany args := by
  cases registered : c ctor with
  | none => simp [application,registered] at found
  | some decl =>
    by_cases arity : decl.parameters.length = args.length
    · cases prim : interp.primitives ctor with
      | none =>
        by_cases nominal : interp.invariantNominal ctor = true ∧
            decl.parameters = List.replicate args.length .type
        · have same : Expr.nominal decl.name args = exp := by
            simpa [application,registered,arity,prim,nominal] using found
          subst exp
          rfl
        · simp [application,registered,arity,prim,nominal] at found
      | some x =>
        by_cases compliant : decl.parameters = x.parameters
        · have arity' : x.parameters.length = args.length := compliant ▸ arity
          have same : Expr.primitive x args = exp := by
            simpa [application,registered,arity,arity',prim,compliant] using found
          subst exp
          rfl
        · simp [application,registered,arity,prim,compliant] at found
    · simp [application,registered,arity] at found

mutual
 theorem actual_names (pattern : Pattern) (found : translate c interp pattern = some exp) :
    names exp = pattern.variables := by
  cases pattern with
  | var n => cases found; rfl
  | app ctor args =>
    cases built : translateMany c interp args with
    | none => simp [translate,built] at found
    | some codes =>
      have appFound : application c interp ctor codes = some exp := by simpa [translate,built] using found
      exact (application_names appFound).trans (actual_names_many args built)
  | record label a b =>
    cases ha : translate c interp a with
    | none => simp [translate,ha] at found
    | some e =>
      cases hb : translate c interp b with
      | none => simp [translate,ha,hb] at found
      | some f =>
        have same : Expr.record label e f = exp := by simpa [translate,ha,hb] using found
        subst exp
        simp only [names,Pattern.variables,actual_names a ha,actual_names b hb]
  | variant tag a =>
    cases ha : translate c interp a with
    | none => simp [translate,ha] at found
    | some e =>
      have same : Expr.variant tag e = exp := by simpa [translate,ha] using found
      subst exp
      change names e = a.variables
      exact actual_names a ha
  | join a b =>
    cases ha : translate c interp a with
    | none => simp [translate,ha] at found
    | some e =>
      cases hb : translate c interp b with
      | none => simp [translate,ha,hb] at found
      | some f =>
        have same : Expr.join e f = exp := by simpa [translate,ha,hb] using found
        subst exp
        simp only [names,Pattern.variables,actual_names a ha,actual_names b hb]
 termination_by sizeOf pattern
 theorem actual_names_many (ps : List Pattern) (found : translateMany c interp ps = some codes) :
    namesMany codes = variablesArgs ps := by
  cases ps with
  | nil => cases found; rfl
  | cons p ps =>
    cases one : translate c interp p with
    | none => simp [translateMany,one] at found
    | some e =>
      cases tail : translateMany c interp ps with
      | none => simp [translateMany,one,tail] at found
      | some es =>
        have same : e :: es = codes := by simpa [translateMany,one,tail] using found
        subst codes
        simp only [namesMany,variablesArgs,actual_names p one,actual_names_many ps tail]
 termination_by sizeOf ps
end

theorem actual_source_occurrences (found : translate c interp pattern = some exp)
    (walk : Trace s .actual arg exp seen) :
    Keys seen pattern.variables ∧ ∀ binder ∈ pattern.variables,
      ∃ name, (⟨binder,.actual,name⟩ : Occurrence) ∈ seen := by
  have distribution := trace_keys_modes walk
  have exacts : Keys seen pattern.variables := by
    simpa only [actual_names pattern found] using distribution.1
  refine ⟨exacts,?_⟩
  intro binder used
  change seen.map Occurrence.binder = pattern.variables at exacts
  rw [← exacts] at used
  obtain ⟨⟨n,mode,name⟩,member,same⟩ := List.mem_map.mp used
  have modeActual : mode = .actual := (distribution.2 _ member).elim id id
  change n = binder at same
  subst_vars
  exact ⟨name,member⟩

end Yulang.GeneralDeclarativeSourceNames321
