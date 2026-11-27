import Yulang.GeneralDeclarativeI65I74RoutedNominalPoint456

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.AuthoredInspectQuery456
open GeneralDeclarationPatterns (Pattern)
open GeneralNominalCenteredHeadMatExpressions (Expr application translate translateMany)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeWitnessConstructorModes357 (Use readUse)
open RoutedNominalPoint456 (cov actual_declared_use_is_readable456)

def legacyApply (s : GeneralDeclarativeI65.State) (key : Nat) (args : List Expr) : Option Expr :=
  application (authoredRegistry s.current).constructors
    (interpretation s.current.environment.source.snapshot) key args

/-- A separate shape-only extension. No use of the expression as a
mode-erased type interpretation; old application takes priority. -/
inductive AuthoredApplication (s : GeneralDeclarativeI65.State) : Nat → List Expr → Expr → Prop
  | legacy : legacyApply s key args = some result → AuthoredApplication s key args result
  | declaredPoint :
      legacyApply s key [arg] = none →
      (use : Use s.current.environment key 1) →
      use.mode = .declared [cov] →
      s.modes[key]? = some [cov] →
      AuthoredApplication s key [arg] (.nominal key [arg])

def compileApply (s : GeneralDeclarativeI65.State) (key : Nat) (args : List Expr) : Option Expr :=
  match legacyApply s key args with
  | some r => some r
  | none =>
    match args with
    | [arg] =>
      match readUse s.current.environment key 1 with
      | none => none
      | some use =>
        match use.mode with
        | .declared ps =>
          if ps = [cov] ∧ s.modes[key]? = some [cov] then some (.nominal key [arg]) else none
        | _ => none
    | _ => none

theorem compile_apply_exact (s : GeneralDeclarativeI65.State) (key : Nat) (args : List Expr) (r : Expr) :
    compileApply s key args = some r ↔ AuthoredApplication s key args r := by
  constructor
  · intro yes
    cases old : legacyApply s key args with
    | some t =>
      have agree : t = r := Option.some.inj (by simpa [compileApply,old] using yes)
      subst r
      exact .legacy old
    | none =>
      cases args with
      | nil => simp [compileApply,old] at yes
      | cons arg rest =>
        cases rest with
        | cons a as => simp [compileApply,old] at yes
        | nil =>
          cases read : readUse s.current.environment key 1 with
          | none => simp [compileApply,old,read] at yes
          | some use =>
            cases mode : use.mode with
            | primitive p => simp [compileApply,old,read,mode] at yes
            | invariant => simp [compileApply,old,read,mode] at yes
            | declared ps =>
              by_cases agreeModes : ps = [cov] ∧ s.modes[key]? = some [cov]
              · have exact : Expr.nominal key [arg] = r :=
                  Option.some.inj (by simpa [compileApply,old,read,mode,agreeModes] using yes)
                subst r
                exact .declaredPoint old use (mode.trans (congrArg _ agreeModes.1)) agreeModes.2
              · simp [compileApply,old,read,mode,agreeModes] at yes
  · intro source
    cases source with
    | legacy old => simp [compileApply,old]
    | declaredPoint old use mode table =>
      have read := actual_declared_use_is_readable456 use mode
      simp [compileApply,old,read,mode,table]

mutual
  inductive AuthoredQuery (s : GeneralDeclarativeI65.State) : Pattern → Expr → Prop
    | var : AuthoredQuery s (.var n) (.variable n)
    | app :
      AuthoredQueries s ps qs →
      AuthoredApplication s key qs result →
      AuthoredQuery s (.app key ps) result
    | record : AuthoredQuery s f q → AuthoredQuery s t u →
      AuthoredQuery s (.record l f t) (.record l q u)
    | variant : AuthoredQuery s f q → AuthoredQuery s (.variant l f) (.variant l q)
    | join : AuthoredQuery s f q → AuthoredQuery s t u →
      AuthoredQuery s (.join f t) (.join q u)
  inductive AuthoredQueries (s : GeneralDeclarativeI65.State) : List Pattern → List Expr → Prop
    | nil : AuthoredQueries s [] []
    | cons : AuthoredQuery s p e → AuthoredQueries s ps es →
      AuthoredQueries s (p::ps) (e::es)
end

mutual
  def compileQuery (s : GeneralDeclarativeI65.State) : Pattern → Option Expr
    | .var n => some (.variable n)
    | .app key args => do
      let qs ← compileQueries s args
      compileApply s key qs
    | .record l f t => do pure (.record l (← compileQuery s f) (← compileQuery s t))
    | .variant l f => (compileQuery s f).map (.variant l)
    | .join f t => do pure (.join (← compileQuery s f) (← compileQuery s t))
  def compileQueries (s : GeneralDeclarativeI65.State) : List Pattern → Option (List Expr)
    | [] => some []
    | p::ps => do pure ((← compileQuery s p) :: (← compileQueries s ps))
end

theorem option_pair_exact (a : Option α) (b : Option β) (f : α → β → γ) (t : γ) :
    (do pure (f (← a) (← b)) : Option γ) = some t ↔
      ∃ x y, a = some x ∧ b = some y ∧ f x y = t := by
  cases a <;> cases b <;> simp

mutual
  theorem compile_query_exact (s : GeneralDeclarativeI65.State) (p : Pattern) (e : Expr) :
      compileQuery s p = some e ↔ AuthoredQuery s p e := by
    cases p with
    | var n =>
      constructor
      · intro h
        cases Option.some.inj h
        exact .var
      · intro h
        cases h
        rfl
    | app key ps =>
      change ((compileQueries s ps).bind (compileApply s key)) = some e ↔ _
      rw [Option.bind_eq_some_iff]
      constructor
      · rintro ⟨args,found,wrote⟩
        exact .app ((compile_queries_exact s ps args).mp found) ((compile_apply_exact ..).mp wrote)
      · intro h
        cases h with
        | app args apply =>
          exact ⟨_,(compile_queries_exact ..).mpr args,(compile_apply_exact ..).mpr apply⟩
    | record l p q =>
      rw [compileQuery,option_pair_exact]
      constructor
      · rintro ⟨a,b,left,right,rfl⟩
        exact .record ((compile_query_exact s p a).mp left) ((compile_query_exact s q b).mp right)
      · intro h
        cases h with | record a b =>
          exact ⟨_,_,(compile_query_exact ..).mpr a,(compile_query_exact ..).mpr b,rfl⟩
    | variant l p =>
      rw [compileQuery,Option.map_eq_some_iff]
      constructor
      · rintro ⟨a,decoded,rfl⟩
        exact .variant ((compile_query_exact s p a).mp decoded)
      · intro h
        cases h with | variant one => exact ⟨_,(compile_query_exact ..).mpr one,rfl⟩
    | join p q =>
      rw [compileQuery,option_pair_exact]
      constructor
      · rintro ⟨a,b,left,right,rfl⟩
        exact .join ((compile_query_exact s p a).mp left) ((compile_query_exact s q b).mp right)
      · intro h
        cases h with | join a b =>
          exact ⟨_,_,(compile_query_exact ..).mpr a,(compile_query_exact ..).mpr b,rfl⟩
  theorem compile_queries_exact (s : GeneralDeclarativeI65.State) (ps : List Pattern) (es : List Expr) :
      compileQueries s ps = some es ↔ AuthoredQueries s ps es := by
    cases ps with
    | nil =>
      constructor
      · intro h
        cases Option.some.inj h
        exact .nil
      · intro h; cases h; rfl
    | cons p ps =>
      rw [compileQueries,option_pair_exact]
      constructor
      · rintro ⟨a,b,first,rest,rfl⟩
        exact .cons ((compile_query_exact s p a).mp first) ((compile_queries_exact s ps b).mp rest)
      · intro h
        cases h with | cons first rest =>
          exact ⟨_,_,(compile_query_exact ..).mpr first,(compile_queries_exact ..).mpr rest,rfl⟩
end


mutual
 theorem compile_query_preserves_legacy (s : GeneralDeclarativeI65.State) (p : Pattern) (e : Expr)
    (old : translate (authoredRegistry s.current).constructors
       (interpretation s.current.environment.source.snapshot) p = some e) :
    compileQuery s p = some e := by
  cases p with
  | var n => exact old
  | app key ps =>
    change ((translateMany (authoredRegistry s.current).constructors
      (interpretation s.current.environment.source.snapshot) ps).bind _) = some e at old
    obtain ⟨es,decoded,app⟩ := Option.bind_eq_some_iff.mp old
    have more := compile_queries_preserve_legacy s ps es decoded
    have written : compileApply s key es = some e := (compile_apply_exact ..).mpr (.legacy app)
    change (compileQueries s ps).bind (compileApply s key) = some e
    rw [more]
    exact written
  | record l f t =>
    rw [translate,option_pair_exact] at old
    obtain ⟨a,b,first,last,rfl⟩ := old
    rw [compileQuery,option_pair_exact]
    exact ⟨a,b,compile_query_preserves_legacy s f a first,
      compile_query_preserves_legacy s t b last,rfl⟩
  | variant l f =>
    change ((do pure (.variant l (← translate (authoredRegistry s.current).constructors
      (interpretation s.current.environment.source.snapshot) f))) : Option Expr) = some e at old
    cases found : translate (authoredRegistry s.current).constructors
        (interpretation s.current.environment.source.snapshot) f with
    | none => simp [found] at old
    | some q =>
      have eq : Expr.variant l q = e := Option.some.inj (by simpa [found] using old)
      subst e
      simp [compileQuery,compile_query_preserves_legacy s f q found]
  | join f t =>
    rw [translate,option_pair_exact] at old
    obtain ⟨a,b,first,last,rfl⟩ := old
    rw [compileQuery,option_pair_exact]
    exact ⟨a,b,compile_query_preserves_legacy s f a first,
      compile_query_preserves_legacy s t b last,rfl⟩
 theorem compile_queries_preserve_legacy (s : GeneralDeclarativeI65.State) (ps : List Pattern) (qs : List Expr)
    (old : translateMany (authoredRegistry s.current).constructors
       (interpretation s.current.environment.source.snapshot) ps = some qs) :
    compileQueries s ps = some qs := by
  cases ps with
  | nil => exact old
  | cons p ps =>
    rw [translateMany,option_pair_exact] at old
    obtain ⟨a,b,first,last,rfl⟩ := old
    rw [compileQueries,option_pair_exact]
    exact ⟨a,b,compile_query_preserves_legacy s p a first,
      compile_queries_preserve_legacy s ps b last,rfl⟩
end

end Yulang.GeneralDeclarativeI65.I72.AuthoredInspectQuery456