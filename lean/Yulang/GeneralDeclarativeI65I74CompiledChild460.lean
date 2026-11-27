import Yulang.GeneralDeclarativeI65I74JointWrittenField460

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
open AuthoredInspectQuery456 (AuthoredQuery AuthoredQueries AuthoredApplication legacyApply)
open GeneralNominalCenteredHeadMatExpressions (Expr application)
open GeneralDeclarativeInspect321 (fieldPatterns)
open RecordTraversal455.MixedQA (ChildAt)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

theorem authored_application_keeps_ordered_args {s key args result}
    (auth : AuthoredApplication s key args result) :
    (∃ prim, result = .primitive prim args) ∨ ∃ k, result = .nominal k args := by
  cases auth with
  | legacy h =>
    cases found : (authoredRegistry s.current).constructors key with
    | none => simp [legacyApply,application,found,Option.bind] at h
    | some decl =>
      by_cases arity : decl.parameters.length = args.length
      · cases mode : (interpretation s.current.environment.source.snapshot).primitives key with
        | some primitive =>
          by_cases kinds : decl.parameters = primitive.parameters
          · have arity' : primitive.parameters.length = args.length := kinds ▸ arity
            exact .inl ⟨primitive,(Option.some.inj (by
              simpa [legacyApply,application,found,Option.bind,arity,mode,kinds,arity'] using h)).symm⟩
          · simp [legacyApply,application,found,Option.bind,arity,mode,kinds] at h
        | none =>
          by_cases kinds : (interpretation s.current.environment.source.snapshot).invariantNominal key = true ∧
              decl.parameters = List.replicate args.length .type
          · exact .inr ⟨decl.name,(Option.some.inj (by
              simpa [legacyApply,application,found,Option.bind,arity,mode,kinds] using h)).symm⟩
          · simp [legacyApply,application,found,Option.bind,arity,mode,kinds] at h
      · simp [legacyApply,application,found,Option.bind,arity] at h
  | declaredPoint => exact .inr ⟨_,rfl⟩

theorem actual_first_field_compiles_to_observed_child {s label source selected e q}
    (first : FirstField label source selected)
    (auth : AuthoredQuery s (writeTerm source) e)
    (hit : (label,q) ∈ fieldPatterns e) :
    AuthoredQuery s (writeTerm selected) q := by
  induction first generalizing e with
  | @here item tail =>
    change AuthoredQuery s (.record label (writeTerm item) (writeTerm tail)) e at auth
    cases auth with
    | record head rest =>
      simp only [fieldPatterns,List.mem_cons,List.mem_filter] at hit
      rcases hit with h | ⟨_,contra⟩
      · obtain ⟨_,rfl⟩ := Prod.mk.inj h
        exact head
      · simp at contra
  | @later l tail item skipped ne walk ih =>
    change AuthoredQuery s (.record l (writeTerm skipped) (writeTerm tail)) e at auth
    cases auth with
    | record head rest =>
      simp only [fieldPatterns,List.mem_cons,List.mem_filter] at hit
      rcases hit with bad | ⟨there,_⟩
      · exact (ne (Prod.mk.inj bad).1).elim
      · exact ih rest there

theorem authored_first_argument_retains_compile {s p ps qs q}
    (auth : AuthoredQueries s (writeArgs (.cons p ps)) qs)
    (atIndex : qs[0]? = some q) :
    AuthoredQuery s (writeTerm p) q := by
  change AuthoredQueries s (writeTerm p :: writeArgs ps) qs at auth
  cases auth with
  | cons one rest =>
    simp at atIndex
    subst q
    exact one

theorem authored_second_argument_retains_compile {s p x ps qs q}
    (auth : AuthoredQueries s (writeArgs (.cons p (.cons x ps))) qs)
    (atIndex : qs[1]? = some q) :
    AuthoredQuery s (writeTerm x) q := by
  change AuthoredQueries s (writeTerm p :: writeTerm x :: writeArgs ps) qs at auth
  cases auth with
  | cons one rest => exact authored_first_argument_retains_compile rest (by simpa using atIndex)

theorem selected_zero_query_of_same_authored_application {s key p ps e sh addr c q}
    (auth : AuthoredQuery s (writeTerm (.app key (.cons p ps))) e)
    (step : ChildAt sh e addr c q) (i : writtenAddress addr = .arg 0) :
    AuthoredQuery s (writeTerm p) q := by
  change AuthoredQuery s (.app key (writeArgs (.cons p ps))) e at auth
  cases auth with
  | app written app =>
    rcases authored_application_keeps_ordered_args app with ⟨a,rfl⟩ | ⟨a,rfl⟩
    · cases step with
      | primitive _ qAt =>
        simp only [writtenAddress,Address.arg.injEq] at i
        subst_vars
        exact authored_first_argument_retains_compile written qAt
    · cases step with
      | nominal _ qAt =>
        simp only [writtenAddress,Address.arg.injEq] at i
        subst_vars
        exact authored_first_argument_retains_compile written qAt

theorem selected_one_query_of_same_authored_application {s key p x ps e sh addr c q}
    (auth : AuthoredQuery s (writeTerm (.app key (.cons p (.cons x ps)))) e)
    (step : ChildAt sh e addr c q) (i : writtenAddress addr = .arg 1) :
    AuthoredQuery s (writeTerm x) q := by
  change AuthoredQuery s (.app key (writeArgs (.cons p (.cons x ps)))) e at auth
  cases auth with
  | app written app =>
    rcases authored_application_keeps_ordered_args app with ⟨a,rfl⟩ | ⟨a,rfl⟩
    · cases step with
      | primitive _ qAt =>
        simp only [writtenAddress,Address.arg.injEq] at i
        subst_vars
        exact authored_second_argument_retains_compile written qAt
    · cases step with
      | nominal _ qAt =>
        simp only [writtenAddress,Address.arg.injEq] at i
        subst_vars
        exact authored_second_argument_retains_compile written qAt

/-- From the existing full compiler derivation, restrict to the one
actually selected child. No compiler computation on another component is
needed for this restriction. -/
theorem same_authored_compilation_at_selected_address {s keys source dest e sh addr c q a}
    (auth : AuthoredQuery s (writeTerm source) e)
    (written : Step keys source a dest)
    (eq : writtenAddress addr = a)
    (raw : ChildAt sh e addr c q) :
    AuthoredQuery s (writeTerm dest) q := by
  cases written with
  | @field tail l k p next closed actual =>
    change AuthoredQuery s (.record k (writeTerm p) (writeTerm tail)) e at auth
    cases auth with
    | record f t =>
      cases raw with
      | field _ into =>
        simp only [writtenAddress,Address.field.injEq] at eq
        subst_vars
        exact actual_first_field_compiles_to_observed_child actual (.record f t) into
  | tag =>
    change AuthoredQuery s (.variant _ (writeTerm dest)) e at auth
    cases auth with
    | variant payload =>
      cases raw
      exact payload
  | pair0 _ => exact selected_zero_query_of_same_authored_application auth raw eq
  | pair1 _ => exact selected_one_query_of_same_authored_application auth raw eq
  | point _ => exact selected_zero_query_of_same_authored_application auth raw eq

theorem same_authored_compilation_at_selected_child {s keys source dest e sh addr c q}
    (auth : AuthoredQuery s (writeTerm source) e)
    (written : Step keys source (writtenAddress addr) dest)
    (raw : ChildAt sh e addr c q) :
    AuthoredQuery s (writeTerm dest) q :=
  same_authored_compilation_at_selected_address auth written rfl raw

end Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
