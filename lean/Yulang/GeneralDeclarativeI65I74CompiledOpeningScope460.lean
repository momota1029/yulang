import Yulang.GeneralDeclarativeI65I74CompiledApplicationReflection460

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
open AuthoredInspectQuery456 (AuthoredQuery AuthoredQueries AuthoredApplication legacyApply compile_apply_exact)
open GeneralNominalCenteredHeadMatExpressions (Expr application)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeWitnessConstructorModes357 (Use SourceMode)
open RoutedNominalPoint456 (cov)
open RecordTraversal455.MixedQA (ChildAt)

theorem declared_mode_cannot_choose_legacy_application {s key}
    (u : Use s.current.environment key 1)
    (mode : u.mode = .declared [cov]) (args : List Expr) :
    legacyApply s key args = none := by
  have auth : SourceMode s.current.environment key (.declared [cov]) := mode ▸ u.sourced
  cases auth with
  | declared checked noPrimitive noInvariant =>
    cases decl : (authoredRegistry s.current).constructors key with
    | none => simp [legacyApply,application,decl,Option.bind]
    | some c =>
      simp [legacyApply,application,decl,Option.bind,interpretation,noPrimitive,noInvariant]

theorem exact_declared_unary_application_at_original_key {s key}
    (u : Use s.current.environment key 1)
    (mode : u.mode = .declared [cov])
    (table : s.modes[key]? = some [cov]) (q : Expr) :
    queryKeys s key = .covariantPoint ∧ AuthoredApplication s key [q] (.nominal key [q]) := by
  have no := declared_mode_cannot_choose_legacy_application u mode
  have ae : emptyKey s key = false := by simp [emptyKey,no]
  have ap : pairKey s key = false := by simp [pairKey,no]
  exact ⟨query_point_key_exact.mpr ⟨ae,ap,⟨u,mode⟩,table⟩,
    .declaredPoint (no _) u mode table⟩

theorem read_pair_key_accepts_any_two_compiled_operands {s key}
    (h : queryKeys s key = .binaryPair) (p q : Expr) :
    AuthoredApplication s key [p,q] (.primitive .pair [p,q]) := by
  obtain ⟨x,y,seen⟩ := query_pair_key_has_actual_pair h
  obtain ⟨d,present,arity,kinds,layout,eq⟩ := primitive_application_exact_signature.mp seen
  exact .legacy (primitive_application_exact_signature.mpr ⟨d,present,by simpa using arity,kinds,layout,rfl⟩)

theorem read_point_key_accepts_actual_declared_unary {s key}
    (h : queryKeys s key = .covariantPoint) (q : Expr) :
    AuthoredApplication s key [q] (.nominal key [q]) := by
  obtain ⟨⟨u,mode⟩,table⟩ := query_point_key_uses_actual_declaration h
  exact (exact_declared_unary_application_at_original_key u mode table q).2

theorem authored_operator_functional {s key inputs x y}
    (a : AuthoredApplication s key inputs x)
    (b : AuthoredApplication s key inputs y) : x = y :=
  Option.some.inj (((compile_apply_exact ..).mpr a).symm.trans ((compile_apply_exact ..).mpr b))

/-- Shape-side criterion for one selected address. It does not choose a raw
row or a child; those stay in the authenticated ChildAt/AtStep premise.
Eligibility of any unvisited sibling is not a premise. -/
inductive CompiledOpening (s : CoreState) : Term → Expr → RawAddress → Prop
  | field : CompiledClosedSpine tail → CompiledOpening s t (.record l p tail) (.field f)
  | tag : CompiledOpening s t (.variant l p) (.variant l)
  | pair0 : CompiledOpening s t (.primitive .pair [p,q]) (.primitive .pair 0)
  | pair1 : CompiledOpening s t (.primitive .pair [p,q]) (.primitive .pair 1)
  | point : queryKeys s k = .covariantPoint →
    CompiledOpening s (.app k (.cons p .nil)) (.nominal k [q]) (.nominal k 0)

theorem compiled_scope_reflects_exact_selected_step {s t e sh addr c q}
    (author : AuthoredQuery s (writeTerm t) e)
    (scope : CompiledOpening s t e addr)
    (raw : ChildAt sh e addr c q) :
    ∃ u, Step (queryKeys s) t (writtenAddress addr) u ∧ AuthoredQuery s (writeTerm u) q := by
  have evidence : ∃ u, Step (queryKeys s) t (writtenAddress addr) u := by
    cases scope with
    | field closed =>
      cases raw with
      | field _ chosen =>
        obtain ⟨u,step,_⟩ := existing_field_address_reflects_original_closed_step author closed chosen
        exact ⟨u,step⟩
    | tag =>
      cases t
      case app key args =>
        change AuthoredQuery s (.app key (writeArgs args)) _ at author
        cases author with
        | app _ apply =>
          rcases authored_application_keeps_ordered_args apply with ⟨_,h⟩ | ⟨_,h⟩ <;> cases h
      case var | record | join => cases author
      case variant tag p =>
        change AuthoredQuery s (.variant tag (writeTerm p)) _ at author
        cases author
        exact ⟨_,.tag⟩
    | pair0 =>
      obtain ⟨_,p,_,rfl,yes,_,_⟩ := actual_authored_pair_is_written_pair author
      exact ⟨p,.pair0 yes⟩
    | pair1 =>
      obtain ⟨_,_,q,rfl,yes,_,_⟩ := actual_authored_pair_is_written_pair author
      exact ⟨q,.pair1 yes⟩
    | point mode => exact ⟨_,.point mode⟩
  obtain ⟨u,choose⟩ := evidence
  exact ⟨u,choose,same_authored_compilation_at_selected_child author choose raw⟩

theorem written_pair_compiles_real_pair_code {s key p q e}
    (mode : queryKeys s key = .binaryPair)
    (auth : AuthoredQuery s (writeTerm (.app key (.cons p (.cons q .nil)))) e) :
    ∃ first last, e = .primitive .pair [first,last] := by
  change AuthoredQuery s (.app key [writeTerm p,writeTerm q]) e at auth
  cases auth with
  | app items apply =>
    cases items with
    | cons first rest =>
      cases rest with
      | cons last stop =>
        cases stop
        exact ⟨_,_,authored_operator_functional apply (read_pair_key_accepts_any_two_compiled_operands mode _ _)⟩

theorem written_point_compiles_real_unary_code {s key p e}
    (mode : queryKeys s key = .covariantPoint)
    (auth : AuthoredQuery s (writeTerm (.app key (.cons p .nil))) e) :
    ∃ child, e = .nominal key [child] := by
  change AuthoredQuery s (.app key [writeTerm p]) e at auth
  cases auth with
  | app args apply =>
    cases args with
    | cons first rest =>
      cases rest
      exact ⟨_,authored_operator_functional apply (read_point_key_accepts_actual_declared_unary mode _)⟩

theorem written_step_has_exact_compiled_scope_at_address {s t u e sh addr c q a}
    (auth : AuthoredQuery s (writeTerm t) e)
    (raw : ChildAt sh e addr c q) (indexed : writtenAddress addr = a)
    (written : Step (queryKeys s) t a u) :
    CompiledOpening s t e addr := by
  cases written with
  | @field tail l k p q closed selected =>
    change AuthoredQuery s (.record k (writeTerm p) (writeTerm tail)) e at auth
    cases auth with
    | record _ compiledTail =>
      cases raw
      exact .field (closed_written_spine_compiles_closed closed compiledTail)
  | tag =>
    change AuthoredQuery s (.variant _ (writeTerm u)) e at auth
    cases auth
    cases raw
    exact .tag
  | pair0 mode =>
    obtain ⟨_,_,rfl⟩ := written_pair_compiles_real_pair_code mode auth
    cases raw
    simp only [writtenAddress,Address.arg.injEq] at indexed
    subst_vars
    exact .pair0
  | pair1 mode =>
    obtain ⟨_,_,rfl⟩ := written_pair_compiles_real_pair_code mode auth
    cases raw
    simp only [writtenAddress,Address.arg.injEq] at indexed
    subst_vars
    exact .pair1
  | point mode =>
    obtain ⟨_,rfl⟩ := written_point_compiles_real_unary_code mode auth
    cases raw
    simp only [writtenAddress,Address.arg.injEq] at indexed
    subst_vars
    exact .point mode

theorem compiled_scope_iff_independent_written_step {s t e sh addr c q}
    (auth : AuthoredQuery s (writeTerm t) e)
    (raw : ChildAt sh e addr c q) :
    CompiledOpening s t e addr ↔
      ∃ u, Step (queryKeys s) t (writtenAddress addr) u ∧ AuthoredQuery s (writeTerm u) q :=
  ⟨fun h => compiled_scope_reflects_exact_selected_step auth h raw,
   fun ⟨_,step,_⟩ => written_step_has_exact_compiled_scope_at_address auth raw rfl step⟩

end Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
