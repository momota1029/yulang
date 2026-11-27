import Yulang.GeneralDeclarativeI65I74CompiledFieldReflection460

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
open AuthoredInspectQuery456 (AuthoredQuery AuthoredQueries AuthoredApplication legacyApply)
open GeneralNominalCenteredHeadMatExpressions (Expr application)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralCandidateInspection (Primitive)

theorem primitive_application_exact_signature {s key xs ys} {op : Primitive} :
    legacyApply s key xs = some (.primitive op ys) ↔
      ∃ decl, (authoredRegistry s.current).constructors key = some decl ∧
      decl.parameters.length = xs.length ∧
      (interpretation s.current.environment.source.snapshot).primitives key = some op ∧
      decl.parameters = op.parameters ∧ xs = ys := by
  constructor
  · intro seen
    cases present : (authoredRegistry s.current).constructors key with
    | none => simp [legacyApply,application,present,Option.bind] at seen
    | some decl =>
      by_cases arity : decl.parameters.length = xs.length
      · cases primitive : (interpretation s.current.environment.source.snapshot).primitives key with
        | none =>
          by_cases inv : (interpretation s.current.environment.source.snapshot).invariantNominal key = true ∧
              decl.parameters = List.replicate xs.length .type <;>
            simp [legacyApply,application,present,Option.bind,arity,primitive,inv] at seen
        | some prim =>
          by_cases layout : decl.parameters = prim.parameters
          · have arity' : prim.parameters.length = xs.length := layout ▸ arity
            have eq : Expr.primitive prim xs = .primitive op ys := by
              simpa [legacyApply,application,present,Option.bind,arity,primitive,layout,arity'] using seen
            obtain ⟨rfl,rfl⟩ := Expr.primitive.inj eq
            exact ⟨decl,rfl,arity,rfl,layout,rfl⟩
          · simp [legacyApply,application,present,Option.bind,arity,primitive,layout] at seen
      · simp [legacyApply,application,present,Option.bind,arity] at seen
  · rintro ⟨decl,present,arity,primitive,layout,rfl⟩
    have arity' : op.parameters.length = xs.length := layout ▸ arity
    simp [legacyApply,application,present,Option.bind,primitive,layout,arity']

theorem legacy_pair_emits_real_original_pair_key {s key a b} :
    legacyApply s key [a,b] = some (.primitive .pair [a,b]) →
      queryKeys s key = .binaryPair := by
  intro h
  obtain ⟨d,lookup,arity,op,layout,_⟩ := primitive_application_exact_signature.mp h
  have probe : legacyApply s key [.variable 0,.variable 0] =
      some (.primitive .pair [.variable 0,.variable 0]) :=
    primitive_application_exact_signature.mpr ⟨d,lookup,by simpa using arity,op,layout,rfl⟩
  have notEmpty : emptyKey s key = false := by
    cases he : emptyKey s key
    · rfl
    · have h : queryKeys s key = .emptyRow := by simp [queryKeys,he]
      obtain ⟨_,_,_,opEmpty,_,_⟩ := primitive_application_exact_signature.mp (query_empty_key_exact.mp h)
      rw [op] at opEmpty
      cases opEmpty
  have ep : pairKey s key = true := by
    change (match legacyApply s key [.variable 0,.variable 0] with
      | some (.primitive .pair [_,_]) => true | _ => false) = true
    rw [probe]
  simp [queryKeys,notEmpty,ep]

theorem actual_authored_pair_is_written_pair {s t p q}
    (auth : AuthoredQuery s (writeTerm t) (.primitive .pair [p,q])) :
    ∃ key first second, t = .app key (.cons first (.cons second .nil)) ∧
        queryKeys s key = .binaryPair ∧
        AuthoredQuery s (writeTerm first) p ∧ AuthoredQuery s (writeTerm second) q := by
  cases t
  case var | variant | record | join => cases auth
  case app k xs =>
    change AuthoredQuery s (.app k (writeArgs xs)) (.primitive .pair [p,q]) at auth
    cases auth with
    | app items app =>
      rcases authored_application_keeps_ordered_args app with ⟨_,same⟩ | ⟨_,wrong⟩
      · obtain ⟨rfl,rfl⟩ := Expr.primitive.inj same
        cases xs with
        | nil => cases items
        | cons first tail =>
          cases tail with
          | nil => cases items with | cons _ t => cases t
          | cons second rest =>
            cases rest with
            | nil =>
              cases items with
              | cons left middle =>
                cases middle with
                | cons right _ =>
                  cases app with
                  | legacy found =>
                    exact ⟨k,first,second,rfl,legacy_pair_emits_real_original_pair_key found,left,right⟩
            | cons elseArg elseRest =>
              cases items with | cons _ more =>
                cases more with | cons _ excess => cases excess
      · cases wrong

end Yulang.GeneralDeclarativeI65.I72.WrittenPattern460
