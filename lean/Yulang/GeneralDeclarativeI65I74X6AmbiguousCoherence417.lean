import Yulang.GeneralDeclarativeI65I74X6AmbiguousLocator417
import Yulang.GeneralDeclarativeI65I74PlainMergedLocation416

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.X6Ambiguous417
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeWitnessDeclaredState357 (point authoredRegistry)
open GeneralNominalCenteredHeadMatExpressions (translate translateMany)
open GeneralSourceMetadataRows291 (interpretation)
open CommonNominalFullCarrier (Equivalent)
open PlainMerged416 (PlainRows sourceX6)

theorem literal_plain_and_ground_never_share_one_author417 {s q} {r t : PlainRows s q}
    (plain : PlainHit r) (ground : GroundHit t) :
    plain.candidate.decl ≠ ground.candidate.decl := by
  intro same
  have impossible := (List.cons.inj (plain.head.symm.trans
    ((congrArg Declaration.head same).trans ground.head))).1
  change Pattern.join _ _ = Pattern.variant _ _ at impossible
  cases impossible

theorem witnessed_ambiguity_cannot_swap_either_actual_declaration417 {s q}
    (a b : Ambiguous s q) :
    a.plain.candidate.decl = b.plain.candidate.decl ∧
    a.ground.candidate.decl = b.ground.candidate.decl := by
  have left := (actual_matching_candidates_are_exactly_two417 b _).mp a.plain.candidate.found
  have right := (actual_matching_candidates_are_exactly_two417 b _).mp a.ground.candidate.found
  exact ⟨left.resolve_right (literal_plain_and_ground_never_share_one_author417 a.plain b.ground),
    right.resolve_left (Ne.symm (literal_plain_and_ground_never_share_one_author417 b.plain a.ground))⟩

structure SourceLocation where
  occurrence : List Nat
  root : Nat
  tag : Nat
  payload : Nat
  leftBinder : Nat
  rightBinder : Nat
  plainId : Nat
  groundId : Nat
  intCtor : Nat
  deriving DecidableEq, Repr

def Ambiguous.location {s q} (a : Ambiguous s q) : SourceLocation :=
  ⟨q.occurrence,a.rows.root,a.rows.tag,a.rows.payload,a.plain.first,a.plain.second,
    a.plain.candidate.decl.id,a.ground.candidate.decl.id,a.ground.intName⟩

theorem ambiguity_uses_one_original_logical_source417 {s q} (a b : Ambiguous s q) :
    a.location = b.location := by
  obtain ⟨roots,tags,payloads⟩ := PlainMerged416.canonical_variant_original_coordinates_unique416 a.rows b.rows
  obtain ⟨plain,ground⟩ := witnessed_ambiguity_cannot_swap_either_actual_declaration417 a b
  have pHeads := Pattern.join.inj (List.cons.inj (a.plain.head.symm.trans
    ((congrArg Declaration.head plain).trans b.plain.head))).1
  have gHeads := Pattern.variant.inj (List.cons.inj (a.ground.head.symm.trans
    ((congrArg Declaration.head ground).trans b.ground.head))).1
  have binder1 := Pattern.var.inj (Pattern.variant.inj pHeads.1).2
  have binder2 := Pattern.var.inj (Pattern.variant.inj pHeads.2).2
  have ctor := (Pattern.app.inj gHeads.2).1
  unfold Ambiguous.location
  rw [roots,tags,payloads,binder1,binder2,plain,ground,ctor]

theorem in_each_fitting_model_both_binders_and_the_ground_head_share_the_original_int417 {s q}
    (a : Ambiguous s q) (m : I72.Model) (fit : Fits s m) :
    (a.plain.event.frame.names.input a.plain.first = point a.rows.payload ∧
      a.plain.event.frame.names.input a.plain.second = point a.rows.payload) ∧
    Equivalent (m.assignment a.rows.payload).1 (.base .int) ∧
    HeadModel s.core m q a.ground.candidate.decl a.ground.originalHead := by
  exact ⟨plain_has_both_captures_on_actual_payload417 a.plain,
    PlainMerged416.actual_integer_payload_is_int_in_every_fit416 a.rows m fit,
    (the_two_candidate_heads_hold_in_the_very_same_model417 a.plain a.ground m fit).2⟩

theorem actual_normalized_codes_of_both_candidates417 {s q} (a : Ambiguous s q) :
    (a.plain.candidate.decl.head.map fun form =>
      translate (authoredRegistry s.core.current).constructors
        (interpretation s.core.current.environment.source.snapshot) (normalize form)) =
      [some (PlainMerged416.mergedCode a.rows.tag a.plain.first a.plain.second)] ∧
    (a.ground.candidate.decl.head.map fun form =>
      translate (authoredRegistry s.core.current).constructors
        (interpretation s.core.current.environment.source.snapshot) (normalize form)) =
      [some (groundCode a.rows.tag)] := by
  constructor
  · rw [a.plain.head]
    simp only [List.map_cons,List.map_nil,
      PlainMerged416.two_literal_plain_arms_normalize_to_one_actual_tag416 _ _ _ a.plain.unlike]
    rfl
  · rw [a.ground.head]
    have fixed : normalize (groundSyntax a.rows.tag a.ground.intName) =
      groundSyntax a.rows.tag a.ground.intName := rfl
    simp only [List.map_cons,List.map_nil,fixed]
    simp [groundSyntax,groundCode,translate,translateMany,a.ground.kind]

theorem both_real_candidates_have_no_where_children417 {s q} (a : Ambiguous s q) :
    a.plain.event.kids = [] ∧ a.ground.event.kids = [] := by
  constructor
  · simp [Event.kids,frameWhereKids400,children,AuthoredBodyFrame393.clauses,PlainHit.event,
      Candidate.frame,a.plain.candidate.noWhere]
  · simp [Event.kids,frameWhereKids400,children,AuthoredBodyFrame393.clauses,GroundHit.event,
      Candidate.frame,a.ground.candidate.noWhere]

end Yulang.GeneralDeclarativeI65.I72.X6Ambiguous417
