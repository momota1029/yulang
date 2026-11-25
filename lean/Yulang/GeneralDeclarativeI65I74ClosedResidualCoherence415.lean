import Yulang.GeneralDeclarativeI65I74ClosedResidualLocation415

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ClosedResidual415
open GeneralDeclarativeI65
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarations (Declaration Clause)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open Checker408 (Problem)

theorem exact_candidate_id_has_one_authored_ordinal415
    {s q r} (a : ExactCandidate s q) (b : ExactCandidate s r)
    (same : a.decl.id = b.decl.id) : a.ordinal = b.ordinal := by
  let ids := (authoredRegistry s.core.current).declarations.map Declaration.id
  have asRead : ids[a.ordinal]? = some a.decl.id := by
    simp [ids,List.getElem?_map,a.authored]
  have bsRead : ids[b.ordinal]? = some b.decl.id := by
    simp [ids,List.getElem?_map,b.authored]
  obtain ⟨inList,_⟩ := List.getElem_of_getElem? asRead
  exact (List.Nodup.getElem?_inj inList a.declarationIds).mp
    (asRead.trans ((congrArg some same).trans bsRead.symm))

/-- The exact same source problem cannot use a different declaration slot,
clause, child request, or capture address just by picking different wire
coordinates. Comparing different source registries is not assumed. -/
theorem exact_verified_residual_location_coheres415 {p : Problem}
    (a b : VerifiedClosed p) : a.location = b.location := by
  let d := a.parent.candidate
  let e := b.parent.candidate
  let c := a.child.candidate
  let f := b.child.candidate
  have parentEq : d.decl = e.decl := (List.cons.inj (d.visibleOne.symm.trans e.visibleOne)).1
  have sameParents := exact_candidate_id_has_one_authored_ordinal415 d e (congrArg Declaration.id parentEq)
  have clauseEqual := (List.cons.inj (a.parent.clause.symm.trans
    ((congrArg Declaration.requirements parentEq).trans b.parent.clause))).1
  have roleSame : a.parent.childRole = b.parent.childRole := congrArg Clause.role clauseEqual
  have clauseId : a.parent.clauseID = b.parent.clauseID := congrArg Clause.id clauseEqual
  have parentBinder := Pattern.var.inj (List.cons.inj (congrArg Clause.arguments clauseEqual)).1
  have first := c.visibleOne
  have second := f.visibleOne
  change ((authoredRegistry p.state.core.current).declarations.filter
    (fun row => row.role == a.parent.childRole)) = [c.decl] at first
  change ((authoredRegistry p.state.core.current).declarations.filter
    (fun row => row.role == b.parent.childRole)) = [f.decl] at second
  have sameVisible := congrArg (fun role => (authoredRegistry p.state.core.current).declarations.filter
    (fun row => row.role == role)) roleSame
  have childEq : c.decl = f.decl := (List.cons.inj (first.symm.trans (sameVisible.trans second))).1
  have sameChildren := exact_candidate_id_has_one_authored_ordinal415 c f (congrArg Declaration.id childEq)
  have childPattern := (List.cons.inj (a.child.literal.symm.trans
    ((congrArg Declaration.head childEq).trans b.child.literal))).1
  have childBinder : a.child.binder = b.child.binder :=
    Pattern.var.inj (Pattern.record.inj childPattern).2.1
  obtain ⟨root,remove,_prefix,keep,_value,resid⟩ := original_coordinate_is_independent_of_wire415 a.rows b.rows
  change ResidualLocation.mk _ _ _ _ _ _ d.decl.id d.ordinal c.decl.id c.ordinal _ _ _ =
    ResidualLocation.mk _ _ _ _ _ _ e.decl.id e.ordinal f.decl.id f.ordinal _ _ _
  congr 1
  all_goals first
    | exact root
    | exact remove
    | exact keep
    | exact resid
    | exact congrArg Declaration.id parentEq
    | exact sameParents
    | exact congrArg Declaration.id childEq
    | exact sameChildren
    | exact clauseId
    | exact parentBinder
    | exact childBinder
    | rfl

theorem all_original_replayed_location_coordinates_unique415 (p : Problem) {a b : ResidualLocation}
    {w u : ClosedWire} (aAt : locate p w = some a) (bAt : locate p u = some b) : a = b := by
  unfold locate at aAt bAt
  cases left : replayClosed415 p w with
  | none => simp [left] at aAt
  | some x =>
    cases right : replayClosed415 p u with
    | none => simp [right] at bAt
    | some y =>
      simp only [left,Option.map_some,Option.some.injEq] at aAt
      simp only [right,Option.map_some,Option.some.injEq] at bAt
      exact aAt.symm.trans ((exact_verified_residual_location_coheres415 x y).trans bAt)

end Yulang.GeneralDeclarativeI65.I72.ClosedResidual415
