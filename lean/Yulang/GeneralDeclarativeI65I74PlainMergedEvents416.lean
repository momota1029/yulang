import Yulang.GeneralDeclarativeI65I74PlainMergedRows416

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PlainMerged416
open GeneralDeclarativeI65
open ClosedResidual415 (ExactCandidate candidate_has_exact_input415)
open GeneralDeclarativeWitnessDeclaredState357 (point authoredRegistry)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeGraphRows321 (shapeOf)
open CommonNominalFullCarrier (Ty Equivalent common_union_is_join subtype_refl)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)

structure PlainRead {s q} (r : PlainRows s q) where
  candidate : ExactCandidate s q
  first : Nat
  second : Nat
  differentBinder : first ≠ second
  head : candidate.decl.head = [sourceX6 r.tag first second]
  noWhere : candidate.decl.requirements = []

def PlainRead.sourceHead {s q} {a : PlainRows s q} (r : PlainRead a) :
    SourceHead s.core q r.candidate.decl := by
  let capture := chosenPoint416 r.first r.second a.payload
  let code := GeneralNominalCenteredHeadMatExpressions.Expr.join
    (.variant a.tag (.variable r.first)) (.variant a.tag (.variable r.second))
  have built : translate (authoredRegistry s.core.current).constructors
      (interpretation s.core.current.environment.source.snapshot)
      (sourceX6 a.tag r.first r.second) = some code := rfl
  refine .ordered capture ?_
  rw [a.requested,r.head]
  have same1 := (two_binders_use_identical_actual_point416 r.first r.second a.payload).1
  have same2 := (two_binders_use_identical_actual_point416 r.first r.second a.payload).2
  refine .cons (.ordinary ⟨⟨.refl _, .refl _⟩,code,built,.direct (.structural ?_)⟩) .nil
  refine .join a.selfRow (.variant a.rootRow (.capture ?_ ?_))
    (.variant a.rootRow (.capture ?_ ?_))
  · simpa [capture,same1,point,GeneralDeclarativeHead320.byMode] using
      GeneralDeclarativeBounds319.Bound.refl a.payload
  · simpa [capture,same1,point,GeneralDeclarativeHead320.byMode] using
      GeneralDeclarativeBounds319.Bound.refl a.payload
  · simpa [capture,same2,point,GeneralDeclarativeHead320.byMode] using
      GeneralDeclarativeBounds319.Bound.refl a.payload
  · simpa [capture,same2,point,GeneralDeclarativeHead320.byMode] using
      GeneralDeclarativeBounds319.Bound.refl a.payload

def PlainRead.event {s q} {a : PlainRows s q} (r : PlainRead a) : Event s q :=
  ⟨r.candidate.frame (chosenPoint416 r.first r.second a.payload),r.sourceHead,fun i => by
    have h := i.isLt
    simp [a.noOutputs] at h⟩

theorem actual_plain_event_captures_same_whole_slot416 {s q} {a : PlainRows s q}
    (r : PlainRead a) :
    r.event.frame.names.input r.first = point a.payload ∧
    r.event.frame.names.input r.second = point a.payload := by
  change (r.candidate.frame _).names.input _ = _ ∧ (r.candidate.frame _).names.input _ = _
  rw [candidate_has_exact_input415,candidate_has_exact_input415]
  exact two_binders_use_identical_actual_point416 _ _ _

theorem actual_plain_event_has_no_where416 {s q} {a : PlainRows s q} (r : PlainRead a) :
    r.event.kids = [] := by
  simp [Event.kids,frameWhereKids400,children,AuthoredBodyFrame393.clauses,PlainRead.event,
    ExactCandidate.frame,r.noWhere]

theorem self_join_is_semantically_idempotent416 (v : Ty) : Equivalent v (.union v v) :=
  ⟨((common_union_is_join v v (.union v v)).mp (subtype_refl _)).1,
    (common_union_is_join v v v).mpr ⟨subtype_refl _,subtype_refl _⟩⟩

theorem idempotent_row_adds_no_model_requirement416 (payload : Nat) (m : I72.Model) :
    GeneralDeclarativeEntailment320.Holds m.assignment (idempotentRow payload) := by
  exact self_join_is_semantically_idempotent416 (m.assignment payload).1

theorem idempotent_row_is_not_a_raw_structural_edge416 (payload : Nat) :
    shapeOf (idempotentRow payload).right = none := rfl

theorem actual_integer_payload_is_int_in_every_fit416 {s q} (a : PlainRows s q)
    (m : I72.Model) (fit : Fits s m) : Equivalent (m.assignment a.payload).1 (.base .int) :=
  fit.1.1.2 _ a.intRow

end Yulang.GeneralDeclarativeI65.I72.PlainMerged416
