import Yulang.GeneralDeclarativeI65I74PlainMergedPriority416

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PlainMerged416
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open ClosedResidual415 (exact_candidate_id_has_one_authored_ordinal415)
open CommonNominalFullCarrier (Equivalent)
open GeneralDeclarativeWhere319 (Capture)
open Checker408 (Problem)

structure PlainLocation where
  occurrence : List Nat
  declaration : Nat
  ordinal : Nat
  root : Nat
  tag : Nat
  payload : Nat
  first : Nat
  second : Nat
  deriving DecidableEq, Repr

def VerifiedPlain.location {p : Problem} (v : VerifiedPlain p) : PlainLocation :=
  ⟨p.root.occurrence,v.actual.candidate.decl.id,v.actual.candidate.ordinal,
    v.rows.root,v.rows.tag,v.rows.payload,v.actual.first,v.actual.second⟩

def locate (p : Problem) (w : PlainWire) : Option PlainLocation :=
  (replayPlain416 p w).map VerifiedPlain.location

theorem canonical_variant_original_coordinates_unique416 {s q} (a b : PlainRows s q) :
    a.root = b.root ∧ a.tag = b.tag ∧ a.payload = b.payload := by
  have roots : a.root = b.root := congrArg Capture.lower
    (List.cons.inj (a.requested.symm.trans b.requested)).1
  obtain ⟨only,found⟩ := List.length_eq_one_iff.mp a.originalCount
  have left : a.source ∈ s.core.origins.filter (fun r => r.slot == a.root) :=
    List.mem_filter.mpr ⟨a.actualSource,by simp [a.sourceRoot]⟩
  have right : b.source ∈ s.core.origins.filter (fun r => r.slot == a.root) :=
    List.mem_filter.mpr ⟨b.actualSource,by simp [b.sourceRoot,roots]⟩
  rw [found] at left right
  have sameOrigin := (List.mem_singleton.mp left).trans (List.mem_singleton.mp right).symm
  have endpoints := a.literal.symm.trans ((congrArg Origin.endpoint sameOrigin).trans b.literal)
  have outer := Core.PresenceGeneration.TyTerm.variant.inj
    (CommonRecursiveNominalIntervals.Endpoint.ordinary.inj endpoints)
  exact ⟨roots,outer.1,Core.PresenceGeneration.TyTerm.var.inj outer.2⟩

theorem actual_merged_location_cannot_swap_source_names416 {p : Problem} (a b : VerifiedPlain p) :
    a.location = b.location := by
  let d := a.actual.candidate
  let e := b.actual.candidate
  have exactRow : d.decl = e.decl := (List.cons.inj (d.visibleOne.symm.trans e.visibleOne)).1
  have id := congrArg Declaration.id exactRow
  have sameOrdinal := exact_candidate_id_has_one_authored_ordinal415 d e id
  have both := Pattern.join.inj (List.cons.inj (a.actual.head.symm.trans
    ((congrArg Declaration.head exactRow).trans b.actual.head))).1
  have aEq := Pattern.var.inj (Pattern.variant.inj both.1).2
  have bEq := Pattern.var.inj (Pattern.variant.inj both.2).2
  obtain ⟨root,tag,name⟩ := canonical_variant_original_coordinates_unique416 a.rows b.rows
  change PlainLocation.mk _ d.decl.id d.ordinal _ _ _ _ _ =
    PlainLocation.mk _ e.decl.id e.ordinal _ _ _ _ _
  congr 1
  all_goals first
    | exact id | exact sameOrdinal | exact root | exact tag | exact name | exact aEq | exact bEq

theorem different_wire_coordinates_cannot_change_captured_payload416
    (p : Problem) {a b : PlainLocation} {w v : PlainWire}
    (first : locate p w = some a) (second : locate p v = some b) : a = b := by
  unfold locate at first second
  cases l : replayPlain416 p w with
  | none => simp [l] at first
  | some x =>
    cases r : replayPlain416 p v with
    | none => simp [r] at second
    | some y =>
      simp only [l,Option.map_some,Option.some.injEq] at first
      simp only [r,Option.map_some,Option.some.injEq] at second
      exact first.symm.trans ((actual_merged_location_cannot_swap_source_names416 x y).trans second)

theorem both_original_binders_read_same_integer_payload_in_every_fit416
    {p : Problem} (v : VerifiedPlain p) (m : I72.Model) (fit : Fits p.state m) :
    (v.actual.event.frame.names.input v.actual.first = point v.rows.payload ∧
     v.actual.event.frame.names.input v.actual.second = point v.rows.payload) ∧
    Equivalent (m.assignment v.rows.payload).1 (.base .int) := by
  exact ⟨actual_plain_event_captures_same_whole_slot416 v.actual,
    actual_integer_payload_is_int_in_every_fit416 v.rows m fit⟩

end Yulang.GeneralDeclarativeI65.I72.PlainMerged416
