import Yulang.GeneralDeclarativeI65I74PreparedHeadField463

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PhysicalVisit463.IssuedProjection464
open Yulang.GeneralDeclarativeI65
open WrittenPattern460
open GeneralDeclarativeHead320 (Equation)
open RecordTraversal455.MixedQA (Address)
open RecordTrail455 (RoutedOpen)
open RecordTrail455.MixedNative456
open RoutedNominalPoint456

/-- No existing hop policy can obtain author identity from graph equations
alone. This lists proof cases of existing authentication, not new lanes. -/
theorem each_existing_raw_open_has_issued_origin_at_its_physical_owner
    {s : CoreState} {root : Nat} {row : Equation} {a : RecordTraversal455.MixedQA.Address} {c : Nat} {stamp : Bool}
    (w : InlineStructuralPolicy458.allows s root row a c stamp) :
    ∃ origin ∈ s.origins, OriginRoute s origin root ∧ origin.slot = row.left := by
  cases stamp with
  | false =>
    obtain ⟨prior,w⟩ := w
    cases prior with
    | false =>
      change ((extraOpenOps s).allowed root row ∨ Nonempty (Opened s root row)) at w
      rcases w with ext | nonempty
      · change RoutedOpen s root row ∨ AuthorizedExtra s root row at ext
        rcases ext with ⟨o,mem,route,_,physical,_,_⟩ | ⟨o,mem,route,physical,_,_,_⟩
        · exact ⟨o,mem,route,physical⟩
        · exact ⟨o,mem,route,physical⟩
      · obtain ⟨nom⟩ := nonempty
        exact ⟨nom.origin,nom.authored,nom.original,nom.physical⟩
    | true =>
      obtain ⟨_,_,_,_,_,_,par,pHere,_,_,rest⟩ := w.2
      exact ⟨par,pHere,rest.1,rest.2.1⟩
  | true =>
    change InlineStructuralPolicy458.NewAuthority s root row a c at w
    rcases w with pair | field | nom
    · obtain ⟨_,par,pHere,_,_,_,_,_,_,route,place,_⟩ := pair
      exact ⟨par,pHere,route,place⟩
    · obtain ⟨_,_,field⟩ := field
      obtain ⟨_,_,_,_,_,_,_,_,_,_,par,pHere,_,_,rest⟩ := field
      exact ⟨par,pHere,rest.2.1,rest.1⟩
    · obtain ⟨_,_,_,_,_,_,_,par,pHere,_,_,rest⟩ := nom
      exact ⟨par,pHere,rest.2.1,rest.1⟩

theorem no_physical_opening_at_any_site_without_original_owner_row
    {s : CoreState} (missing : s.origins = []) {root code i addr child next mark}
    (h : IndexedOpen s.current.ordinary (InlineStructuralPolicy458.policy s)
      root code i addr child next mark) : False := by
  obtain ⟨row,sh,ord,alias,form,child,p⟩ := h.actual
  obtain ⟨o,fromActual,route,place⟩ := each_existing_raw_open_has_issued_origin_at_its_physical_owner p
  rw [missing] at fromActual
  cases fromActual

theorem without_issued_origin_a_finite_existing_trail_can_only_stop
    {s : CoreState} (missing : s.origins = []) {keys root t code path rows terminal last mark}
    (h : IndexedJoint s.current.ordinary (InlineStructuralPolicy458.policy s)
      keys root t code path rows terminal last mark) : path = [] := by
  cases h with
  | stop => rfl
  | down _ source _ _ => exact (no_physical_opening_at_any_site_without_original_owner_row missing source).elim


open RecordTraversal455.MixedQA (ChildAt)
open RoutedInlineStructural458 (ModelOpening)
open GeneralDeclarativeGraphRows321 (shapeOf)
open GeneralDeclarativeK2Graph321 (Shape)

/-- The addressed hop in the original evidence uses exactly the ordinal at
that hop, not just an equation of equal value or another origin at that slot. -/
theorem selected_index_keeps_the_exact_issued_owner_in_the_same_fit
    {s : CoreState} {keys root t code path rows terminal last stamp}
    (run : IndexedJoint s.current.ordinary (InlineStructuralPolicy458.policy s)
      keys root t code path rows terminal last stamp)
    (m : I72.Model) (fit : GeneralDeclarativeI65.Fits s m)
    {step ix : Nat} (pick : rows[step]? = some ix) :
    ∃ here query row shape addr child next used origin,
      path[step]? = some (addr,child) ∧
      s.current.ordinary.equations[ix]? = some row ∧
      GeneralDeclarativeLowerKnown321.Alias s.current.ordinary here row.left ∧
      shapeOf row.right = some shape ∧ ChildAt shape query addr child next ∧
      InlineStructuralPolicy458.allows s here row addr child used ∧
      origin ∈ s.origins ∧ OriginRoute s origin here ∧ origin.slot = row.left ∧
      m.nativeSyntax origin.slot = some origin.endpoint ∧
      ModelOpening s m here row shape query addr child next used := by
  induction run generalizing step with
  | stop _ => simp at pick
  | @down start query ordinal addr child next mark term selected path orders terminal last used safe bound wrote tail ih =>
    cases step with
    | zero =>
      have eq : ordinal = ix := Option.some.inj pick
      subst ix
      obtain ⟨row,form,stored,alias,shape,chosen,allowed⟩ := bound.actual
      obtain ⟨origin,seen,route,owner⟩ := each_existing_raw_open_has_issued_origin_at_its_physical_owner allowed
      exact ⟨start,query,row,form,addr,child,next,mark,origin,rfl,stored,alias,shape,chosen,
        allowed,seen,route,owner,fit.2 origin seen,
        existing_authorized_opening_preserves_the_very_same_raw_row shape chosen allowed m fit⟩
    | succ index =>
      exact ih pick

end Yulang.GeneralDeclarativeI65.I72.PhysicalVisit463.IssuedProjection464
