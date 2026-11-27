import Yulang.GeneralDeclarativeI65I74IssuedProjection464

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PhysicalVisit463.IssuedProjection464
open Yulang.GeneralDeclarativeI65
open WrittenPattern460
open RecordTraversal455.MixedQA (MixedPath)
open GeneralDeclarativeHead320 (Equation)

/-- The zero-th hop begins at the original centre; every later one begins
at the exact previous selected child, not a semantically equal replacement. -/
def logicalBeforeHop (root : Nat) (path : MixedPath) : Nat → Option Nat
  | 0 => some root
  | n + 1 => (path[n]?).map Prod.snd

/-- This strengthens indexed traversal with the exact input site at the
selected ordinal. It is independent of any fitting assignment or new graph. -/
theorem indexed_logical_site_is_the_previous_selected_child
    {s : CoreState} {keys root t code path rows terminal last stamp}
    (run : IndexedJoint s.current.ordinary (InlineStructuralPolicy458.policy s)
      keys root t code path rows terminal last stamp)
    {step ix : Nat} (pick : rows[step]? = some ix) :
    ∃ here query addr child next used,
      logicalBeforeHop root path step = some here ∧
      path[step]? = some (addr,child) ∧
      IndexedOpen s.current.ordinary (InlineStructuralPolicy458.policy s)
        here query ix addr child next used := by
  induction run generalizing step with
  | stop _ => simp at pick
  | @down start query ordinal a c next mark term selected path orders terminal last used safe bound wrote tail ih =>
    cases step with
    | zero =>
      have eq : ordinal = ix := Option.some.inj pick
      subst ix
      exact ⟨start,query,a,c,next,mark,rfl,rfl,bound⟩
    | succ k =>
      obtain ⟨here,q,addr,child,out,flag,source,atChild,old⟩ := ih pick
      cases k with
      | zero => exact ⟨here,q,addr,child,out,flag,source,atChild,old⟩
      | succ n => exact ⟨here,q,addr,child,out,flag,source,atChild,old⟩

open PreparedDeclarations463
open Checker408 (Problem)

theorem every_successful_field_receipt_uses_the_very_same_previous_logical_site
    {p : Problem} {tab : CheckedTable p.state.core.current} {w : HeadFieldWire p} {r : HeadFieldReceipt}
    (read : readHeadField (p := p) tab w = some r)
    {capture : GeneralDeclarativeWhere319.Capture}
    (centre : p.root.demand.arguments[r.authored.headArgument]? = some capture)
    {step ordinal logical : Nat}
    (row : r.rows[step]? = some ordinal)
    (atSite : logicalBeforeHop capture.lower r.path step = some logical) :
    ∃ stored, p.state.core.current.ordinary.equations[ordinal]? = some stored ∧
      GeneralDeclarativeLowerKnown321.Alias p.state.core.current.ordinary logical stored.left ∧
      ∃ o ∈ p.state.core.origins, OriginRoute p.state.core o logical ∧ o.slot = stored.left := by
  obtain ⟨a,last,located,walk,_,_,_⟩ := (prechecked_head_field_iff_finite_exact_wire ..).mpr ⟨w,read⟩
  have same : a.orig.capture = capture := Option.some.inj
    (a.orig.actualArgument.symm.trans (by rw [located]; exact centre))
  obtain ⟨here,query,addr,child,next,mark,prior,chosen,actual⟩ :=
    indexed_logical_site_is_the_previous_selected_child walk row
  rw [same, atSite] at prior
  have identical := Option.some.inj prior
  subst here
  obtain ⟨e,shape,physical,alias,formed,coincides,author⟩ := actual.actual
  exact ⟨e,physical,alias,each_existing_raw_open_has_issued_origin_at_its_physical_owner author⟩

end Yulang.GeneralDeclarativeI65.I72.PhysicalVisit463.IssuedProjection464
