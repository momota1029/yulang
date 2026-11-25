import Yulang.GeneralDeclarativeI65I74RecordEndpointsBoundary422

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RecordEndpoints422
open GeneralDeclarativeI65
open CommonNominalFullCarrier (Equivalent)
open CommonRoleOutermostResolver (Dictionary)
open GeneralDeclarativeHead320 (Models)

/-- No enlargement that changes only `SourcePrimitives` can represent
this selected record. Any selected trace still carries the fixed
SourceHead of the same visible declaration. This is not a source
rejection rule and yields no rejected or pending classification. -/
theorem primitives_only_cannot_add_genuine_nonpoint_record_selection422 {p}
    (r : Read p) (absent : NoCenterRecord r)
    (m : I72.Model) (fit : Models p.state.core.current.ordinary m.assignment)
    (unequal : ¬ Equivalent (m.assignment r.arg.lower).1 (m.assignment r.arg.upper).1)
    (R : SourcePrimitives) (d : Dictionary) : ¬ I72.Classifies R p.state p.root (.selected d) := by
  rintro ⟨_,_,⟨trace⟩,summary⟩
  cases trace with
  | rootK2 _ => cases summary
  | other verdict _ _ _ => cases verdict <;> cases summary
  | selected event _ _ _ _ =>
    have same : event.frame.decl = r.decl := by simpa [r.only] using event.frame.inScope
    exact genuine_nonpoint_endpoint_record_has_no_fixed_source_head422 r absent m fit unequal
      ⟨same ▸ event.head⟩

end Yulang.GeneralDeclarativeI65.I72.RecordEndpoints422
