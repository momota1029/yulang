import Yulang.GeneralDeclarativeI65I75ProjectedCoreOutput425
import Yulang.GeneralDeclarativeI65I75ProjectedWriteWire425

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
open GeneralDeclarativeI65
open Checker408 (Problem)
open CommonNominalFullCarrier (Ty Equivalent)

/-- Recover the event-level original projection source from the
actual prepared data. This is the inversion towards the acyclic lower
module, not an import of the high reader from inside an Event. -/
def originalProjectedCoreOutput425 {p : Problem} (data : PreparedWrite p) :
    ProjectedCore425.Output p.state.core p.state.b6 p.root data.original.outIndex :=
  let r := data.original
  ⟨r.arg,r.request,r.low.label,endpointInputs423 r,r.fieldBinder,r.residualBinder,r.distinct,
    r.decl,r.only,r.ordinal,r.actualDecl,r.literal,r.assoc,data.typed.sourceBody,r.assocRhs,
    data.typed.plan,data.typed.originalCompiled⟩

theorem projected_core_output_preserves_original_B6_evaluation425
    {p : Problem} (data : PreparedWrite p) (m : I72.Model) :
    (originalProjectedCoreOutput425 data).valueAt m = data.typed.actualRightValue m :=
  rfl

/-- An exact current Write gives an acyclic typed output source with
literal B6 evaluation and fixed-target retention, all in the same
original State and model. Election and the canonical event constructor
are separate and are not assumed in this lemma. -/
theorem replayed_Write_yields_acyclic_core_and_fixed_target425
    {p : Problem} {tag wire offered data}
    (h : replayProjectedWrite425 p tag wire offered = some data)
    (m : I72.Model) (fit : I72.Fits p.state m) :
    let o := originalProjectedCoreOutput425 data
    o.ordinal = offered.declarationOrdinal ∧ o.plan = data.typed.plan ∧
    ∃ v : Ty, o.valueAt m =
      some (offered.occurrence,offered.declarationOrdinal,offered.outputOrdinal,offered.target.target,v) ∧
      Equivalent (m.assignment offered.target.target).1 v := by
  obtain ⟨_,original,same⟩ := replay_projected_write_requires_exact_original_write425.mp h
  subst offered
  obtain ⟨v,observed,retained⟩ := (read_retained_Pick_write_sound423 original).2 m fit
  exact ⟨rfl,rfl,v,observed,retained⟩

end Yulang.GeneralDeclarativeI65.I72.ProjectedRetention423
