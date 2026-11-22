import Yulang.GeneralDeclarativeCurrentOrder345
import Yulang.GeneralNominalVersionedMixedReady235

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCurrentSnapshot345
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralDictionaryAssociatedProvenance (Body lookup)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary checked_compiled)
open GeneralNominalCenteredHeadMatStepRoles (Origin Invariant alias_color color_of_origin)
open GeneralNominalCenteredHeadMatEffects (Ready compileBody bodySchema)
open GeneralNominalCenteredHeadOutputs (requests mem_requests_iff)
open GeneralNominalCenteredHeadDefaultSchemas (RequestsDeclared)
open GeneralDeclarativeCurrentOrder345 (Row rows exact_row)
open GeneralNominalSaturationState (Alias)

theorem row_origin {r : Registry} {root focus : Occurrence rs}
    {core : GeneralNominalCenteredSteps.State rs} (checked : Checked r)
    (valid : Invariant r seed root core) (focusOrigin : Origin r seed root focus)
    (row : Row) (member : row ∈ rows core focus) :
    ∃ site : GeneralNominalDemandMerging.Site rs,
      core.erased.current.sites[row.physical]? = some site ∧
      site.occurrence.demand.outputs[row.ordinal]? = some row.output ∧
      Alias core.erased.current focus.identity site.occurrence.identity ∧
      Origin r seed root site.occurrence ∧ focus.demand.role = site.occurrence.demand.role := by
  obtain ⟨site,physical,ordinal,alias⟩ := exact_row.mp member
  have owns := valid.raw _ (List.mem_iff_getElem?.mpr ⟨_,physical⟩)
  have eq := alias_color valid alias
  rw [color_of_origin checked focusOrigin,color_of_origin checked owns] at eq
  exact ⟨site,physical,ordinal,alias,owns,eq⟩

/-- Current output obligations are attached to the contributing physical
site. They do not require a birth-output coincidence or a previous cache
record; an actual current frame and checked source reachability suffice. -/
theorem from_reached_frame {r : Registry} {root focus : Occurrence rs}
    {state : State rs} {p : Plan rs}
    (checked : (boundary rs).Checked r)
    (path : B4TargetV8.Reachable (boundary rs) r root state)
    (frame : Frame (registry r) state.core focus key p) :
    RequestsDeclared state.core focus p ∧ Ready state.core focus p ∧
    ∀ row ∈ rows state.core focus,
      ∃ (site : GeneralNominalDemandMerging.Site rs) (body : Body) (code : Expr),
        state.core.erased.current.sites[row.physical]? = some site ∧
        site.occurrence.demand.outputs[row.ordinal]? = some row.output ∧
        Alias state.core.erased.current focus.identity site.occurrence.identity ∧
        Origin (registry r) state.core.erased.source.state.seed root site.occurrence ∧
        lookup rs p.packet.declaration row.output.name = some body ∧
        compileBody p body = some code := by
  have invariant := GeneralNominalVersionedMixedRoles235.reachable checked path
  have origin : Origin (registry r) state.core.erased.source.state.seed root focus :=
    frame.occurrence_eq ▸ invariant.raw _ frame.raw_recorded
  have declared := GeneralDeclarativeCurrentRequest345.declared (p := p) (checked_compiled checked).2
    invariant origin frame.role_eq
  have ready := GeneralNominalVersionedMixedReady235.ready checked path frame
  refine ⟨declared,ready,?_⟩
  intro row member
  obtain ⟨site,physical,ordinal,alias,author,_⟩ := row_origin (checked_compiled checked).2 invariant origin row member
  have hits := mem_requests_iff.mpr ⟨site,List.mem_iff_getElem?.mpr ⟨_,physical⟩,alias,
    List.mem_iff_getElem?.mpr ⟨_,ordinal⟩⟩
  obtain ⟨body,found,compiled⟩ := ready row.output hits
  cases h : compileBody p body with
  | none => simp [bodySchema,h] at compiled
  | some code => exact ⟨site,body,code,physical,ordinal,alias,author,found,h⟩

end Yulang.GeneralDeclarativeCurrentSnapshot345
