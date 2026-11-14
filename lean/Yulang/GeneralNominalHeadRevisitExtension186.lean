import Yulang.GeneralNominalHeadBinderCollisions186
import Yulang.GeneralNominalHeadTestSemantic186
import Yulang.GeneralNominalHeadFrameExtension186

/-! A revisited candidate has historical tests and actual observations.
Its entire conservative head extension is equivalent to the remaining current
capture Fits checks. These bounds are not asserted automatically from choice. -/
namespace Yulang.GeneralNominalHeadRevisitExtension186
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadOutputs (Frame HeadEquations)
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalRecursiveInspection (Observes)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalHeadConservativeExtension186 (support)
open GeneralNominalHeadEquationExtension186 (uses uses_mem Compatible)
variable {roles : Roles.RoleDecls} {registry : Registry} {root focus : Occurrence roles}
variable {state : State roles}

def BoundsFit (candidate : Plan roles) (model : Assignment) : Prop :=
  ∀ index value, Observes model (uses candidate index).origin value →
    GeneralNominalCaptureMerges.Fits model
      ((GeneralNominalPacketSupport.capture candidate.packet).inputs (uses candidate index).name) value

theorem compatible_iff_bounds (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (registered : candidate.input ∈ state.core.sites)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (current : candidate.packet.context = state.core.erased.current.context)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (model : Assignment) (valid : Models state model) :
    Compatible candidate model ↔ BoundsFit candidate model := by
  constructor
  · exact fun compatible => compatible.2.2.1
  · intro bounds
    refine ⟨?_,?_,bounds,?_⟩
    · exact GeneralNominalHeadTestSemantic186.candidate_tests checked reachable historical candidate
        member registered identity current declaration model valid
    · intro index
      exact (GeneralNominalHeadCandidateSemantic186.candidate_actual checked reachable historical candidate
        member registered identity current declaration (uses candidate index) (uses_mem candidate index)
        (GeneralNominalHeadSchemaNames186.head_actual candidate _ (uses_mem candidate index)) model valid).1
    · intro i j first last same one two
      exact GeneralNominalHeadBinderCollisions186.historical_coherence checked reachable historical candidate
        member registered identity current declaration (uses candidate i) (uses candidate j)
        (uses_mem candidate i) (uses_mem candidate j)
        (GeneralNominalHeadSchemaNames186.head_actual candidate _ (uses_mem candidate i))
        (GeneralNominalHeadSchemaNames186.head_actual candidate _ (uses_mem candidate j))
        (GeneralNominalHeadSchemaNames186.head_not_output candidate _ (uses_mem candidate i))
        (GeneralNominalHeadSchemaNames186.head_not_output candidate _ (uses_mem candidate j))
        model valid first last one two (bounds i first one) (bounds j last two) same

theorem revisit_extension_iff_bounds (checked : Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (historical candidate : Plan roles) (member : historical ∈ state.core.plans)
    (frame : Frame registry state.core focus key candidate)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (model : Assignment) (valid : Models state model) :
    (∃ extended, Models state extended ∧
      (∀ name ∈ support state candidate (uses candidate), extended name = model name) ∧
      HeadEquations candidate extended) ↔ BoundsFit candidate model := by
  rw [GeneralNominalHeadFrameExtension186.frame_extension_iff checked reachable frame model valid]
  exact compatible_iff_bounds checked reachable historical candidate member frame.center_recorded
    identity frame.context_eq declaration model valid

end Yulang.GeneralNominalHeadRevisitExtension186
