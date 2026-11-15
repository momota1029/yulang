import Yulang.GeneralNominalCenteredHeadAllocV7Boundary
import Yulang.GeneralNominalCenteredHeadMatStepTrace

namespace Yulang.GeneralDictionaryAllocRecordedChildren202
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadMatStepKernel
variable {roles : Roles.RoleDecls} {before after state : State roles}

/-- Pure execution bookkeeping, independent of satisfiability. -/
def RecordedEdges (state : State roles) : Prop :=
  ∀ plan ∈ state.core.plans, ∀ child ∈ plan.packet.children,
    (plan.packet.site.occurrence,child) ∈ state.core.erased.current.edges

theorem edges_grow (action : At registry before focus after) :
    before.core.erased.current.edges ⊆ after.core.erased.current.edges := by
  cases action with
  | administrative action => cases action <;> exact fun _ h => h
  | refresh | merge => exact fun _ h => h
  | install => exact fun _ h => List.mem_append_left _ h

theorem at_recorded (recorded : RecordedEdges before) (action : At registry before focus after) :
    RecordedEdges after := by
  have growth := edges_grow action
  cases action with
  | administrative action =>
      cases action <;> exact fun plan present child member => growth (recorded plan present child member)
  | refresh | merge => exact fun plan present child member => growth (recorded plan present child member)
  | install effect enabled novel =>
      intro plan present child member
      rcases List.mem_cons.mp present with rfl | present
      · exact installed_child member
      · exact growth (recorded plan present child member)

theorem trace_recorded (path : B4Target.Steps (Step registry root) (initial context root) state) :
    RecordedEdges state := by
  induction path with
  | refl => exact fun _ impossible => False.elim (List.not_mem_nil impossible)
  | tail _ step ih => exact at_recorded ih step.choose_spec.2

theorem reachable_recorded
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadAllocBoundary.boundary roles) value root state) :
    RecordedEdges state := by
  obtain ⟨first,⟨context,labels,source,point,ground,coverage,rfl⟩,path⟩ := reachable
  exact trace_recorded path

theorem recorded_committed
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadAllocBoundary.boundary roles) value root state)
    (recorded : plan ∈ state.core.plans) : Committed state plan :=
  ⟨fun _ model => model.2.2.2.2.1 plan recorded,reachable_recorded reachable plan recorded⟩

theorem recorded_generated
    (reachable : B4TargetV6.Reachable (GeneralNominalCenteredHeadAllocBoundary.boundary roles) value root state)
    (recorded : plan ∈ state.core.plans)
    (reached : plan.packet.site.occurrence = root ∨
      GeneralNominalSaturationState.Generated state.core.erased.current root plan.packet.site.occurrence)
    (member : child ∈ plan.packet.children) :
    GeneralNominalSaturationState.Generated state.core.erased.current root child := by
  have parent : GeneralNominalSaturationState.Generated state.core.erased.current root plan.packet.site.occurrence :=
    reached.elim (fun same => same.symm ▸ GeneralNominalSaturationState.Generated.root) id
  exact .child parent ((recorded_committed reachable recorded).2 child member)

/-- V7 retains the same actual trace; no conflict or model premise is needed. -/
theorem v7_recorded_generated
    (reachable : B4TargetV7.Reachable (GeneralNominalCenteredHeadAllocV7Boundary.boundary roles) value root state)
    (recorded : plan ∈ state.core.plans)
    (reached : plan.packet.site.occurrence = root ∨
      GeneralNominalSaturationState.Generated state.core.erased.current root plan.packet.site.occurrence)
    (member : child ∈ plan.packet.children) :
    GeneralNominalSaturationState.Generated state.core.erased.current root child :=
  recorded_generated reachable recorded reached member

end Yulang.GeneralDictionaryAllocRecordedChildren202
