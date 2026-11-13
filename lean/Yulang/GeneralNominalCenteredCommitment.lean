import Yulang.GeneralNominalCenteredAdministrativeComposition

/-! Fixed-packet commitment and its actual child edges persist through every
centered action. A recorded packet is committed on every reachable snapshot. -/
namespace Yulang.GeneralNominalCenteredCommitment
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalSaturationState (Packet Generated)

variable {roles : Roles.RoleDecls}
variable {state : State roles} {packet : Packet roles}

theorem committed_at (action : At registry before focus after)
    (committed : GeneralNominalFeedbackSteps.Committed before.erased.current packet) :
    GeneralNominalFeedbackSteps.Committed after.erased.current packet := by
  have growth := (GeneralNominalCenteredTrace.at_extends action).journal
  exact ⟨fun model valid => committed.1 model (growth.models model valid),
    fun child member => growth.edges _ (committed.2 child member)⟩

theorem committed_steps (path : B4Target.Steps (Step registry root) before after)
    (committed : GeneralNominalFeedbackSteps.Committed before.erased.current packet) :
    GeneralNominalFeedbackSteps.Committed after.erased.current packet := by
  induction path with
  | refl => exact committed
  | tail path step ih => exact committed_at step.choose_spec.2 ih

theorem installed_committed (state : State roles) (plan : Plan roles) (support : List (Occurrence roles)) :
    GeneralNominalFeedbackSteps.Committed (install state plan support).erased.current plan.packet := by
  refine ⟨fun model valid => valid.2.1 _ (List.mem_cons_self ..),?_⟩
  intro child member
  exact List.mem_append_right _ (List.mem_map.mpr ⟨child,member,rfl⟩)

def RecordedCommitted (state : State roles) : Prop :=
  ∀ packet ∈ state.erased.current.packets, GeneralNominalFeedbackSteps.Committed state.erased.current packet

theorem recorded_at (recorded : RecordedCommitted before) (action : At registry before focus after) :
    RecordedCommitted after := by
  intro packet member
  cases action with
  | administrative focus after action =>
    have old : packet ∈ before.erased.current.packets := by cases action <;> exact member
    exact committed_at (.administrative focus after action) (recorded packet old)
  | refresh focus context certificate source memberSource unknown known =>
    exact committed_at (registry := registry) (.refresh focus context certificate source memberSource unknown known) (recorded packet member)
  | merge first last support one two inputs novel guard =>
    exact committed_at (registry := registry) (.merge first last support one two inputs novel guard) (recorded packet member)
  | install plan support enabled novel guard =>
    rcases List.mem_cons.mp member with rfl | member
    · exact installed_committed before plan support
    · exact committed_at (.install plan support enabled novel guard) (recorded packet member)

theorem recorded_trace (path : B4Target.Steps (Step registry root) (initial context root) state) :
    RecordedCommitted state := by
  induction path with
  | refl => intro packet member; cases member
  | tail path step ih => exact recorded_at ih step.choose_spec.2

theorem recorded_reachable
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredAdministrativeLocal.boundary roles) registry root state) :
    RecordedCommitted state := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  exact recorded_trace path

theorem committed_children
    (generated : Generated state.erased.current root packet.site.occurrence)
    (committed : GeneralNominalFeedbackSteps.Committed state.erased.current packet) :
    ∀ child ∈ packet.children, Generated state.erased.current root child :=
  fun child member => .child generated (committed.2 child member)

theorem recorded_children
    (reachable : B4TargetV5.Reachable (GeneralNominalCenteredAdministrativeLocal.boundary roles) registry root state)
    (recorded : packet ∈ state.erased.current.packets)
    (generated : Generated state.erased.current root packet.site.occurrence) :
    ∀ child ∈ packet.children, Generated state.erased.current root child :=
  committed_children generated (recorded_reachable reachable packet recorded)

theorem halted_installable_committed
    (halted : ∀ next, ¬ Step registry root state next)
    (generated : Generated state.erased.current root plan.packet.site.occurrence)
    (enabled : GeneralNominalCenteredBoundary.Installable registry state plan) :
    GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet := by
  apply Classical.byContradiction
  intro novel
  obtain ⟨base,support,guard⟩ := enabled
  exact halted _ ⟨_,generated,.install plan support base novel guard⟩

end Yulang.GeneralNominalCenteredCommitment
