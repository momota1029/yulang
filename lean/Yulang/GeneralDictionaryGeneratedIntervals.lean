import Yulang.GeneralDictionaryCapturedChildIntervals
import Yulang.GeneralDictionaryGeneratedOrigins

/-! Interval formation for genuinely generated demands, not just the original
root. A syntactic variable-input fragment restricts journal packets; no endpoint
order, arbitrary frame or dictionary validity is assumed. -/
namespace Yulang.GeneralDictionaryGeneratedIntervals
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState GeneralNominalSupport
open GeneralDictionaryCapturedChildIntervals CommonNominalFullCarrier
variable {roles : Roles.RoleDecls}

/-- Restriction on the actual finite journal, not a restriction on source
language acceptance: compound inputs remain outside this particular theorem. -/
def VariableJournal (state : Tracked roles) : Prop :=
  ∀ packet ∈ state.current.packets, VariableInputs packet

theorem recorded_child (state : Tracked roles) (packet : Packet roles)
    (recorded : packet ∈ state.current.packets) (shape : VariableInputs packet)
    (child : Occurrence roles) (emitted : child ∈ packet.children)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) (index) :
    Subtype (model (child.demand.arguments index).1).1 (model (child.demand.arguments index).2).1 :=
  child_intervals packet shape child emitted model (valid.2.1 packet recorded) index

theorem generated_intervals {registry : Registry} {root child : Occurrence roles} {state : Tracked roles}
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (journal : VariableJournal state) (reached : Generated state.current root child)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) (index) :
    Subtype (model (child.demand.arguments index).1).1 (model (child.demand.arguments index).2).1 := by
  rcases GeneralDictionaryGeneratedOrigins.reachable_generated reachable reached with same | ⟨packet,recorded,emitted⟩
  · subst child
    exact GeneralDictionaryReachableRootIntervals.root_intervals registry root state reachable model valid index
  · exact recorded_child state packet recorded (journal packet recorded) child emitted model valid index

theorem located_intervals {registry : Registry} {root child : Occurrence roles} {state : Tracked roles}
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (journal : VariableJournal state) (reached : Generated state.current root child)
    (bounds : List (GeneralNominalInspection.Bounds state.current.context.state))
    (located : GeneralNominalCandidates.arguments state.current.context child = some bounds)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    ∀ pair ∈ bounds, Subtype
      (model (state.current.context.state.base.source pair.1)).1
      (model (state.current.context.state.base.source pair.2)).1 := by
  intro pair member
  have same := GeneralDictionaryReachableRootIntervals.locate_sources state.current.context.state.base
    (List.ofFn child.demand.arguments) bounds located
  have present : (state.current.context.state.base.source pair.1,state.current.context.state.base.source pair.2) ∈
      List.ofFn child.demand.arguments := by
    rw [←same]
    exact List.mem_map.mpr ⟨pair,member,rfl⟩
  obtain ⟨index,equal⟩ := List.mem_ofFn.mp present
  have result := generated_intervals reachable journal reached model valid index
  simpa only [equal] using result

end Yulang.GeneralDictionaryGeneratedIntervals
