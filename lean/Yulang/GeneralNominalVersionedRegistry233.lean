import Yulang.GeneralNominalVersionedGrowth233
set_option backward.isDefEq.respectTransparency false
/-! Registry provenance and legacy-history emptiness on actual new-kernel paths.
These invariants support later canonical-order and cache-integration work;
they do not supply a terminating executor or the canonical-order bridge. -/
namespace Yulang.GeneralNominalVersionedRegistry233
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 GeneralNominalVersionedKernel232

def Recorded (registry : Registry) (state : State roles) : Prop :=
  (∀ packet ∈ state.core.erased.current.packets, packet.registry = registry) ∧
  (∀ plan ∈ state.plans, plan.packet.registry = registry) ∧
  ∀ effect ∈ state.effects, effect.registry = registry

theorem administrative (action : Administrative before focus after) (recorded : Recorded registry before) :
    Recorded registry after := by
  cases action <;> exact recorded

theorem at_recorded (action : At registry before focus after) (recorded : Recorded registry before) : Recorded registry after := by
  cases action with
  | administrative action => exact administrative action recorded
  | refresh => exact recorded
  | merge => exact recorded
  | install effect enabled novel =>
    have same : effect.plan.packet.registry = registry := effect.frame.registry_eq.trans enabled.registry_eq
    refine ⟨?_,?_,?_⟩
    · intro packet member
      rcases List.mem_cons.mp member with rfl | member
      · exact same
      · exact recorded.1 packet member
    · intro plan member
      rcases List.mem_cons.mp member with rfl | member
      · exact same
      · exact recorded.2.1 plan member
    · intro candidate member
      rcases List.mem_cons.mp member with rfl | member
      · exact enabled.registry_eq
      · exact recorded.2.2 candidate member

theorem step (action : Step registry root before after) (recorded : Recorded registry before) : Recorded registry after :=
  at_recorded action.choose_spec.2 recorded

theorem steps (path : B4Target.Steps (Step registry root) before after) (recorded : Recorded registry before) :
    Recorded registry after := by
  induction path with
  | refl => exact recorded
  | tail path action ih => exact step action ih

theorem initial (registry : Registry) (context : GeneralNominalCandidates.Context) (root : Occurrence roles) :
    Recorded registry (GeneralNominalVersionedJournal232.initial context root) :=
  ⟨(by intro _ member; cases member),(by intro _ member; cases member),(by intro _ member; cases member)⟩

theorem reachable
    (reachable : B4TargetV8.Reachable (GeneralNominalVersionedSourceBoundary232.boundary roles) value root state) :
    Recorded (GeneralNominalCenteredHeadAllocEncoding.registry value) state := by
  obtain ⟨first,⟨legacy,⟨context,labels,source,point,ground,coverage,sameLegacy⟩,same⟩,path⟩ := reachable
  subst first
  subst legacy
  exact steps path (initial _ context root)

theorem distinct_shared_packet_free
    (different : GeneralNominalCenteredHeadAllocEncoding.registry first ≠ GeneralNominalCenteredHeadAllocEncoding.registry last)
    (one : B4TargetV8.Reachable (GeneralNominalVersionedSourceBoundary232.boundary roles) first root state)
    (two : B4TargetV8.Reachable (GeneralNominalVersionedSourceBoundary232.boundary roles) last root state) :
    state.core.erased.current.packets = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro packet member
  exact different (((reachable one).1 packet member).symm.trans ((reachable two).1 packet member))

def LegacyEmpty (state : State roles) : Prop := state.core.plans = [] ∧ state.legacy.effects = []

theorem administrative_empty (action : Administrative before focus after) (empty : LegacyEmpty before) : LegacyEmpty after := by
  cases action <;> exact empty

theorem at_empty (action : At registry before focus after) (empty : LegacyEmpty before) : LegacyEmpty after := by
  cases action with
  | administrative action => exact administrative_empty action empty
  | refresh => exact empty
  | install => exact empty
  | merge => exact empty

theorem steps_empty (path : B4Target.Steps (Step registry root) before after) (empty : LegacyEmpty before) : LegacyEmpty after := by
  induction path with
  | refl => exact empty
  | tail path action ih => exact at_empty action.choose_spec.2 ih

theorem reachable_legacy_empty
    (reachable : B4TargetV8.Reachable (GeneralNominalVersionedSourceBoundary232.boundary roles) value root state) :
    LegacyEmpty state := by
  obtain ⟨first,⟨legacy,⟨context,labels,source,point,ground,coverage,sameLegacy⟩,same⟩,path⟩ := reachable
  subst first
  subst legacy
  exact steps_empty path ⟨rfl,rfl⟩

end Yulang.GeneralNominalVersionedRegistry233
