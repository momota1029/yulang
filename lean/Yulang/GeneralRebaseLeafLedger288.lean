import Yulang.GeneralRebaseLeafOutput288
import Yulang.GeneralNominalVersionedSupportGrowth233

/-! Static extension of the plan ledger only. No executable transition or
operational source-reachability conclusion follows from these laws. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseLeafLedger288
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedSupport233
open GeneralNominalVersionedGrowth233 (Monotone)
open GeneralRebaseInertLeaf288 (Leaf)
open GeneralRebaseLeafOutput288 (Extension)
variable {roles : Roles.RoleDecls}

def record (state : State roles) (leafPlan : Plan roles) : State roles :=
  { state with plans := leafPlan :: state.plans }

theorem growth (state : State roles) (leafPlan : Plan roles) : Monotone state (record state leafPlan) :=
  ⟨(GeneralNominalVersionedGrowth233.refl state).legacy,fun _ old => List.mem_cons_of_mem _ old,
    (fun _ h => h),(fun _ h => h),rfl,rfl,rfl⟩

theorem core_eq (state : State roles) (leafPlan : Plan roles) : (record state leafPlan).core = state.core := rfl

theorem effects_eq (state : State roles) (leafPlan : Plan roles) : (record state leafPlan).effects = state.effects := rfl

variable {registry : Registry} {state : State roles} {root : Occurrence roles} {key : Nat} {leafPlan : Plan roles}

theorem record_models (leaf : Leaf registry state root key leafPlan) (m : Assignment) :
    Models (record state leafPlan) m ↔ Models state m := by
  constructor
  · intro valid
    exact ⟨valid.1,(fun plan present => valid.2.1 plan (List.mem_cons_of_mem _ present)),valid.2.2⟩
  · intro valid
    refine ⟨valid.1,?_,valid.2.2⟩
    intro plan present
    rcases List.mem_cons.mp present with rfl | present
    · exact leaf.sourcePacket m (trusted_models .source valid)
    · exact valid.2.1 plan present

theorem recorded_child (leaf : Leaf registry state root key leafPlan) :
    Discharged (record state leafPlan) root := by
  rw [← leaf.frame.occurrence_eq]
  refine .packet leafPlan List.mem_cons_self ?_
  intro child member
  rw [leaf.noChildren] at member
  cases member

theorem singleton_settlement (leaf : Leaf registry state root key leafPlan)
    {parent : Plan roles} (parentIn : parent ∈ state.plans)
    (sole : GeneralNominalVersionedFrame231.children parent.packet = [root]) :
    PacketSettled (record state leafPlan) parent := by
  refine ⟨(growth state leafPlan).plans parentIn,?_⟩
  intro child member
  rw [sole] at member
  cases List.mem_singleton.mp member
  exact recorded_child leaf

theorem old_trust_in_static_ledger {effect : Effect roles} {prior : List (Fact roles)}
    (extension : Extension state prior effect)
    (leaf : Leaf effect.registry state root key leafPlan)
    (sole : GeneralNominalVersionedFrame231.children effect.plan.packet = [root]) :
    Trusted (record state leafPlan) (.output effect :: prior) := by
  have lift := growth state leafPlan
  have settled := singleton_settlement leaf extension.settled.1 sole
  exact .output effect (GeneralNominalVersionedSupportGrowth233.trusted lift extension.trusted)
    (lift.effects extension.effectRecorded) settled.1 extension.inputRecorded
    (GeneralNominalVersionedSupportGrowth233.class_readback lift extension.classReadback) settled

end Yulang.GeneralRebaseLeafLedger288
