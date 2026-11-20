import Yulang.GeneralRebaseInertLeaf288

/-! One new output fact over an original, unchanged trusted prefix.
This is a proof-only interface, not a new recursive trust closure. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseLeafOutput288
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedSupport233
open GeneralRebaseInertLeaf288 (Leaf SourceSlice)
variable {roles : Roles.RoleDecls}

def Child (registry : Registry) (state : State roles) (occurrence : Occurrence roles) : Prop :=
  Discharged state occurrence ∨ ∃ key plan, Leaf registry state occurrence key plan

def Parent (registry : Registry) (state : State roles) (plan : Plan roles) : Prop :=
  plan ∈ state.plans ∧ ∀ child ∈ GeneralNominalVersionedFrame231.children plan.packet,
    Child registry state child

theorem old_settlement {registry : Registry} {state : State roles} {plan : Plan roles}
    (old : PacketSettled state plan) : Parent registry state plan :=
  ⟨old.1,fun child member => .inl (old.2 child member)⟩

structure Extension (state : State roles) (prior : List (Fact roles)) (effect : Effect roles) : Prop where
  trusted : Trusted state prior
  effectRecorded : effect ∈ state.effects
  inputRecorded : Fact.input effect.plan ∈ prior
  classReadback : ClassReadback state prior effect
  settled : Parent effect.registry state effect.plan

variable {state : State roles} {prior : List (Fact roles)} {effect : Effect roles} {model : Assignment}

theorem old_output (trusted : Trusted state prior) (recorded : effect ∈ state.effects)
    (input : Fact.input effect.plan ∈ prior) (readback : ClassReadback state prior effect)
    (settled : PacketSettled state effect.plan) : Extension state prior effect :=
  ⟨trusted,recorded,input,readback,old_settlement settled⟩

theorem output_iff :
    SliceModels state (.output effect :: prior) model ↔
      SliceModels state prior model ∧ (Fact.output effect).Holds model := by
  constructor
  · intro h
    exact ⟨⟨h.1,h.2.1,fun fact seen => h.2.2 fact (List.mem_cons_of_mem _ seen)⟩,
      h.2.2 _ List.mem_cons_self⟩
  · rintro ⟨base,output⟩
    refine ⟨base.1,base.2.1,?_⟩
    intro fact seen
    rcases List.mem_cons.mp seen with rfl | seen
    · exact output
    · exact base.2.2 fact seen

theorem output_models (extension : Extension state prior effect) (valid : Models state model) :
    SliceModels state (.output effect :: prior) model :=
  output_iff.mpr ⟨trusted_models extension.trusted valid,
    (valid.2.1 effect.plan extension.settled.1).2.2,
    (valid.2.2 effect extension.effectRecorded).1⟩

theorem new_child_has_source_evidence {registry : Registry} {occurrence : Occurrence roles}
    (child : Child registry state occurrence) (notRecorded : ¬ Discharged state occurrence)
    (model : Assignment) (source : SourceSlice state model) :
    ∃ key, GeneralNominalVersionedEvidence231.Evidence registry state.core model occurrence (.node key []) := by
  rcases child with h | ⟨key,plan,cert⟩
  · exact (notRecorded h).elim
  · exact ⟨key,GeneralRebaseInertLeaf288.source_evidence cert model source⟩

end Yulang.GeneralRebaseLeafOutput288
