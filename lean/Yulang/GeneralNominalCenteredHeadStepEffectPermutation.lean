import Yulang.GeneralNominalCenteredHeadStepOrder

set_option backward.isDefEq.respectTransparency false

/-! Historical effects pair independently of the packet table. Their live
meaning is transported whenever the two alias classes retain the same requests.
The model theorem includes the complete recorded and live effect ledger. -/
namespace Yulang.GeneralNominalCenteredHeadStepEffectPermutation
open GeneralDeclarations GeneralSourceDictionaries GeneralRegistryReordering GeneralNominalCenters
open GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredPermutationRepresentation
open GeneralNominalLedgerPermutation (All₂)
variable {roles : Roles.RoleDecls}
variable {relation : GeneralNominalSaturationState.Packet roles → GeneralNominalSaturationState.Packet roles → Prop}

theorem requests_eq
    (same : GeneralNominalJournalPermutation.Related left.erased.current right.erased.current)
    (root : Occurrence roles) : requests left root = requests right root := by
  classical
  unfold requests
  rw [same.sites]
  congr 2
  funext site
  exact decide_eq_decide.mpr (same.alias root.identity site.occurrence.identity)

theorem requests_output (equal : requests left root = requests right root)
    (plan : Plan roles) (model) : OutputEquations left root plan model ↔ OutputEquations right root plan model := by
  simp only [OutputEquations,outputSchema,EqualOutputs,equal]

theorem requests_ready (equal : requests left root = requests right root) (plan : Plan roles) :
    EffectsReady left root plan ↔ EffectsReady right root plan := by
  simp only [EffectsReady,outputSchema,equal]

open GeneralNominalCenteredPermutationPlans (metadata)
variable (plan : Plan roles) (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat)

theorem metadata_head (model) : HeadEquations (metadata plan allocated reserved) model ↔ HeadEquations plan model := by
  have cap : GeneralNominalPacketSupport.capture (metadata plan allocated reserved).packet =
      GeneralNominalPacketSupport.capture plan.packet := GeneralNominalPacketMetadata.capture ..
  simp only [HeadEquations,GeneralNominalCenteredPermutationPlans.head_schema,
    GeneralNominalCenteredPermutationPlans.binder,GeneralNominalCenteredPermutationPlans.schema_holds,cap]
  rfl

theorem metadata_output (state root model) :
    OutputEquations state root (metadata plan allocated reserved) model ↔ OutputEquations state root plan model := by
  have schemas : outputSchema state root (metadata plan allocated reserved) = outputSchema state root plan := rfl
  simp only [OutputEquations,schemas,GeneralNominalCenteredPermutationPlans.schema_holds]

theorem metadata_ready (state root) :
    EffectsReady state root (metadata plan allocated reserved) ↔ EffectsReady state root plan := Iff.rfl

variable {plan allocated reserved}

structure PlanPair (first last : Plan roles) : Prop where
  root : first.packet.site.occurrence = last.packet.site.occurrence
  head : ∀ model, HeadEquations first model ↔ HeadEquations last model
  output : ∀ state root model, OutputEquations state root first model ↔ OutputEquations state root last model
  ready : ∀ state root, EffectsReady state root first ↔ EffectsReady state root last

theorem plan_rebased (order : Reorders plan.packet.registry registry)
    (pair : DeclarationReorders plan.packet.declaration declaration) (allocated reserved) :
    PlanPair plan (GeneralNominalCenteredPermutationCounterparts.rebase plan order pair allocated reserved) := by
  refine ⟨rfl,?_,?_,?_⟩
  · intro model
    exact (GeneralNominalCenteredHeadStepOrder.head_equations order pair model).symm.trans
      (metadata_head _ allocated reserved model).symm
  · intro state root model
    exact (GeneralNominalCenteredHeadStepOrder.output_equations order pair state root model).symm.trans
      (metadata_output _ allocated reserved state root model).symm
  · intro state root
    exact (GeneralNominalCenteredHeadStepOrder.effects_ready order pair state root).symm.trans
      (metadata_ready _ allocated reserved state root).symm

theorem plan_pair (rebased : RebasedPacket first last plan.packet other.packet)
    (input : plan.input = other.input) : PlanPair plan other := by
  obtain ⟨_,declaration,order,pair,allocated,reserved,_,_,packetEq⟩ := rebased
  have equal : other = GeneralNominalCenteredPermutationCounterparts.rebase plan order pair allocated reserved := by
    cases other with
    | mk packet center exactInput =>
      dsimp at packetEq input
      cases packetEq; cases input; rfl
  rw [equal]
  exact plan_rebased order pair allocated reserved

theorem PlanPair.symm (pair : PlanPair first last) : PlanPair last first :=
  ⟨pair.root.symm,fun model => (pair.head model).symm,fun state root model => (pair.output state root model).symm,
    fun state root => (pair.ready state root).symm⟩

structure EffectPair (first last : Effect roles) : Prop where
  plan : PlanPair first.plan last.plan
  snapshot : requests first.snapshot first.plan.packet.site.occurrence = requests last.snapshot last.plan.packet.site.occurrence

theorem EffectPair.holds (pair : EffectPair first last) (model) : first.Holds model ↔ last.Holds model := by
  refine and_congr (pair.plan.head model) ?_
  have moved := pair.plan.output first.snapshot first.plan.packet.site.occurrence model
  have requestsSame : requests first.snapshot last.plan.packet.site.occurrence = requests last.snapshot last.plan.packet.site.occurrence :=
    pair.plan.root ▸ pair.snapshot
  exact moved.trans (pair.plan.root ▸ requests_output requestsSame last.plan model)

theorem EffectPair.live (pair : EffectPair first last)
    (same : ∀ root, requests left root = requests right root) (model) :
    first.Live left model ↔ last.Live right model := by
  unfold Effect.Live
  rw [pair.plan.root]
  exact (pair.plan.output left last.plan.packet.site.occurrence model).trans
    (requests_output (same last.plan.packet.site.occurrence) last.plan model)

theorem EffectPair.ready (pair : EffectPair first last)
    (same : ∀ root, requests left root = requests right root) :
    EffectsReady left first.plan.packet.site.occurrence first.plan ↔
      EffectsReady right last.plan.packet.site.occurrence last.plan := by
  rw [pair.plan.root]
  exact (pair.plan.ready left last.plan.packet.site.occurrence).trans
    (requests_ready (same last.plan.packet.site.occurrence) last.plan)

theorem EffectPair.symm (pair : EffectPair first last) : EffectPair last first :=
  ⟨pair.plan.symm,pair.snapshot.symm⟩

structure Related (relation : GeneralNominalSaturationState.Packet roles → GeneralNominalSaturationState.Packet roles → Prop)
    (left right : State roles) : Prop where
  core : GeneralNominalCenteredLedgerPermutation.Related relation left.core right.core
  effects : All₂ EffectPair left.effects right.effects

theorem Related.models (same : Related relation left right) (model) : Models left model ↔ Models right model := by
  apply and_congr (same.core.models model)
  constructor
  · intro valid effect member
    obtain ⟨old,present,pair⟩ := GeneralNominalLedgerPermutation.all₂_right same.effects member
    exact ⟨(pair.holds model).mp (valid old present).1,
      (pair.live (requests_eq same.core.erased.current) model).mp (valid old present).2⟩
  · intro valid effect member
    obtain ⟨other,present,pair⟩ := GeneralNominalLedgerPermutation.all₂_left same.effects member
    exact ⟨(pair.holds model).mpr (valid other present).1,
      (pair.live (requests_eq same.core.erased.current) model).mpr (valid other present).2⟩

theorem Related.live_ready (same : Related relation left right) : LiveEffectsReady left ↔ LiveEffectsReady right := by
  constructor
  · intro valid effect member
    obtain ⟨old,present,pair⟩ := GeneralNominalLedgerPermutation.all₂_right same.effects member
    exact (pair.ready (requests_eq same.core.erased.current)).mp (valid old present)
  · intro valid effect member
    obtain ⟨other,present,pair⟩ := GeneralNominalLedgerPermutation.all₂_left same.effects member
    exact (pair.ready (requests_eq same.core.erased.current)).mpr (valid other present)

theorem Related.symm (same : Related relation left right) : Related (fun b a => relation a b) right left := by
  refine ⟨GeneralNominalCenteredPermutationSafety.symm same.core,?_⟩
  have reverse : ∀ {xs ys : List (Effect roles)}, All₂ EffectPair xs ys → All₂ EffectPair ys xs := by
    intro xs ys pairs
    induction pairs with
    | nil => exact .nil
    | cons pair rest ih => exact .cons pair.symm ih
  exact reverse same.effects

end Yulang.GeneralNominalCenteredHeadStepEffectPermutation
