import Yulang.GeneralNominalCenteredHeadMatPermutationRaw

set_option backward.isDefEq.respectTransparency false

/-! The coherent table pairs plans, including their input centers. Historical
effects carry their alias-class snapshots; current effects use the live class. -/
namespace Yulang.GeneralNominalCenteredHeadMatPermutationLedger
open GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadMatPermutationRaw
open GeneralNominalCenteredHeadMatPermutationPlans (Pair)
open GeneralNominalLedgerPermutation (All₂ all₂_left all₂_right)
variable {roles : Roles.RoleDecls}

def Coupled (relation : Plan roles → Plan roles → Prop) (first last : Plan roles) : Prop :=
  relation first last ∧ Pair first last

structure Coherent (relation : Plan roles → Plan roles → Prop) : Prop where
  left : ∀ {a b c}, relation a b → relation a c → b = c
  right : ∀ {a b c}, relation a c → relation b c → a = b

structure EffectPair (relation : Plan roles → Plan roles → Prop) (first last : Effect roles) : Prop where
  plan : Coupled relation first.plan last.plan
  snapshot : Snapshot first.snapshot last.snapshot

structure Related (relation : Plan roles → Plan roles → Prop) (first last : State roles) : Prop where
  core : Core first.core last.core
  coherent : Coherent relation
  recorded : ∀ a b, relation a b → a ∈ first.core.plans ∧ b ∈ last.core.plans
  plans : All₂ (Coupled relation) first.core.plans last.core.plans
  effects : All₂ (EffectPair relation) first.effects last.effects
  packetsLeft : ∀ plan ∈ first.core.plans, plan.packet ∈ first.core.erased.current.packets
  packetsRight : ∀ plan ∈ last.core.plans, plan.packet ∈ last.core.erased.current.packets

theorem all_models {α β : Type} {relation : α → β → Prop} {xs ys}
    (pairs : All₂ relation xs ys) (first : α → Prop) (last : β → Prop)
    (sound : ∀ a b, relation a b → (first a ↔ last b)) :
    (∀ a ∈ xs, first a) ↔ ∀ b ∈ ys, last b := by
  constructor
  · intro valid b member
    obtain ⟨a,present,pair⟩ := all₂_right pairs member
    exact (sound a b pair).mp (valid a present)
  · intro valid a member
    obtain ⟨b,present,pair⟩ := all₂_left pairs member
    exact (sound a b pair).mpr (valid b present)

theorem all_symm {α β : Type} {relation : α → β → Prop} {other : β → α → Prop} {xs ys}
    (reverse : ∀ a b, relation a b → other b a) (pairs : All₂ relation xs ys) : All₂ other ys xs := by
  induction pairs with
  | nil => exact .nil
  | cons pair rest ih => exact .cons (reverse _ _ pair) ih

theorem all_mono {α β : Type} {relation other : α → β → Prop} {xs ys}
    (forward : ∀ a b, relation a b → other a b) (pairs : All₂ relation xs ys) : All₂ other xs ys := by
  induction pairs with
  | nil => exact .nil
  | cons pair rest ih => exact .cons (forward _ _ pair) ih

variable {relation : Plan roles → Plan roles → Prop} {first last : State roles}

theorem EffectPair.holds (pair : EffectPair relation a b) (model) : a.Holds model ↔ b.Holds model := by
  have root := congrArg GeneralNominalDemandMerging.Site.occurrence pair.plan.2.matched.packet.site
  exact and_congr (pair.plan.2.head model)
    ((pair.plan.2.effects a.snapshot a.plan.packet.site.occurrence model).trans
      (root ▸ pair.snapshot.effects _ b.plan model))

theorem EffectPair.live (pair : EffectPair relation a b) (same : Snapshot left right) (model) :
    a.Live left model ↔ b.Live right model := by
  have root := congrArg GeneralNominalDemandMerging.Site.occurrence pair.plan.2.matched.packet.site
  exact (pair.plan.2.effects left a.plan.packet.site.occurrence model).trans
    (root ▸ same.effects _ b.plan model)

theorem EffectPair.symm (pair : EffectPair relation a b) : EffectPair (fun b a => relation a b) b a :=
  ⟨⟨pair.plan.1,pair.plan.2.symm⟩,pair.snapshot.symm⟩

theorem Related.symm (same : Related relation first last) : Related (fun b a => relation a b) last first :=
  ⟨same.core.symm,⟨same.coherent.right,same.coherent.left⟩,
    fun a b pair => ⟨(same.recorded b a pair).2,(same.recorded b a pair).1⟩,
    all_symm (fun _ _ pair => ⟨pair.1,pair.2.symm⟩) same.plans,
    all_symm (fun _ _ pair => pair.symm) same.effects,same.packetsRight,same.packetsLeft⟩

theorem Related.models (same : Related relation first last) (model) : Models first model ↔ Models last model := by
  have plans := all_models same.plans (fun plan => GeneralNominalCenteredHeadMatStepPackets.Holds plan model)
    (fun plan => GeneralNominalCenteredHeadMatStepPackets.Holds plan model) (fun _ _ pair => pair.2.holds model)
  have effects := all_models same.effects (fun effect => effect.Holds model ∧ effect.Live first.core model)
    (fun effect => effect.Holds model ∧ effect.Live last.core model)
    (fun _ _ pair => and_congr (pair.holds model) (pair.live same.core.snapshot model))
  simp only [Models,GeneralNominalMetadataEquivalence.models same.core.current.context.state,
    same.core.source,same.core.current.sites,same.core.centers,plans,effects]

open GeneralNominalCenteredHeadMatStepSupport (Fact Trusted Readback ClassReadback)

inductive FactPair (relation : Plan roles → Plan roles → Prop) : Fact roles → Fact roles → Prop
  | input : Coupled relation a b → FactPair relation (.input a) (.input b)
  | output : EffectPair relation a b → FactPair relation (.output a) (.output b)
  | merge : FactPair relation (.merge a b) (.merge a b)

theorem fact_models (pair : FactPair relation a b) (model) : a.Holds model ↔ b.Holds model := by
  cases pair with
  | input pair => exact pair.2.inputs model
  | output pair => exact and_congr (pair.plan.2.outputs model) (pair.holds model)
  | merge => exact Iff.rfl

theorem Related.facts_models (same : Related relation first last) (pairs : All₂ (FactPair relation) xs ys) (model) :
    GeneralNominalCenteredHeadMatStepSupport.Models first xs model ↔
      GeneralNominalCenteredHeadMatStepSupport.Models last ys model := by
  have facts := all_models pairs (fun fact => fact.Holds model) (fun fact => fact.Holds model)
    (fun _ _ pair => fact_models pair model)
  simp only [GeneralNominalCenteredHeadMatStepSupport.Models,same.core.source,same.core.roots,facts]

theorem Related.input_member (same : Related relation first last) (pairs : All₂ (FactPair relation) xs ys)
    (pair : Coupled relation a b) (member : Fact.input a ∈ xs) : Fact.input b ∈ ys := by
  obtain ⟨other,present,paired⟩ := all₂_left pairs member
  cases paired with
  | input actual => exact same.coherent.left actual.1 pair.1 ▸ present

theorem Related.readback (same : Related relation first last) (pairs : All₂ (FactPair relation) xs ys)
    (pair : Coupled relation a b) : Readback first xs a ↔ Readback last ys b := by
  have condition (state : State roles) facts (plan : Plan roles) : Readback state facts plan ↔
      ∀ observation, GeneralNominalLedgerPermutation.Reads plan.packet observation → ∀ model,
        GeneralNominalCenteredHeadMatStepSupport.Models state facts model → observation.Holds model :=
    ⟨fun valid observation ⟨slot,member,test,head⟩ => valid slot member test observation head,
      fun valid slot member test observation head => valid observation ⟨slot,member,test,head⟩⟩
  rw [condition,condition]
  simp only [pair.2.matched.packet.reads,same.facts_models pairs]

theorem Related.class_readback (same : Related relation first last) (pairs : All₂ (FactPair relation) xs ys)
    (pair : EffectPair relation a b) : ClassReadback first xs a ↔ ClassReadback last ys b := by
  have models := funext (fun model => propext (same.facts_models pairs model))
  simp only [ClassReadback,pair.snapshot.centers,pair.plan.2.matched.input,pair.snapshot.alias,models]

theorem Related.packet_settled (same : Related relation first last) (pair : Coupled relation a b) :
    GeneralNominalSettledSupport.PacketSettled first.core.erased.current a.packet ↔
      GeneralNominalSettledSupport.PacketSettled last.core.erased.current b.packet :=
  same.core.current.packet_settled pair.2.matched.packet.toPacketPair
    ⟨fun _ => same.packetsRight b (same.recorded a b pair.1).2,
      fun _ => same.packetsLeft a (same.recorded a b pair.1).1⟩

theorem Related.trusted (same : Related relation first last) (trusted : Trusted first facts) :
    ∃ other, All₂ (FactPair relation) facts other ∧ Trusted last other := by
  induction trusted with
  | source => exact ⟨[],.nil,.source⟩
  | input plan _ recorded readback ih =>
      obtain ⟨facts,pairs,trusted⟩ := ih
      obtain ⟨other,present,pair⟩ := all₂_left same.plans recorded
      exact ⟨_,.cons (.input pair) pairs,.input other trusted present ((same.readback pairs pair).mp readback)⟩
  | output effect _ recorded _ included classReadback settled ih =>
      obtain ⟨facts,pairs,trusted⟩ := ih
      obtain ⟨other,present,pair⟩ := all₂_left same.effects recorded
      exact ⟨_,.cons (.output pair) pairs,.output other trusted present
        (same.recorded _ _ pair.plan.1).2 (same.input_member pairs pair.plan included)
        ((same.class_readback pairs pair).mp classReadback) ((same.packet_settled pair.plan).mp settled)⟩
  | merge a b _ one two alias atoms holds inputs ih =>
      obtain ⟨facts,pairs,trusted⟩ := ih
      have models := funext (fun model => propext (same.facts_models pairs model))
      refine ⟨_,.cons .merge pairs,.merge a b trusted ((same.core.centers _).mp one)
        ((same.core.centers _).mp two) ((same.core.snapshot.alias _ _).mp alias) ?_ ?_ (models ▸ inputs)⟩
      · intro atom member
        have ordinary : first.core.erased.current.context.state.ordinary = last.core.erased.current.context.state.ordinary := by
          obtain ⟨_,_,equal,_,_⟩ := same.core.current.context.state
          rw [equal]; rfl
        exact ordinary ▸ atoms atom member
      · exact fun model valid => holds model ((same.facts_models pairs model).mpr valid)

theorem Related.justifies (same : Related relation first last) (claim) :
    GeneralNominalCenteredHeadMatStepObservations.Justifies first claim ↔
      GeneralNominalCenteredHeadMatStepObservations.Justifies last claim := by
  have forward {relation} {a b : State roles} (same : Related relation a b)
      (valid : GeneralNominalCenteredHeadMatStepObservations.Justifies a claim) :
      GeneralNominalCenteredHeadMatStepObservations.Justifies b claim := by
    obtain ⟨facts,trusted,sound⟩ := valid
    obtain ⟨other,pairs,trusted⟩ := same.trusted trusted
    exact ⟨other,trusted,fun model valid => sound model ((same.facts_models pairs model).mpr valid)⟩
  exact ⟨forward same,forward same.symm⟩

theorem Related.cache (same : Related relation first last) (snapshot) :
    GeneralNominalCenteredHeadMatStepObservations.CacheSound first snapshot ↔
      GeneralNominalCenteredHeadMatStepObservations.CacheSound last snapshot := by
  simp only [GeneralNominalCenteredHeadMatStepObservations.CacheSound,same.justifies]

end Yulang.GeneralNominalCenteredHeadMatPermutationLedger
