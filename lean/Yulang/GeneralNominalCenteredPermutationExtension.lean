import Yulang.GeneralNominalCenteredPermutationEmission

set_option backward.isDefEq.respectTransparency false

/-! A new packet pair extends the common table. Recorded commitment excludes
collisions with historical entries; all support alternatives are retained. -/
namespace Yulang.GeneralNominalCenteredPermutationExtension
open GeneralDeclarations GeneralSourceDictionaries GeneralRegistryReordering GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredPermutationRepresentation
open GeneralNominalCenteredPermutationCounterparts
open GeneralNominalLedgerPermutation (All₂ Coherent)
variable {roles : Roles.RoleDecls}

private theorem all₂_mono {α β : Type} {p q : α → β → Prop} (imp : ∀ a b, p a b → q a b)
    {xs ys} (pairs : All₂ p xs ys) : All₂ q xs ys := by
  induction pairs with
  | nil => exact .nil
  | cons pair rest ih => exact .cons (imp _ _ pair) ih

private theorem all₂_append {α β : Type} {p : α → β → Prop} {a b c d}
    (one : All₂ p a b) (two : All₂ p c d) : All₂ p (a ++ c) (b ++ d) := by
  induction one with
  | nil => exact two
  | cons pair rest ih => exact .cons pair ih

private theorem fact_mono {p q : GeneralNominalSaturationState.Packet roles → GeneralNominalSaturationState.Packet roles → Prop}
    (imp : ∀ a b, p a b → q a b) {a b} (pair : GeneralNominalLedgerPermutation.FactPair p a b) :
    GeneralNominalLedgerPermutation.FactPair q a b := by
  cases pair with
  | inputs pair => exact .inputs (imp _ _ pair)
  | outputs pair => exact .outputs (imp _ _ pair)
  | merge => exact .merge

private theorem plan_mono {p q : GeneralNominalSaturationState.Packet roles → GeneralNominalSaturationState.Packet roles → Prop}
    (imp : ∀ a b, p a b → q a b) {a b} (pair : GeneralNominalCenteredLedgerPermutation.PlanPair p a b) :
    GeneralNominalCenteredLedgerPermutation.PlanPair q a b :=
  ⟨imp _ _ pair.packet,pair.input,pair.inputs,pair.outputs,pair.equations,pair.tests⟩

variable {table : List (GeneralNominalSaturationState.Packet roles × GeneralNominalSaturationState.Packet roles)}
variable {left right : State roles} {first last : Registry} {plan other : Plan roles}

theorem table_coherent (same : GeneralNominalCenteredLedgerPermutation.Related (paired table) left right)
    (recorded : ∀ a b, paired table a b → a ∈ left.erased.current.packets ∧ b ∈ right.erased.current.packets)
    (oneNew : plan.packet ∉ left.erased.current.packets) (twoNew : other.packet ∉ right.erased.current.packets)
    (matchPlan : Match plan other) : Coherent (paired ((plan.packet,other.packet) :: table)) := by
  have entry {a b} : paired ((plan.packet,other.packet) :: table) a b ↔
      (a = plan.packet ∧ b = other.packet) ∨ paired table a b := by
    simp only [paired,List.mem_cons,Prod.mk.injEq]
  refine ⟨?_,?_,?_⟩
  · intro a b c one two
    rcases entry.mp one with ⟨rfl,rfl⟩ | one
    · rcases entry.mp two with ⟨_,rfl⟩ | two
      · rfl
      · exact False.elim (oneNew (recorded _ _ two).1)
    · rcases entry.mp two with ⟨rfl,rfl⟩ | two
      · exact False.elim (oneNew (recorded _ _ one).1)
      · exact same.erased.coherent.left one two
  · intro a b c one two
    rcases entry.mp one with ⟨rfl,rfl⟩ | one
    · rcases entry.mp two with ⟨rfl,_⟩ | two
      · rfl
      · exact False.elim (twoNew (recorded _ _ two).2)
    · rcases entry.mp two with ⟨rfl,rfl⟩ | two
      · exact False.elim (twoNew (recorded _ _ one).2)
      · exact same.erased.coherent.right one two
  · intro a b member
    rcases entry.mp member with ⟨rfl,rfl⟩ | member
    · exact matchPlan.packet
    · exact same.erased.coherent.sound member

theorem rebased_emitted (rebased : RebasedPacket first last plan.packet other.packet)
    (inputEq : plan.input = other.input) (site : Site roles) : site ∈ plan.emitted ↔ site ∈ other.emitted := by
  obtain ⟨registry,decl,order,pair,allocated,reserved,_,_,packetEq⟩ := rebased
  have equal : other = GeneralNominalCenteredPermutationCounterparts.rebase plan order pair allocated reserved := by
    cases other with | mk packet input exactInput =>
      dsimp at packetEq inputEq
      cases packetEq
      cases inputEq
      rfl
  rw [equal]
  change _ ↔ site ∈ (GeneralNominalCenteredPermutationPlans.metadata _ _ _).emitted
  rw [GeneralNominalCenteredPermutationPlans.emitted]
  exact (GeneralNominalCenteredPlanReordering.emitted_mem order pair site).symm

theorem support_alternatives (same : GeneralNominalCenteredLedgerPermutation.Related (paired table) left right)
    (order : Reorders first last) (matchPlan : Match plan other)
    (one : GeneralNominalFeedbackSteps.Installable first left.erased.current plan.packet)
    (two : GeneralNominalFeedbackSteps.Installable last right.erased.current other.packet) :
    GeneralNominalSupportChoices.alternatives left.erased plan.packet = GeneralNominalSupportChoices.alternatives right.erased other.packet := by
  classical
  obtain ⟨⟨r₁,c₁,_,v₁,h₁,b₁,_⟩,_⟩ := one
  obtain ⟨⟨r₂,c₂,_,v₂,h₂,b₂,_⟩,_⟩ := two
  have packetOrder : Reorders plan.packet.registry other.packet.registry := by simpa only [r₁,r₂] using order
  unfold GeneralNominalSupportChoices.alternatives
  rw [same.erased.pool]
  apply congrArg (List.filter · _)
  funext support
  exact decide_eq_decide.mpr (GeneralNominalCenteredPermutationGuards.choices same.erased packetOrder matchPlan c₁ c₂
    (r₁ ▸ v₁) (r₂ ▸ v₂) h₁ h₂ b₁ b₂ support)

theorem installed_related (same : GeneralNominalCenteredLedgerPermutation.Related (paired table) left right)
    (recorded : ∀ a b, paired table a b → a ∈ left.erased.current.packets ∧ b ∈ right.erased.current.packets)
    (order : Reorders first last) (roleEq : first.roles = roles) (matchPlan : Match plan other)
    (rebased : RebasedPacket first last plan.packet other.packet)
    (oneNew : plan.packet ∉ left.erased.current.packets) (twoNew : other.packet ∉ right.erased.current.packets)
    (one : GeneralNominalFeedbackSteps.Installable first left.erased.current plan.packet)
    (two : GeneralNominalFeedbackSteps.Installable last right.erased.current other.packet) (support) :
    GeneralNominalCenteredLedgerPermutation.Related (paired ((plan.packet,other.packet) :: table))
      (install left plan support) (install right other support) := by
  let extended := (plan.packet,other.packet) :: table
  have oldPair : ∀ a b, paired table a b → paired extended a b := fun _ _ member => List.mem_cons_of_mem _ member
  have newPair : paired extended plan.packet other.packet := List.mem_cons_self ..
  have planPair : GeneralNominalCenteredLedgerPermutation.PlanPair (paired extended) plan other :=
    ⟨newPair,matchPlan.input,matchPlan.plans.inputs,matchPlan.plans.outputs,matchPlan.plans.equations,matchPlan.plans.tests⟩
  have current : GeneralNominalJournalPermutation.Related (install left plan support).erased.current
      (install right other support).erased.current := by
    refine ⟨GeneralNominalCenteredPermutationEmission.rebased_private plan.packet rebased,
      .cons matchPlan.packet.toPacketPair same.erased.current.packets,?_,?_,same.erased.current.aliases⟩
    · change left.erased.current.sites ++ _ = right.erased.current.sites ++ _
      rw [same.erased.current.sites,GeneralNominalCenteredPermutationEmission.rebased_emitted plan.packet rebased roleEq]
    · change left.erased.current.edges ++ plan.packet.children.map _ = right.erased.current.edges ++ other.packet.children.map _
      rw [same.erased.current.edges,matchPlan.packet.children,matchPlan.packet.site]
  refine ⟨⟨table_coherent same recorded oneNew twoNew matchPlan,same.erased.source,current,?_,?_⟩,?_,
    .cons planPair (all₂_mono oldPairPlan same.plans),same.roots⟩
  · intro a b member
    rcases List.mem_cons.mp member with eq | member
    · have one := congrArg Prod.fst eq
      have two := congrArg Prod.snd eq
      dsimp at one two
      cases one; cases two
      exact ⟨fun _ => List.mem_cons_self ..,fun _ => List.mem_cons_self ..⟩
    · exact ⟨fun _ => List.mem_cons_of_mem _ (recorded a b member).2,
        fun _ => List.mem_cons_of_mem _ (recorded a b member).1⟩
  · change All₂ _ (GeneralNominalSupportChoices.installedFacts left.erased plan.packet ++ left.erased.facts)
      (GeneralNominalSupportChoices.installedFacts right.erased other.packet ++ right.erased.facts)
    apply all₂_append _ (all₂_mono (fun _ _ pair => fact_mono oldPair pair) same.erased.facts)
    unfold GeneralNominalSupportChoices.installedFacts
    rw [support_alternatives same order matchPlan one two]
    generalize GeneralNominalSupportChoices.alternatives right.erased other.packet = alternatives
    induction alternatives with
    | nil => exact .nil
    | cons support rest ih => exact .cons (.inputs newPair) (.cons (.outputs newPair) ih)
  · intro site
    change site ∈ left.sites ++ plan.emitted ↔ site ∈ right.sites ++ other.emitted
    simp only [List.mem_append,same.sites,rebased_emitted rebased matchPlan.input]
where
  oldPairPlan a b (pair : GeneralNominalCenteredLedgerPermutation.PlanPair (paired table) a b) :
      GeneralNominalCenteredLedgerPermutation.PlanPair (paired ((plan.packet,other.packet) :: table)) a b :=
    plan_mono (fun _ _ member => List.mem_cons_of_mem _ member) pair

theorem installed_corresponds (same : Corresponds first last left right)
    (order : Reorders first last) (roleEq : first.roles = roles) (matchPlan : Match plan other)
    (rebased : RebasedPacket first last plan.packet other.packet)
    (oneNew : plan.packet ∉ left.erased.current.packets) (twoNew : other.packet ∉ right.erased.current.packets)
    (one : GeneralNominalFeedbackSteps.Installable first left.erased.current plan.packet)
    (two : GeneralNominalFeedbackSteps.Installable last right.erased.current other.packet) (support) :
    Corresponds first last (install left plan support) (install right other support) := by
  obtain ⟨table,rebases,recorded,pairs⟩ := same
  refine ⟨(plan.packet,other.packet) :: table,?_,?_,installed_related pairs recorded order roleEq matchPlan rebased oneNew twoNew one two support⟩
  · intro a b member
    rcases List.mem_cons.mp member with eq | member
    · have fst := congrArg Prod.fst eq
      have snd := congrArg Prod.snd eq
      dsimp at fst snd
      cases fst; cases snd
      exact rebased
    · exact rebases a b member
  · intro a b member
    rcases List.mem_cons.mp member with eq | member
    · have fst := congrArg Prod.fst eq
      have snd := congrArg Prod.snd eq
      dsimp at fst snd
      cases fst; cases snd
      exact ⟨List.mem_cons_self ..,List.mem_cons_self ..⟩
    · exact ⟨List.mem_cons_of_mem _ (recorded a b member).1,List.mem_cons_of_mem _ (recorded a b member).2⟩

end Yulang.GeneralNominalCenteredPermutationExtension
