import Yulang.GeneralVersionedTraceDomain313
import Yulang.GeneralVersionedSiteOrigins312

set_option backward.isDefEq.respectTransparency false
/-! Stored frames read genuine earlier raw domains. Those domains persist
under every real mixed step, including arbitrary checked cache refinement. -/
namespace Yulang.GeneralVersionedHistoricalDomain313
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalState (sources)
open GeneralVersionedTraceDomain313 (raw)

theorem extend_mono (state : GeneralNominalState.State) (reserved) (atoms) :
    sources state ⊆ sources (GeneralNominalState.extend state reserved atoms) := by
  intro n h
  simp only [sources,GeneralNominalState.extend,List.mem_append,List.flatMap_append] at h ⊢
  rcases h with ((source|row)|old)|atom
  · exact .inl (.inl (.inl source))
  · exact .inl (.inl (.inr row))
  · exact .inl (.inr (.inl old))
  · exact .inr (.inl atom)

theorem growth {before after : State roles}
    (action : Step registry root before after) : raw before ⊆ raw after := by
  obtain ⟨focus,generated,action⟩ := action
  cases action with
  | administrative action =>
    cases action with
    | enqueue => exact fun _ h => h
    | refresh ctx cert _ _ _ _ => exact GeneralNominalRefinements.sources cert.refines
    | equate => exact extend_mono _ _ _
    | reobserve => exact fun _ h => h
  | refresh focus ctx cert _ _ _ _ => exact GeneralNominalRefinements.sources cert.refines
  | merge => exact extend_mono _ _ _
  | install effect enabled _ =>
    have same := (GeneralNominalVersionedMixedAncestry237.frame enabled).context_eq
    intro n h
    change n ∈ sources _ at h ⊢
    have included := extend_mono effect.plan.packet.context.state
      (GeneralNominalVersionedInstallation231.reserved effect.plan.packet)
      (GeneralNominalVersionedInstallation231.atoms effect.plan.packet)
    exact included (same.symm ▸ h)

def IncludesHistory (s : State roles) : Prop :=
  ∀ p ∈ s.plans, sources p.packet.context.state ⊆ raw s

theorem next {before after : State roles} (action : Step registry root before after)
    (history : IncludesHistory before) : IncludesHistory after := by
  have growing := growth action
  obtain ⟨focus,generated,action⟩ := action
  have keep (p : Plan roles) (old : p ∈ before.plans) : sources p.packet.context.state ⊆ raw after :=
    fun _ inEarlier => growing (history p old inEarlier)
  unfold IncludesHistory
  cases action with
  | administrative action =>
    cases action <;> exact keep
  | refresh | merge => exact keep
  | install effect enabled _ =>
    intro p member
    rcases List.mem_cons.mp member with new | old
    · subst p
      have context := (GeneralNominalVersionedMixedAncestry237.frame enabled).context_eq
      intro n h
      apply growing
      change n ∈ sources before.core.erased.current.context.state
      rw [context] at h
      exact h
    · exact keep p old

theorem reached {s : State roles} (actual : Reachable registry root s) : IncludesHistory s := by
  obtain ⟨start,⟨legacy,_,rfl⟩,steps⟩ := actual
  induction steps with
  | refl => intro p h; cases h
  | tail _ action ih => exact next action ih

end Yulang.GeneralVersionedHistoricalDomain313
