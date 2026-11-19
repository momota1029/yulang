import Yulang.GeneralNominalVersionedMixedAncestry237

namespace Yulang.GeneralRebaseRetainedMetadata270
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalCandidates (Context)
open GeneralNominalVersionedMixedAncestry237 (frame configuration_trace)

def Retains (registry : Registry) (origin : Context) (state : State roles) : Prop :=
 ∀ p ∈ state.plans, p.packet.registry = registry ∧ p.packet.declaration ∈ registry.declarations ∧
  p.packet.context.interpretation = origin.interpretation

theorem retained_step (registry : Registry) (root : Occurrence roles) (origin : Context)
 (before after : State roles) (known : Retains registry origin before)
 (current : before.core.erased.current.context.interpretation = origin.interpretation)
 (step : Step registry root before after) : Retains registry origin after := by
 obtain ⟨focus,_,action⟩ := step
 cases action with
 | administrative admin => cases admin <;> exact known
 | refresh => exact known
 | merge => exact known
 | install effect enabled _ =>
   intro p listed
   rcases List.mem_cons.mp listed with rfl | prior
   · have valid := frame enabled
     exact ⟨valid.registry_eq,valid.visible,(congrArg Context.interpretation valid.context_eq).trans current⟩
   · exact known p prior

theorem from_empty (registry : Registry) (root : Occurrence roles) (start target : State roles)
 (empty : start.plans = []) (path : B4Target.Steps (Step registry root) start target) :
 Retains registry start.core.erased.current.context target := by
 induction path with
 | refl =>
   intro p listed
   rw [empty] at listed
   cases listed
 | tail trace step ih =>
   exact retained_step registry root _ _ _ ih (configuration_trace trace).2.2 step

end Yulang.GeneralRebaseRetainedMetadata270
