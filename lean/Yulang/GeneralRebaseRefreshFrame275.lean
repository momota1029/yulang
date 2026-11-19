import Yulang.GeneralRebaseRetargetEffects275

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25000
set_option maxHeartbeats 7700000
namespace Yulang.GeneralRebaseRefreshFrame275
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryOptionalInitial229 (registry declaration)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalRefinements (Refines)
open GeneralNominalVersionedCandidates231 (inputs)
open GeneralNominalRecursiveCandidates (arguments)
open GeneralRebaseRetarget275 (retarget)
open GeneralRebaseRefreshClosure275 (Gates)

structure LocatedFrame (state : State roles) (plan : Plan roles) : Prop where
 registry_eq : plan.packet.registry = registry
 context_eq : plan.packet.context = state.core.erased.current.context
 declaration_eq : plan.packet.declaration = declaration
 raw_recorded : plan.packet.site ∈ state.core.erased.current.sites
 center_recorded : plan.input ∈ state.core.sites
 located : arguments plan.packet.context (inputs root) = some plan.packet.bounds

theorem of_frame {state : State roles} {plan : Plan roles} {key : Nat}
 (frame : Frame registry state.core root key plan) : LocatedFrame state plan :=
 ⟨frame.registry_eq,frame.context_eq,List.mem_singleton.mp frame.visible,
   frame.raw_recorded,frame.center_recorded,frame.located⟩

theorem same_plan {state : State roles} (gate : Gates state)
 {first last : Plan roles} (a : LocatedFrame state first) (b : LocatedFrame state last) : first = last := by
 rcases first with ⟨⟨reg₁,ctx₁,site₁,d₁,checked₁,bounds₁⟩,center₁,p₁⟩
 rcases last with ⟨⟨reg₂,ctx₂,site₂,d₂,checked₂,bounds₂⟩,center₂,p₂⟩
 have sameRegistry : reg₁ = reg₂ := a.registry_eq.trans b.registry_eq.symm
 have sameCtx : ctx₁ = ctx₂ := a.context_eq.trans b.context_eq.symm
 have sameDecl : d₁ = d₂ := a.declaration_eq.trans b.declaration_eq.symm
 have raw₁ := List.mem_singleton.mp (gate.sites ▸ a.raw_recorded)
 have raw₂ := List.mem_singleton.mp (gate.sites ▸ b.raw_recorded)
 have siteEq : site₁ = site₂ := raw₁.trans raw₂.symm
 have input₁ := List.mem_singleton.mp (gate.centers ▸ a.center_recorded)
 have input₂ := List.mem_singleton.mp (gate.centers ▸ b.center_recorded)
 have inputEq : center₁ = center₂ := input₁.trans input₂.symm
 subst reg₂; subst ctx₂; subst d₂; subst site₂; subst center₂
 have boundsEq : bounds₁ = bounds₂ := Option.some.inj (a.located.symm.trans b.located)
 subst bounds₂
 rfl

def refinement {state : State roles} {plan : Plan roles} {ctx : GeneralNominalCandidates.Context}
 (frame : LocatedFrame state plan) (cert : Refresh state ctx) :
 Refines plan.packet.context.state ctx.state :=
 frame.context_eq.symm ▸ cert.refines

theorem interpretation {state : State roles} {plan : Plan roles} {ctx : GeneralNominalCandidates.Context}
 (frame : LocatedFrame state plan) (cert : Refresh state ctx) :
 ctx.interpretation = plan.packet.context.interpretation :=
 cert.interpretation.trans (congrArg GeneralNominalCandidates.Context.interpretation frame.context_eq).symm

theorem moved {state : State roles} {plan : Plan roles} {ctx : GeneralNominalCandidates.Context}
 (frame : LocatedFrame state plan) (cert : Refresh state ctx) :
 LocatedFrame (GeneralNominalVersionedRefresh232.refresh state ctx) (retarget plan (refinement frame cert)) :=
 ⟨frame.registry_eq,rfl,frame.declaration_eq,frame.raw_recorded,frame.center_recorded,
   GeneralDictionaryRefinedLocations.arguments plan.packet.context ctx (refinement frame cert)
     (inputs root) plan.packet.bounds frame.located⟩

end Yulang.GeneralRebaseRefreshFrame275
