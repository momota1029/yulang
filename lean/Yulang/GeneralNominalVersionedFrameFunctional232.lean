import Yulang.GeneralNominalVersionedEvidence231
set_option backward.isDefEq.respectTransparency false

/-! Frame functionality under explicit singleton storage hypotheses. This is
not global uniqueness of current frames for arbitrary multi-site journals. -/
namespace Yulang.GeneralNominalVersionedFrameFunctional232
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedEvidence231

theorem frame_plan_unique {registry : Registry} {state : GeneralNominalCenteredSteps.State roles}
    (declarations : registry.declarations = [declaration])
    (raw : state.erased.current.sites = [rawSite]) (centers : state.sites = [center])
    (one : Frame registry state root key first) (two : Frame registry state root other last) :
    first = last := by
  rcases first with ⟨⟨reg₁,ctx₁,site₁,decl₁,check₁,bounds₁⟩,input₁,inputEq₁⟩
  rcases last with ⟨⟨reg₂,ctx₂,site₂,decl₂,check₂,bounds₂⟩,input₂,inputEq₂⟩
  have regEq₁ : reg₁ = registry := one.registry_eq
  have regEq₂ : reg₂ = registry := two.registry_eq
  have ctxEq₁ : ctx₁ = state.erased.current.context := one.context_eq
  have ctxEq₂ : ctx₂ = state.erased.current.context := two.context_eq
  have declEq₁ : decl₁ = declaration := List.mem_singleton.mp (declarations ▸ one.visible)
  have declEq₂ : decl₂ = declaration := List.mem_singleton.mp (declarations ▸ two.visible)
  have siteEq₁ : site₁ = rawSite := List.mem_singleton.mp (raw ▸ one.raw_recorded)
  have siteEq₂ : site₂ = rawSite := List.mem_singleton.mp (raw ▸ two.raw_recorded)
  have inputSame₁ : input₁ = center := List.mem_singleton.mp (centers ▸ one.center_recorded)
  have inputSame₂ : input₂ = center := List.mem_singleton.mp (centers ▸ two.center_recorded)
  subst reg₁; subst reg₂; subst ctx₁; subst ctx₂
  subst decl₁; subst decl₂; subst site₁; subst site₂; subst input₁; subst input₂
  have boundsEq : bounds₁ = bounds₂ := Option.some.inj (one.located.symm.trans two.located)
  subst bounds₂
  rfl

theorem frame_key_unique {registry : Registry} {state : GeneralNominalCenteredSteps.State roles}
    (declarations : registry.declarations = [declaration])
    (one : Frame registry state root key first) (two : Frame registry state root other last) :
    key = other := by
  have firstDecl : first.packet.declaration = declaration := List.mem_singleton.mp (declarations ▸ one.visible)
  have lastDecl : last.packet.declaration = declaration := List.mem_singleton.mp (declarations ▸ two.visible)
  exact one.key_eq.symm.trans ((congrArg Declaration.id (firstDecl.trans lastDecl.symm)).trans two.key_eq)

end Yulang.GeneralNominalVersionedFrameFunctional232
