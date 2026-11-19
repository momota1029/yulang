import Yulang.GeneralRebaseCandidateShell267

namespace Yulang.GeneralRebaseCandidatePlan267
open GeneralDeclarations (Registry Declaration DeclarationChecked)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalSaturationState (Packet)
open GeneralNominalDemandMerging renaming Site → RawSite
open GeneralNominalCenters (Plan Site)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedCandidates231 (inputs Prepared)
open GeneralNominalRecursiveCandidates (arguments)
open GeneralRebaseExecutableGenerated267 (discover discover_exact)
open GeneralRebaseOccurrenceEq267 (same same_exact)

abbrev DeclChecked (registry : Registry) (roles : Roles.RoleDecls) :=
 ∀ declaration ∈ registry.declarations, DeclarationChecked registry.constructors roles declaration

/-- The data-only part of the actual Frame, plus generatedness. Prepared
is intentionally separate: it asks for actual head models. -/
structure Shell (registry : Registry) (state : State roles) (root : Occurrence roles)
 (plan : Plan roles) : Prop where
 registry_eq : plan.packet.registry = registry
 context_eq : plan.packet.context = state.core.erased.current.context
 generated : GeneralNominalSaturationState.Generated state.core.erased.current root plan.packet.site.occurrence
 raw : plan.packet.site ∈ state.core.erased.current.sites
 center : plan.input ∈ state.core.sites
 visible : plan.packet.declaration ∈ registry.declarations
 role_eq : plan.packet.declaration.role = plan.packet.site.occurrence.demand.role
 located : arguments plan.packet.context (inputs plan.packet.site.occurrence) = some plan.packet.bounds

local instance : DecidableEq (Occurrence roles) := GeneralRebaseOccurrenceEq267.occurrenceEq

def build (registry : Registry) (state : State roles) (checked : DeclChecked registry roles)
 (focus : Occurrence roles) (decl : {d // d ∈ registry.declarations}) (raw : RawSite roles) (center : Site roles) :
 Option (Plan roles) :=
 if decl.val.role = focus.demand.role then
  if raw.occurrence = focus then
   if sameCenter : center.occurrence = raw.occurrence then
    (arguments state.core.erased.current.context (inputs raw.occurrence)).map fun bounds =>
      ⟨⟨registry,state.core.erased.current.context,raw,decl.val,checked decl.val decl.property,bounds⟩,center,sameCenter⟩
   else none
  else none
 else none


theorem build_sound (registry : Registry) (state : State roles) (checked : DeclChecked registry roles)
 (focus : Occurrence roles) (decl : {d // d ∈ registry.declarations}) (raw : RawSite roles) (center : Site roles)
 (plan : Plan roles) (result : build registry state checked focus decl raw center = some plan)
 (generated : GeneralNominalSaturationState.Generated state.core.erased.current root focus)
 (rawListed : raw ∈ state.core.erased.current.sites) (centerListed : center ∈ state.core.sites) :
 Shell registry state root plan := by
 unfold build at result
 split at result <;> try contradiction
 rename_i matching
 split at result <;> try contradiction
 rename_i rawFocus
 split at result <;> try contradiction
 generalize found : arguments state.core.erased.current.context (inputs raw.occurrence) = answer at result
 cases answer with
 | none => contradiction
 | some bounds =>
   simp only [Option.map_some,Option.some.injEq] at result
   subst plan
   exact ⟨rfl,rfl,rawFocus.symm ▸ generated,rawListed,centerListed,decl.property,matching.trans (congrArg (fun o : Occurrence roles => o.demand.role) rawFocus).symm,found⟩

theorem build_recreates (registry : Registry) (state : State roles) (checked : DeclChecked registry roles)
 (plan : Plan roles) (shell : Shell registry state root plan) :
 build registry state checked plan.packet.site.occurrence ⟨plan.packet.declaration,shell.visible⟩
   plan.packet.site plan.input = some plan := by
 unfold build
 rw [ite_eq_left shell.role_eq,ite_eq_left rfl,dite_eq_left plan.input_exact]
 rw [←shell.context_eq,shell.located]
 cases plan with
 | mk packet center equal =>
   cases packet with
   | mk r c raw d valid bounds =>
     rcases shell with ⟨reg,ctx,_,_,_,_,_,_⟩
     dsimp at reg ctx ⊢
     subst r
     subst c
     rfl

end Yulang.GeneralRebaseCandidatePlan267
