import Yulang.GeneralNominalCanonicalBasis255
import Yulang.GeneralNominalSourceOwnerCandidates252
namespace Yulang.GeneralNominalSourcePublicBasis255
open Core.PresenceGeneration (TyTerm CompTerm)
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234 GeneralNominalVersionedInstall232
open GeneralNominalOwnerCandidates252
open GeneralPresenceCheckedNormal252 (Side)
variable {roles : Roles.RoleDecls} {root : Occurrence roles} {state : State roles}

/-- One data-defined basis, fixed before the trace, using the existing source
owner bound rather than a list of owners seen during execution. -/
def basis (registry : Registry) (context : GeneralNominalCandidates.Context)
 (root : Occurrence roles) (rootLabels : List GeneralDeclarationPatterns.Pattern) : List (TyTerm Nat) :=
 GeneralNominalCanonicalBasis255.basis registry context
   (owners registry context.state.seed root.identity (GeneralNominalPatersonLineage.mass rootLabels))

theorem initial_success (registry : Registry) (context : GeneralNominalCandidates.Context)
 (root : Occurrence roles) (rootLabels : List GeneralDeclarationPatterns.Pattern) (side : Side) :
 GeneralNominalViewNormal255.prepare side (basis registry context root rootLabels)
   (GeneralNominalRebaseRawView243.compile context.state CompTerm.var) =
 some (GeneralNominalViewNormal255.rewrite side (basis registry context root rootLabels)
   (GeneralNominalRebaseRawView243.compile context.state CompTerm.var)) :=
 GeneralNominalCanonicalBasis255.source_success registry context _ side

theorem private_separated
 (source : GeneralNominalSourceFormation.InitialSource registry context root)
 (rootLabels : List GeneralDeclarationPatterns.Pattern)
 (invocation key purpose binder position : Nat) (privatePurpose : purpose ≤ 1)
 (term : TyTerm Nat) (member : term ∈ basis registry context root rootLabels) :
 GeneralNominalPublicBasis253.privateName context.state.seed invocation key purpose binder position ∉
 GeneralPresenceSubstitutionSupport244.typeSources term :=
 GeneralNominalCanonicalBasis255.separated source _ invocation key purpose binder position privatePurpose term member

/-- Each genuinely enabled new installation's public port is supported by the
same fixed basis. This is not closure of every consumer or substitution. -/
theorem installed_port
 (source : GeneralNominalSourceFormation.InitialSource registry context root)
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
 (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
 (path : B4Target.Steps (Step registry root) (initial context root) state)
 (generated : GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence)
 (enabled : Installable registry state effect) (novel : ¬ Committed state effect.plan)
 (name : Nat) (member : name ∈ GeneralNominalPublicPorts253.ports effect.plan.packet.context.state.seed
   effect.plan.packet.site.occurrence.identity effect.plan.packet.declaration) :
 TyTerm.var name ∈ basis registry context root rootLabels := by
 have named := GeneralNominalPublicPorts253.installed_port_enumerated source point ground coverage path generated enabled novel name member
 apply List.mem_eraseDups.mpr
 apply List.mem_append_right
 exact List.mem_map.mpr ⟨name,List.mem_append_right _ named,rfl⟩

theorem installed_port_prepared
 (source : GeneralNominalSourceFormation.InitialSource registry context root)
 (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
 (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
 (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
 (path : B4Target.Steps (Step registry root) (initial context root) state)
 (generated : GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence)
 (enabled : Installable registry state effect) (novel : ¬ Committed state effect.plan)
 (name : Nat) (member : name ∈ GeneralNominalPublicPorts253.ports effect.plan.packet.context.state.seed
   effect.plan.packet.site.occurrence.identity effect.plan.packet.declaration) (side : Side) :
 GeneralPresenceCheckedNormal252.prepare side (basis registry context root rootLabels) (.var name) =
 some (GeneralPresenceCheckedNormal252.normalize side (basis registry context root rootLabels) (.var name)) := by
 apply (GeneralPresenceCheckedNormal252.prepare_exact ..).mpr
 refine ⟨?_,rfl⟩
 have present := installed_port source point ground coverage path generated enabled novel name member
 cases side <;> exact fun _ occurs => List.mem_singleton.mp occurs ▸ present

/-- A single finite, duplicate-free candidate basis obtained from the actual
initial source. It handles the complete initial View and all later enabled
new-installation public ports. No whole-trace substitution closure is claimed. -/
theorem mixed_source_basis (sourceRegistry : Registry) (root : Occurrence roles) (start : State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial sourceRegistry root start) :
 ∃ (context : GeneralNominalCandidates.Context) (pool : List (TyTerm Nat)),
 start = initial context root ∧ pool.Nodup ∧
 (∀ side, GeneralNominalViewNormal255.prepare side pool (GeneralNominalRebaseRawView243.compile context.state CompTerm.var) =
   some (GeneralNominalViewNormal255.rewrite side pool (GeneralNominalRebaseRawView243.compile context.state CompTerm.var))) ∧
 (∀ state, B4Target.Steps ((GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step sourceRegistry root) start state →
   ∀ effect, GeneralNominalSaturationState.Generated state.core.erased.current root effect.plan.packet.site.occurrence →
   Installable (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry) state effect →
   ¬ Committed state effect.plan → ∀ name ∈ GeneralNominalPublicPorts253.ports effect.plan.packet.context.state.seed
     effect.plan.packet.site.occurrence.identity effect.plan.packet.declaration, TyTerm.var name ∈ pool) ∧
 (∀ invocation key purpose binder position, purpose ≤ 1 → ∀ term ∈ pool,
   GeneralNominalPublicBasis253.privateName context.state.seed invocation key purpose binder position ∉
   GeneralPresenceSubstitutionSupport244.typeSources term) := by
 have compiled := GeneralNominalVersionedMixedSourceBoundary234.initial_compiled source
 obtain ⟨legacy,⟨context,labels,formed,point,ground,coverage,rfl⟩,rfl⟩ := compiled
 refine ⟨context,basis (GeneralNominalCenteredHeadAllocEncoding.registry sourceRegistry) context root labels,rfl,
   GeneralNominalCanonicalBasis255.basis_unique _ _ _,initial_success _ context root labels,?_,?_⟩
 · intro state path effect generated enabled novel name member
   exact installed_port formed point ground coverage path generated enabled novel name member
 · intro invocation key purpose binder position privatePurpose term member
   exact private_separated formed labels invocation key purpose binder position privatePurpose term member

end Yulang.GeneralNominalSourcePublicBasis255
