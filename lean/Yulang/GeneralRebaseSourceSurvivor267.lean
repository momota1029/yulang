import Yulang.GeneralRebaseCandidatePrepared267
import Yulang.GeneralNominalVersionedMixedSelectedFrame235

namespace Yulang.GeneralRebaseSourceSurvivor267
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalSaturationState (Generated Packet)
open GeneralNominalVersionedCandidates231 (Survivor Prepared)
open GeneralRebaseCandidatePlan267 (DeclChecked)
open GeneralRebaseCandidatePrepared267 (readyPlans ready_exact prepared_iff headCondition)
open GeneralNominalRecursiveCandidates (Metadata)

abbrev Boundary (roles : Roles.RoleDecls) := GeneralNominalVersionedMixedSourceBoundary234.boundary roles
abbrev Encoded := GeneralNominalCenteredHeadAllocEncoding.registry

theorem declChecked (checked : (Boundary roles).Checked registry) : DeclChecked (Encoded registry) roles := by
 have same : registry.roles = roles := checked.1
 rw [←same]
 exact (GeneralNominalCenteredHeadAllocEncoding.registry_checked checked.2).2

/-- On a real reachable source, *every* survivor yields a generated plan
that is enumerated, not just an already-selected unique winner. -/
theorem from_survivor (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry)
 (reachable : B4TargetV8.Reachable (Boundary roles) registry root state)
 (generated : Generated state.core.erased.current root focus)
 (survivor : Survivor (Encoded registry) state.core.erased.current.context focus key children) :
 ∃ plan ∈ readyPlans (Encoded registry) state root (declChecked checked),
 plan.packet.site.occurrence = focus ∧ plan.packet.declaration.id = key ∧
 GeneralNominalVersionedFrame231.children plan.packet = children ∧ headCondition plan := by
 obtain ⟨raw,rawListed,rawEq⟩ :=
   GeneralNominalVersionedMixedTrace235.generated_registered (GeneralNominalVersionedMixedTrace235.reachable reachable).1 generated
 obtain ⟨center,centerListed,centers⟩ := (GeneralNominalVersionedMixedTrace235.reachable reachable).2.2 raw rawListed
 obtain ⟨known,decl,listed,isChecked,keyEq,role,bounds,located,prepared,kids⟩ := survivor
 let packet : Packet roles := ⟨Encoded registry,state.core.erased.current.context,raw,decl,isChecked,bounds⟩
 let plan : Plan roles := ⟨packet,center,centers⟩
 have valid : Prepared (Encoded registry) state.core.erased.current.context plan.packet.site.occurrence decl := by
   simpa only [plan,packet,rawEq] using prepared
 have shell : GeneralRebaseCandidatePlan267.Shell (Encoded registry) state root plan :=
   ⟨rfl,rfl,rawEq.symm ▸ generated,rawListed,centerListed,listed,
     role.trans (congrArg (fun o : Occurrence roles => o.demand.role) rawEq).symm,
     by simpa only [plan,packet,rawEq] using located⟩
 have h := (prepared_iff (Encoded registry) state root plan shell).mp valid
 have actualChildren : GeneralNominalVersionedFrame231.children plan.packet = children := by
   unfold GeneralNominalVersionedCandidates231.children at kids
   change GeneralNominalVersionedFrame231.children
     ⟨Encoded registry,state.core.erased.current.context,raw,decl,isChecked,bounds⟩ = children
   rw [kids]
   -- For child output, the raw-site input descriptors are irrelevant.
   unfold GeneralNominalVersionedFrame231.children
   simp only [GeneralDictionaryEmissionPlans.children,GeneralNominalVersionedFrame231.frame,Packet.bindings,rawEq]
   rfl
 refine ⟨plan,(ready_exact ..).mpr ⟨shell,?_ ,h.2.1⟩,rawEq,keyEq,actualChildren,h.2.2⟩
 simpa only [plan,packet,rawEq] using known

theorem to_survivor (registry : Registry) (state : State roles) (root : Occurrence roles)
 (checked : DeclChecked registry roles) (plan : Plan roles)
 (member : plan ∈ readyPlans registry state root checked)
 (metadata : Metadata registry state.core.erased.current.context)
 (head : headCondition plan) :
 Survivor registry state.core.erased.current.context plan.packet.site.occurrence
    plan.packet.declaration.id (GeneralNominalVersionedFrame231.children plan.packet) := by
 obtain ⟨shell,known,bits⟩ := (ready_exact ..).mp member
 have prepared := (prepared_iff registry state root plan shell).mpr ⟨metadata,bits,head⟩
 have frame : GeneralNominalVersionedEvidence231.Frame registry state.core
     plan.packet.site.occurrence plan.packet.declaration.id plan :=
   ⟨shell.registry_eq,shell.context_eq,rfl,rfl,shell.raw,shell.center,shell.visible,shell.role_eq,shell.located,prepared⟩
 exact GeneralNominalVersionedMixedFrameSelection235.frame_survivor frame known

end Yulang.GeneralRebaseSourceSurvivor267
