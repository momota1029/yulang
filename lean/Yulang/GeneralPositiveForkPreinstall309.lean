import Yulang.GeneralPositiveForkPlan309
import Yulang.GeneralNominalVersionedMixedReady235

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 11500000
namespace Yulang.GeneralPositiveForkPreinstall309
open GeneralPositiveForkSource309
open GeneralPositiveForkPlan309 (packet plan report ordered_children kids)
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples (model context state state_models)
open GeneralNominalVersionedCandidates231
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedJournal232 (Effect)
open GeneralNominalVersionedPlans231 (head_models)
open GeneralNominalCenters (Plan)
open GeneralDeclarations
open GeneralNominalRecursiveCandidates (Metadata arguments)
open GeneralNominalVersionedMixedKernel234 (AlternativesSafe)
open GeneralNominalVersionedCycles232 (Safe)

theorem compiled_checked : Checked compiled :=
  GeneralNominalCenteredHeadAllocEncoding.registry_checked checked

theorem member_parent {d : Declaration} (h : d ∈ compiled.declarations) (role : d.role = root.demand.role) :
    d = parent := by
  change d ∈ [right,parent,left] at h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl|rfl|rfl
  · cases role
  · rfl
  · cases role

theorem located : arguments (context true) (inputs root) = some [(0,0)] := by decide +kernel

theorem known : ¬ GeneralNominalState.RootPending (state true) (inputs root).demand := by
  rintro ⟨i,no⟩
  exact no ⟨(0 : Fin 2),rfl,Or.inr ⟨_,rfl⟩⟩

theorem fresh (owner : Nat) (bindings : GeneralNominalAllocation.Bindings) :
    GeneralNominalVersionedAllocation231.Fresh (state true) compiled owner bindings := by
  intro key _ hit
  have bound := init_source.below_seed _ hit
  exact False.elim (Nat.not_lt_of_ge bound (GeneralNominalIdentities.source_above_seed _ _))

theorem prepared : Prepared compiled (context true) root parent := by
  have linked : GeneralNominalState.Linked (state true) (inputs root).demand :=
    ⟨init_source.linked.1,fun _ absent => nomatch absent⟩
  refine ⟨⟨rfl,init_source.metadata.2⟩,linked,[(0,0)],located,fresh _ _,?_,
    model,head_models (GeneralPositiveForkPlan309.holds model (state_models true))⟩
  change GeneralNominalRecursiveInspection.Finished (GeneralNominalPacketSupport.report packet)
  rw [report]; exact ⟨rfl,rfl,rfl⟩

theorem frame : Frame compiled initial.core root parent.id plan :=
  ⟨rfl,rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,
    List.mem_cons_of_mem _ List.mem_cons_self,rfl,located,prepared⟩

theorem survivor : Survivor compiled (context true) root parent.id kids :=
  ⟨known,parent,List.mem_cons_of_mem _ List.mem_cons_self,parent_checked,rfl,rfl,[(0,0)],located,
    prepared,ordered_children.symm⟩

theorem unique : Unique compiled (context true) root parent.id kids := by
  refine ⟨survivor,?_⟩
  intro k cs h
  have copy := h
  obtain ⟨_,d,mem,_,id,role,_⟩ := copy
  cases member_parent mem role
  subst k
  exact ⟨rfl,survivor_children_functional compiled_checked h survivor⟩

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready initial.core root plan :=
  GeneralNominalVersionedMixedReady235.ready ⟨rfl,checked⟩ init_reached frame

theorem administrative : GeneralNominalVersionedDiagnostic232.AdministrativeReady initial root := by
  refine ⟨⟨plan.input,List.mem_singleton_self _,rfl⟩,?_⟩
  intro a one _ b two _
  cases List.mem_singleton.mp one
  cases List.mem_singleton.mp two
  exact .refl _

theorem safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles)
    compiled initial root := by
  refine ⟨known,?_,?_,?_⟩
  · rintro (raw | (⟨i,cyclic⟩ | ⟨site,_,_,i,cyclic⟩))
    · obtain ⟨_,_,_,slot,_,cyclic⟩ := raw
      exact GeneralRebaseDisplaySafety276.raw_acyclic (state true) rfl (state_models true) slot cyclic
    · exact GeneralRebaseDisplaySafety276.semantic init_model _ cyclic
    · exact GeneralRebaseDisplaySafety276.semantic init_model _ cyclic
  · rintro (raw | ⟨p,_,entry,_,cyclic⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cyclic⟩ := raw
      exact GeneralRebaseDisplaySafety276.raw_acyclic (state true) rfl (state_models true) visited.1 cyclic
    · exact GeneralRebaseDisplaySafety276.semantic init_model _ cyclic
  · rintro (⟨_,d,visible,role,_,notPrepared⟩ | pending)
    · cases member_parent visible role
      exact notPrepared prepared
    · exact pending administrative

theorem positions : Safe initial plan := by
  refine ⟨?_,fun _ _ => GeneralRebaseDisplaySafety276.semantic init_model _⟩
  exact GeneralRebaseDisplaySafety276.position_length

theorem alternatives : AlternativesSafe compiled initial plan.input := by
  intro p matched framed
  have f : Frame compiled initial.core root p.packet.declaration.id p := framed
  have raw : p.packet.site = plan.packet.site := List.mem_singleton.mp f.raw_recorded
  have same := GeneralRebaseScopedFrame276.same_frame f frame (member_parent f.visible f.role_eq) raw matched
  subst p
  exact positions

def effect : Effect roles :=
  ⟨compiled,initial.core,plan,frame,ordered_children ▸ unique,ready⟩

end Yulang.GeneralPositiveForkPreinstall309
