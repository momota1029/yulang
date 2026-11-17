import Yulang.GeneralNominalRebaseMergeSupport243
import Yulang.GeneralNominalPointRevision240
namespace Yulang.GeneralNominalRebaseSourceTrace244
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalAllocationSupport
open GeneralNominalRebaseStablePool243 (pool)
open GeneralNominalRebaseChildProducer243 GeneralNominalRebaseChildrenUniverse243
open GeneralNominalRebaseMergeSupport243
structure State (roles : Roles.RoleDecls) where
 raw : GeneralNominalState.State
 sites : List (Occurrence roles)
def initialState (initial : GeneralNominalCandidates.Context) (root : Occurrence roles) : State roles :=
 ⟨initial.state,[root]⟩
def Good (registry : Registry) (checked : Checked registry) (initial : GeneralNominalCandidates.Context)
 (root : Occurrence registry.roles) (budget : Nat) (state : State registry.roles) : Prop :=
 GeneralNominalState.sources state.raw ⊆ pool registry initial root.identity budget ∧
 state.sites ⊆ sitesPool registry checked initial root budget

theorem emitted_supported (checked : Checked registry)
 (supported : GeneralNominalState.sources state ⊆ pool registry initial root budget)
 (seed : state.seed = initial.state.seed)
 (parent : site.identity ∈ GeneralNominalInvocationAncestry.frontier registry initial.state.seed root budget)
 (report : GeneralNominalRecursiveInspection.Report state)
 (visible : declaration ∈ registry.declarations)
 (member : child ∈ GeneralNominalAllocation.children state registry site declaration
   (checked.2 declaration visible) (GeneralNominalRecursiveInspection.bindings state report)) :
 child ∈ childrenPool registry checked initial root budget := by
 unfold GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children at member
 obtain ⟨emission,present,rfl⟩ := List.mem_map.mp member
 have old := (GeneralCanonicalChildOrder.canonicalEmit_perm site.identity declaration
   (checked.2 declaration visible) _ _).mem_iff.mpr present
 unfold GeneralDeclarationDemands.emitAll at old
 obtain ⟨clause,_,same⟩ := List.mem_map.mp old
 cases same
 apply List.mem_flatMap.mpr
 refine ⟨site.identity,parent,List.mem_flatMap.mpr ?_⟩
 refine ⟨⟨declaration,visible⟩,List.mem_attach _ _,List.mem_flatMap.mpr ?_⟩
 refine ⟨clause,List.mem_attach _ _,List.mem_map.mpr ?_⟩
 have endpoints : Endpoints (GeneralNominalRecursiveInspection.bindings state report)
     (pool registry initial root budget) := by
   intro entry present
   have old := report_endpoints state report entry present
   exact ⟨supported old.1,supported old.2⟩
 have found := child_finite endpoints (GeneralNominalRebaseStablePool243.reserved_supported seed parent)
   visible (checked.2 declaration visible).scope clause.property
   ((checked.2 declaration visible).signature.2.2.2 clause.val clause.property)
 rw [candidates_seed seed] at found
 refine ⟨_,found,?_⟩
 dsimp only [GeneralDictionaryEmissionPlans.occurrence, GeneralDeclarationDemands.emit,
   GeneralNominalAllocation.frame, GeneralNominalAllocation.source]
 rw [seed]

inductive Step (registry : Registry) (initial : GeneralNominalCandidates.Context)
 (root : Occurrence registry.roles) (budget : Nat) : State registry.roles → State registry.roles → Prop
 | install (before : State registry.roles) (packet : GeneralNominalSaturationState.Packet registry.roles)
   (context : packet.context.state = before.raw) (sameRegistry : packet.registry = registry)
   (sameSeed : packet.context.state.seed = initial.state.seed)
   (visible : packet.declaration ∈ registry.declarations)
   (registered : packet.site.occurrence ∈ before.sites)
   (parent : packet.site.occurrence.identity ∈ GeneralNominalInvocationAncestry.frontier registry initial.state.seed root.identity budget) :
   Step registry initial root budget before ⟨packet.privateContext.state,before.sites ++ packet.children⟩
 | inline (before : State registry.roles) (owner declaration : Nat) (names : List Nat)
   (report : GeneralNominalRecursiveInspection.Report before.raw) :
   Step registry initial root budget before
     ⟨GeneralNominalRebaseSourceSteps243.inlineReport before.raw owner declaration names report,before.sites⟩
 | discard (before : State registry.roles) (keep : PresenceNormalForm.Atom Nat → Bool) :
   Step registry initial root budget before ⟨GeneralNominalRebaseSourceSteps243.discard before.raw keep,before.sites⟩
 | equate (before : State registry.roles) (first last : Nat)
   (one : first ∈ GeneralNominalState.sources before.raw) (two : last ∈ GeneralNominalState.sources before.raw) :
   Step registry initial root budget before
     ⟨GeneralNominalState.extend before.raw [] (GeneralNominalAllocation.equations first (.var last)),before.sites⟩
 | refresh (before : State registry.roles) (journal : GeneralNominalVersionedJournal232.State registry.roles)
   (same : journal.core.erased.current.context.state = before.raw) (context : GeneralNominalCandidates.Context)
   (certificate : GeneralNominalVersionedMixedObservations233.Refresh journal context) :
   Step registry initial root budget before ⟨context.state,before.sites⟩
 | reobserve (before : State registry.roles) (raw : GeneralNominalSaturationState.State registry.roles)
   (same : raw.context.state = before.raw) (revision : GeneralNominalReobservationSteps.Revision raw)
   (pointSafe : GeneralNominalPointRevision240.Preserves revision) :
   Step registry initial root budget before ⟨revision.snapshot,before.sites⟩
 | merge (before : State registry.roles) (first last : GeneralNominalDemandMerging.Site registry.roles)
   (one : first.occurrence ∈ before.sites) (two : last.occurrence ∈ before.sites) :
   Step registry initial root budget before
     ⟨GeneralNominalState.extend before.raw [] (GeneralNominalDemandMerging.outputAtoms first last),before.sites⟩

theorem step_good (checked : Checked registry)
 (linked : GeneralNominalState.Linked initial.state root.demand)
 (action : Step registry initial root budget before after)
 (good : Good registry checked initial root budget before) :
 Good registry checked initial root budget after := by
 cases action with
 | install before packet context sameRegistry sameSeed visible registered parent =>
   constructor
   · apply private_sources packet (sameRegistry ▸ visible) (context ▸ good.1)
     rw [sameRegistry]
     exact GeneralNominalRebaseStablePool243.reserved_supported sameSeed parent
   · intro child present
     rcases List.mem_append.mp present with old | new
     · exact good.2 old
     · apply List.mem_cons_of_mem
       have copied := new
       unfold GeneralNominalSaturationState.Packet.children at copied
       rcases packet with ⟨packetRegistry,packetContext,packetSite,packetDeclaration,packetChecked,bounds⟩
       dsimp only at sameRegistry context sameSeed visible parent copied
       subst packetRegistry
       exact emitted_supported checked (context ▸ good.1) sameSeed parent
         (GeneralNominalRecursiveCandidates.report packetContext packetDeclaration bounds) visible copied
 | inline before owner declaration names report =>
   exact ⟨GeneralNominalRebaseSourceSteps243.inline_supported before.raw owner declaration names report good.1,good.2⟩
 | discard before keep => exact ⟨GeneralNominalRebaseSourceSteps243.discard_supported good.1 keep,good.2⟩
 | equate before first last one two =>
   exact ⟨GeneralNominalRebaseSourceSteps243.step_supported (.equate before.raw first last one two) good.1,good.2⟩
 | refresh before journal same context certificate =>
   exact ⟨fun _ h => good.1 (same ▸ certificate.support _ h),good.2⟩
 | reobserve before raw same revision pointSafe =>
   exact ⟨fun _ h => good.1 (same ▸ h),good.2⟩
 | merge before first last one two =>
   refine ⟨extend_sources before.raw [] _ good.1 (by intro _ h; cases h) ?_,good.2⟩
   exact output_atoms first last (fun _ h => site_outputs checked linked (good.2 one) h)
     (fun _ h => site_outputs checked linked (good.2 two) h)

theorem trace_good (checked : Checked registry)
 (linked : GeneralNominalState.Linked initial.state root.demand)
 (path : B4Target.Steps (Step registry initial root budget) (initialState initial root) state) :
 Good registry checked initial root budget state := by
 induction path with
 | refl => exact ⟨GeneralNominalRebaseStablePool243.initial_supported,fun _ h =>
     List.mem_cons.mpr (Or.inl (List.mem_singleton.mp h))⟩
 | tail path action ih => exact step_good checked linked action ih
end Yulang.GeneralNominalRebaseSourceTrace244
