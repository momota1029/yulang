import Yulang.GeneralNominalRebaseStablePool243
import Yulang.GeneralNominalRebaseInlineSupport243
namespace Yulang.GeneralNominalRebaseSourceSteps243
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalState (sources atomSources typeSources)
open GeneralNominalAllocationSupport
open GeneralNominalRebaseInline241
open GeneralNominalRebaseDefinitions241 (entries)
open GeneralNominalInvocationAncestry (frontier)

noncomputable def inlineReport (state : GeneralNominalState.State) (root declaration : Nat)
 (names : List Nat) (report : GeneralNominalRecursiveInspection.Report state) : GeneralNominalState.State :=
 { state with ordinary := state.ordinary.map (atomSubst (substitution
   (entries state.seed root declaration (GeneralNominalRecursiveInspection.bindings state report) names))) }

def discard (state : GeneralNominalState.State) (keep : PresenceNormalForm.Atom Nat → Bool) : GeneralNominalState.State :=
 { state with ordinary := state.ordinary.filter keep }

theorem ordinary_member (supported : sources state ⊆ pool) (atom : PresenceNormalForm.Atom Nat) (present : atom ∈ state.ordinary) : atomSources atom ⊆ pool := by
 intro name member
 exact supported (List.mem_append_right _ (List.mem_flatMap.mpr ⟨atom,present,member⟩))

theorem ordinary_replace (state : GeneralNominalState.State) (atoms : List (PresenceNormalForm.Atom Nat))
 (supported : sources state ⊆ pool) (new : ∀ atom ∈ atoms, atomSources atom ⊆ pool) :
 sources {state with ordinary := atoms} ⊆ pool := by
 intro name member
 rcases List.mem_append.mp member with base | ordinary
 · exact supported (List.mem_append_left _ base)
 · obtain ⟨atom,present,within⟩ := List.mem_flatMap.mp ordinary
   exact new atom present within

theorem inline_supported (state : GeneralNominalState.State) (root declaration : Nat)
 (names : List Nat) (report : GeneralNominalRecursiveInspection.Report state)
 (supported : sources state ⊆ pool) : sources (inlineReport state root declaration names report) ⊆ pool := by
 apply ordinary_replace state _ supported
 intro atom member
 obtain ⟨old,present,rfl⟩ := List.mem_map.mp member
 apply GeneralNominalRebaseInlineSupport243.atom_inline_support _ old (ordinary_member supported old present)
 intro entry included name within
 have endpoints : Endpoints (GeneralNominalRecursiveInspection.bindings state report) pool := by
   intro binding member
   have found := report_endpoints state report binding member
   exact ⟨supported found.1,supported found.2⟩
 exact GeneralNominalRebaseDefinitions241.supported state.seed root declaration _ names endpoints entry included name within

theorem discard_supported (supported : sources state ⊆ pool) (keep) : sources (discard state keep) ⊆ pool := by
 apply ordinary_replace state _ supported
 intro atom member
 exact ordinary_member supported atom (List.mem_filter.mp member).1

inductive Step (registry : Registry) (initial : GeneralNominalCandidates.Context) (root budget : Nat) :
 GeneralNominalState.State → GeneralNominalState.State → Prop
 | reserveInstall {roles : Roles.RoleDecls} (packet : GeneralNominalSaturationState.Packet roles)
   (sameRegistry : packet.registry = registry)
   (sameSeed : packet.context.state.seed = initial.state.seed)
   (visible : packet.declaration ∈ registry.declarations)
   (parent : packet.site.occurrence.identity ∈ frontier registry initial.state.seed root budget) :
   Step registry initial root budget packet.context.state packet.privateContext.state
 | inline (before : GeneralNominalState.State) (owner declaration : Nat) (names : List Nat)
   (report : GeneralNominalRecursiveInspection.Report before) :
   Step registry initial root budget before (inlineReport before owner declaration names report)
 | discard (before : GeneralNominalState.State) (keep : PresenceNormalForm.Atom Nat → Bool) :
   Step registry initial root budget before (discard before keep)
 | equate (before : GeneralNominalState.State) (first last : Nat)
   (one : first ∈ sources before) (two : last ∈ sources before) :
   Step registry initial root budget before
     (GeneralNominalState.extend before [] (GeneralNominalAllocation.equations first (.var last)))
 | refresh {roles : Roles.RoleDecls} (before : GeneralNominalVersionedJournal232.State roles)
   (context : GeneralNominalCandidates.Context)
   (certificate : GeneralNominalVersionedMixedObservations233.Refresh before context) :
   Step registry initial root budget before.core.erased.current.context.state context.state
 | reobserve {roles : Roles.RoleDecls} (before : GeneralNominalSaturationState.State roles)
   (revision : GeneralNominalReobservationSteps.Revision before) :
   Step registry initial root budget before.context.state revision.snapshot

theorem step_supported (action : Step registry initial root budget before after)
 (supported : sources before ⊆ GeneralNominalRebaseStablePool243.pool registry initial root budget) :
 sources after ⊆ GeneralNominalRebaseStablePool243.pool registry initial root budget := by
 cases action with
 | reserveInstall packet sameRegistry sameSeed visible parent =>
   apply private_sources packet (sameRegistry ▸ visible) supported
   rw [sameRegistry]
   exact GeneralNominalRebaseStablePool243.reserved_supported sameSeed parent
 | inline before owner declaration names report => exact inline_supported before owner declaration names report supported
 | discard before keep => exact discard_supported supported keep
 | equate before first last one two =>
   apply extend_sources before [] _ supported (by intro name member; cases member)
   intro atom member
   exact equation_sources first (.var last) (supported one)
     (fun name present => List.mem_singleton.mp present ▸ supported two) atom member
 | refresh before context certificate => exact fun name member => supported (certificate.support name member)
 | reobserve => exact supported

theorem trace_supported (path : B4Target.Steps (Step registry initial root budget) initial.state after) :
 sources after ⊆ GeneralNominalRebaseStablePool243.pool registry initial root budget := by
 induction path with
 | refl => exact GeneralNominalRebaseStablePool243.initial_supported
 | tail path action ih => exact step_supported action ih
end Yulang.GeneralNominalRebaseSourceSteps243
