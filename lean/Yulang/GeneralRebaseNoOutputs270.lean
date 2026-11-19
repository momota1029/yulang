import Yulang.GeneralRebaseRankOne269
import Yulang.GeneralNominalVersionedMixedTrace235
import Yulang.GeneralNominalVersionedMixedAncestry237

namespace Yulang.GeneralRebaseNoOutputs270
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCandidates (Context)
open GeneralNominalVersionedJournal232 (State initial)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedMixedTrace235 (Registered generated_registered)
open GeneralNominalVersionedMixedAncestry237 (frame)
open GeneralNominalCenters (Plan)
open GeneralSourceState (Output)
open GeneralRebaseLiveProjection264 (project liveFacts)
open GeneralRebaseMultiSelection263 (ofPlan proposal requests)
open GeneralRebaseCompression266 (Basis)
open GeneralRebaseStep258 (Fact)
open GeneralRebaseBehavior269 (code)
open FiniteRankBehavior269 (Code)

def OutputFree (registry : Registry) : Prop :=
 ∀ declaration ∈ registry.declarations, ∀ clause ∈ declaration.requirements, clause.outputs = []

def QuietSites (source : State roles) : Prop :=
 ∀ raw ∈ source.core.erased.current.sites, raw.occurrence.demand.outputs = []

theorem emitted_quiet (registry : Registry) (outputFree : OutputFree registry)
 (plan : Plan roles) (visible : plan.packet.declaration ∈ registry.declarations)
 (raw : GeneralNominalDemandMerging.Site roles)
 (listed : raw ∈ GeneralNominalVersionedChildren232.rawSites plan) :
 raw.occurrence.demand.outputs = [] := by
 obtain ⟨center,onList,rfl⟩ := List.mem_map.mp listed
 obtain ⟨clause,_,rfl⟩ := List.mem_map.mp onList
 have known := (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mpr clause.property
 have empty := outputFree plan.packet.declaration visible clause.val known
 change clause.val.outputs.map _ = []
 rw [empty]
 rfl

theorem step_quiet (registry : Registry) (root : Occurrence roles) (before after : State roles)
 (outputFree : OutputFree registry) (registered : Registered before root)
 (prior : QuietSites before) (step : Step registry root before after) : QuietSites after := by
 obtain ⟨focus,generated,action⟩ := step
 cases action with
 | administrative admin =>
   cases admin with
   | enqueue linked absent =>
     obtain ⟨s,listed,same⟩ := generated_registered registered generated
     exact False.elim (absent s listed same)
   | refresh | equate | reobserve => exact prior
 | refresh | merge => exact prior
 | install effect enabled _ =>
   intro raw listed
   rcases List.mem_append.mp listed with old | added
   · exact prior raw old
   · exact emitted_quiet registry outputFree effect.plan (frame enabled).visible raw added

theorem initial_quiet (context : Context) (root : Occurrence roles) (empty : root.demand.outputs = []) :
 QuietSites (initial context root) := by
 intro raw listed
 cases List.mem_singleton.mp listed
 exact empty

theorem trace_quiet (registry : Registry) (context : Context) (root : Occurrence roles)
 (outputFree : OutputFree registry) (empty : root.demand.outputs = [])
 (path : B4Target.Steps (Step registry root) (initial context root) target) : QuietSites target := by
 induction path with
 | refl => exact initial_quiet context root empty
 | tail path one ih =>
   have registered := (GeneralNominalVersionedMixedTrace235.steps (GeneralNominalVersionedMixedTrace235.initial context) path).1
   exact step_quiet registry root _ _ outputFree registered ih one

theorem no_requests (state : State roles) (quiet : QuietSites state) (focus : Occurrence roles) :
 GeneralNominalCenteredHeadOutputs.requests state.core focus = [] := by
 apply List.eq_nil_iff_forall_not_mem.mpr
 intro output hit
 obtain ⟨raw,listed,_,requested⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp hit
 rw [quiet raw listed] at requested
 cases requested

theorem no_liveFacts (state : State roles) (quiet : QuietSites state) : liveFacts state = [] := by
 apply List.eq_nil_iff_forall_not_mem.mpr
 intro fact found
 obtain ⟨plan,_,hit⟩ := (GeneralRebaseLiveProjection264.member ..).mp found
 have cleared : requests state.core (ofPlan plan) = [] := by
   rw [requests,GeneralRebaseExecutableRequests262.requests_eq,no_requests state quiet]
 change fact ∈ GeneralRebaseStableClass261.facts plan (ofPlan plan).owner (requests state.core (ofPlan plan)) at hit
 rw [cleared] at hit
 cases hit

theorem fixed (registry : Registry) (context : Context) (root : Occurrence roles)
 (outputFree : OutputFree registry) (empty : root.demand.outputs = [])
 (path : B4Target.Steps (Step registry root) (initial context root) target)
 (owners : List Nat) (pool : List Output) :
 project owners pool target = GeneralRebaseStep258.initial (Basis owners pool) := by
 unfold project
 rw [no_liveFacts target (trace_quiet registry context root outputFree empty path)]
 exact GeneralRebaseWriteAlgebra259.empty _

def terminalCode (basis : List Fact) : Code (List Fact) := .node basis []

theorem exact_code (registry : Registry) (context : Context) (root : Occurrence roles)
 (outputFree : OutputFree registry) (empty : root.demand.outputs = [])
 (path : B4Target.Steps (Step registry root) (initial context root) target)
 (owners : List Nat) (pool : List Output) :
 code registry root owners pool target = terminalCode (Basis owners pool) := by
 have quiet := (GeneralRebaseWeakTerminal268.terminal_iff registry root owners pool target).mpr (by
   intro later future
   rw [fixed registry context root outputFree empty (GeneralRebaseWeakTerminal268.append path future) owners pool,
       fixed registry context root outputFree empty path owners pool])
 rw [GeneralRebaseRankOne269.terminal_code registry root owners pool target quiet,
     fixed registry context root outputFree empty path owners pool]
 rfl

theorem executable_stop (basis : List Fact) (fuel : Nat) :
 FiniteBehaviorDriver269.drive fuel (terminalCode basis) = (0,terminalCode basis) := by
 cases fuel <;> rfl

end Yulang.GeneralRebaseNoOutputs270
