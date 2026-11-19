import Yulang.GeneralRebaseDirectedRoot268

namespace Yulang.GeneralRebaseDirectedCandidate268
open GeneralDeclarations (Registry)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalCenters (Plan)
open GeneralSourceDictionaries (Occurrence)
open GeneralRebaseSourceSurvivor267 (Boundary Encoded declChecked)
open GeneralRebaseHeadProbe267 (atFocus atFocus_exact Honest)
open GeneralRebaseCandidatePrepared267 (ready_exact prepared_iff)
open GeneralRebaseDirectCycles268 (cycle cycle_exact)
open GeneralRebasePartialBool268 (Reflect)

def visited (plan : Plan roles) : Bool :=
 (GeneralNominalRecursiveCandidates.report plan.packet.context plan.packet.declaration plan.packet.bounds).inspected.any
   fun bounds => cycle plan.packet.context.state bounds.1

theorem visited_exact (plan : Plan roles) : visited plan = true ↔
 ∃ bounds ∈ (GeneralNominalRecursiveCandidates.report plan.packet.context plan.packet.declaration plan.packet.bounds).inspected,
   GeneralNominalCycleK2.DirectCycle plan.packet.context.state bounds.1 := by
 simp [visited,List.any_eq_true,cycle_exact]

def check (entries : List (Plan roles)) (head : Plan roles → Option Bool) : Bool :=
 entries.any fun plan => (head plan == some true) && visited plan

theorem direct_op (registry : Registry) (ctx : GeneralNominalCandidates.Context)
 (plan : Plan roles) (focus : Occurrence roles)
 (sameCtx : plan.packet.context = ctx)
 (listed : plan.packet.declaration ∈ registry.declarations)
 (checked : GeneralDeclarations.DeclarationChecked registry.constructors roles plan.packet.declaration)
 (roleEq : plan.packet.declaration.role = focus.demand.role)
 (located : GeneralNominalRecursiveCandidates.arguments plan.packet.context (GeneralNominalVersionedCandidates231.inputs focus) = some plan.packet.bounds)
 (known : ¬ GeneralNominalState.RootPending ctx.state (GeneralNominalVersionedCandidates231.inputs focus).demand)
 (prepared : GeneralNominalVersionedCandidates231.Prepared registry ctx focus plan.packet.declaration)
 (cyclic : visited plan = true) :
 GeneralNominalVersionedCycles232.RawCandidateK2 registry ctx (GeneralNominalVersionedCandidates231.inputs focus) := by
 cases sameCtx
 have identical : GeneralNominalVersionedCandidates231.inputs focus =
    GeneralNominalVersionedCandidates231.inputs (GeneralNominalVersionedCandidates231.inputs focus) :=
    (GeneralNominalVersionedCandidates231.inputs_idempotent focus).symm
 have present := (GeneralNominalVersionedCandidates231.prepared_ignores_outputs identical).mp prepared
 obtain ⟨bounds,onReport,direct⟩ := (visited_exact ..).mp cyclic
 exact ⟨known,plan.packet.declaration,listed,checked,roleEq,present,plan.packet.bounds,located,
   bounds,onReport,Or.inl direct⟩

theorem witness (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry)
 (head : Plan roles → Option Bool)
 (honest : Honest head (atFocus (Encoded registry) state root focus (declChecked checked)))
 (metadata : GeneralNominalRecursiveCandidates.Metadata (Encoded registry) state.core.erased.current.context)
 (seen : check (atFocus (Encoded registry) state root focus (declChecked checked)) head = true) :
 GeneralNominalVersionedCycles232.RawCandidateK2 (Encoded registry) state.core.erased.current.context
  (GeneralNominalVersionedCandidates231.inputs focus) := by
 simp only [check,List.any_eq_true,Bool.and_eq_true,beq_iff_eq] at seen
 obtain ⟨plan,onTable,positive,cyclic⟩ := seen
 obtain ⟨ready,focusExact⟩ := (atFocus_exact ..).mp onTable
 obtain ⟨shell,known,control⟩ := (ready_exact ..).mp ready
 have prepared := (prepared_iff _ _ _ _ shell).mpr ⟨metadata,control,honest.positive plan onTable positive⟩
 have initial := shell.located
 have actualCheck := plan.packet.checked
 rw [shell.registry_eq] at actualCheck
 rw [focusExact] at initial known prepared
 exact direct_op (Encoded registry) state.core.erased.current.context plan focus shell.context_eq
   shell.visible actualCheck (by simpa only [←focusExact] using shell.role_eq) initial known prepared cyclic

def probe (entries : List (Plan roles)) (head : Plan roles → Option Bool) : Option Bool :=
 if check entries head then some true else none

theorem probe_sound (registry : Registry) (state : State roles) (root focus : Occurrence roles)
 (checked : (Boundary roles).Checked registry)
 (head : Plan roles → Option Bool)
 (honest : Honest head (atFocus (Encoded registry) state root focus (declChecked checked)))
 (metadata : GeneralNominalRecursiveCandidates.Metadata (Encoded registry) state.core.erased.current.context) :
 Reflect ((Boundary roles).CandidateK2 registry state focus)
   (probe (atFocus (Encoded registry) state root focus (declChecked checked)) head) := by
 unfold probe
 split
 · rename_i seen
   exact Or.inl (witness registry state root focus checked head honest metadata seen)
 · trivial

end Yulang.GeneralRebaseDirectedCandidate268
