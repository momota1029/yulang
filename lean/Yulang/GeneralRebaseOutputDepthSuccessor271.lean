import Yulang.GeneralRebaseSourceStepDriver270
import Yulang.GeneralDictionaryOutputDepthInstall252

set_option maxRecDepth 25000
set_option maxHeartbeats 3000000
namespace Yulang.GeneralRebaseOutputDepthSuccessor271
open GeneralDictionaryOutputDepth252 (registry sourceRegistry declaration context interpretation root initial plan)
open GeneralDictionaryOutputDepthInstall252 (installed step)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralRebaseStep258 (Fact)
open GeneralRebaseCompression266 (Basis)
open GeneralRebaseBodyTable261 (schema)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseWeakProgress268 (Weak weak_source lull_same)
open GeneralRebaseMultiSelection263 (ofPlan requests)
open GeneralRebaseOneOutputProjection270 (basis_two remaining_cases)

def owner : Nat := GeneralNominalIdentities.pair root.identity declaration.id
def output : GeneralSourceState.Output := ⟨0,3⟩
abbrev support : List Fact := Basis [owner] [output]

theorem exact_schema (p : GeneralNominalCenters.Plan GeneralDictionaryOutputDepth252.roles)
 (reg : p.packet.registry = registry) (decl : p.packet.declaration = declaration)
 (interp : p.packet.context.interpretation = interpretation) :
 (schema p output).equations.length = 1 := by
 unfold schema
 rw [decl]
 change (GeneralNominalCenteredHeadMatEffects.bodySchema p 3
    (.explicit ⟨0,0,.app 0 [.app 0 [.var 0]]⟩)).equations.length = 1
 unfold GeneralNominalCenteredHeadMatEffects.bodySchema GeneralNominalCenteredHeadMatEffects.compileBody
 rw [reg,interp]
 rfl

theorem dichotomy (after : GeneralNominalVersionedJournal232.State GeneralDictionaryOutputDepth252.roles)
 (path : B4Target.Steps (Step registry root) initial after) :
 (project [owner] [output] after).remaining = [] ∨ (project [owner] [output] after).remaining = support := by
 apply remaining_cases
 intro p retained _
 have good := GeneralRebaseRetainedMetadata270.from_empty registry root _ _ rfl path p retained
 exact exact_schema p good.1 (List.mem_singleton.mp good.2.1) good.2.2

theorem initial_view : project [owner] [output] initial = GeneralRebaseStep258.initial support := by
 change GeneralRebaseStep258.write (GeneralRebaseStep258.initial support) [] = _
 exact GeneralRebaseWriteAlgebra259.empty _

theorem projected_install : (project [owner] [output] installed).remaining = [] := by decide +kernel

theorem source_weak : Weak registry root [owner] [output] initial installed := by
 refine ⟨initial,.refl,step,?_⟩
 intro equal
 have left := congrArg GeneralRebaseStep258.State.remaining equal
 rw [projected_install,initial_view] at left
 have no : [] ≠ support := by decide +kernel
 exact no left

theorem every_weak (target : GeneralNominalVersionedJournal232.State GeneralDictionaryOutputDepth252.roles)
 (genuine : Weak registry root [owner] [output] initial target) :
 (project [owner] [output] target).remaining = [] := by
 rcases dichotomy target (weak_source genuine) with clear | unchanged
 · exact clear
 · obtain ⟨before,silent,_,strict⟩ := genuine
   have same := congrArg GeneralRebaseStep258.State.remaining (lull_same silent)
   rw [initial_view] at same
   exfalso
   exact strict (GeneralRebaseStep258.state_ext _ _ (unchanged.trans same.symm))

def initialCode := GeneralRebaseSingleExitCode270.compile support support

theorem exact_code :
 GeneralRebaseBehavior269.code registry root [owner] [output] initial = initialCode := by
 have full := GeneralRebaseSingleExitCode270.exact_code registry root [owner] [output] initial
   ⟨installed,source_weak⟩ every_weak
 rw [initial_view] at full
 exact full

theorem computed :
 FiniteBehaviorDriver269.drive 2 initialCode = (1,.node [] []) := by rfl

def driveStep := GeneralRebaseSourceStepDriver270.next support (GeneralRebaseStep258.initial support)

theorem one_step : driveStep = some (GeneralRebaseStep258.done support) := rfl

theorem matches_genuine : driveStep = some (project [owner] [output] installed) := by
 rw [one_step]
 exact congrArg some (GeneralRebaseStep258.state_ext _ _ projected_install).symm

theorem bidirectional (target : GeneralRebaseStep258.State support) :
 GeneralRebaseStep258.Step (GeneralRebaseSourceStepDriver270.propose support)
   (project [owner] [output] initial) target ↔
 ∃ source, Weak registry root [owner] [output] initial source ∧ project [owner] [output] source = target := by
 rw [← GeneralRebaseSourceStepDriver270.next_exact,initial_view]
 change driveStep = some target ↔ _
 rw [one_step]
 constructor
 · intro same
   exact ⟨installed,source_weak,(GeneralRebaseStep258.state_ext _ _ projected_install).trans (Option.some.inj same)⟩
 · rintro ⟨previous,genuine,rfl⟩
   exact congrArg some (GeneralRebaseStep258.state_ext _ _ (every_weak previous genuine)).symm

theorem no_second_step (target : GeneralRebaseStep258.State support) :
 ¬ GeneralRebaseStep258.Step (GeneralRebaseSourceStepDriver270.propose support)
   (project [owner] [output] installed) target := by
 have settled : project [owner] [output] installed = GeneralRebaseStep258.done support :=
   GeneralRebaseStep258.state_ext _ _ projected_install
 rw [settled]
 exact GeneralRebaseSourceStepDriver270.terminal support target

end Yulang.GeneralRebaseOutputDepthSuccessor271
