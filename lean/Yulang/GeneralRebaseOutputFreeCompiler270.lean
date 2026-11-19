import Yulang.GeneralRebaseOutputFreeRegressions270
import Yulang.GeneralRebaseCompoundExecutable270

namespace Yulang.GeneralRebaseOutputFreeCompiler270
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralSourceState (Output)
open GeneralNominalCandidates (Context)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralRebaseNoOutputs270 (OutputFree terminalCode exact_code executable_stop)
open GeneralRebaseCompression266 (Basis)
open GeneralRebaseBehavior269 (code)
open GeneralRebaseStep258 (Fact)
open FiniteRankBehavior269 (Code)

def recognizes (registry : Registry) (root : Occurrence roles) : Bool :=
 root.demand.outputs.isEmpty &&
 registry.declarations.all (fun decl => decl.requirements.all (fun clause => clause.outputs.isEmpty))

theorem recognizes_exact (registry : Registry) (root : Occurrence roles) :
 recognizes registry root = true ↔ root.demand.outputs = [] ∧ OutputFree registry := by
 simp [recognizes,OutputFree,Bool.and_eq_true,List.all_eq_true,List.isEmpty_iff]

/-- An executable compiler for the exact canonical behavior on an
all-reachable source fragment. An unrecognized program is not terminal. -/
def compile (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output) : Option (Code (List Fact)) :=
 if recognizes registry root then some (terminalCode (Basis owners pool)) else none

theorem compiler_sound (registry : Registry) (context : Context) (root : Occurrence roles)
 (owners : List Nat) (pool : List Output)
 (path : B4Target.Steps (Step registry root) (GeneralNominalVersionedJournal232.initial context root) state)
 (result : compile registry root owners pool = some compiled) :
 code registry root owners pool state = compiled := by
 unfold compile at result
 split at result
 · rename_i supported
   obtain ⟨empty,quiet⟩ := (recognizes_exact registry root).mp supported
   cases Option.some.inj result
   exact exact_code registry context root quiet empty path owners pool
 · contradiction

theorem compiler_complete_on_fragment (registry : Registry) (root : Occurrence roles)
 (owners : List Nat) (pool : List Output) (quiet : OutputFree registry) (empty : root.demand.outputs = []) :
 compile registry root owners pool = some (terminalCode (Basis owners pool)) := by
 have flag := (recognizes_exact registry root).mpr ⟨empty,quiet⟩
 simp [compile,flag]

def run (registry : Registry) (root : Occurrence roles) (owners : List Nat) (pool : List Output)
 (fuel : Nat) : Option (Nat × Code (List Fact)) :=
 (compile registry root owners pool).map (FiniteBehaviorDriver269.drive fuel)

theorem run_exact (registry : Registry) (context : Context) (root : Occurrence roles)
 (owners : List Nat) (pool : List Output) (fuel : Nat)
 (path : B4Target.Steps (Step registry root) (GeneralNominalVersionedJournal232.initial context root) state)
 (result : run registry root owners pool fuel = some observed) :
 FiniteBehaviorDriver269.drive fuel (code registry root owners pool state) = observed := by
 unfold run at result
 cases compiled : compile registry root owners pool with
 | none => simp [compiled] at result
 | some key =>
   rw [compiler_sound registry context root owners pool path compiled]
   exact Option.some.inj (by simpa only [compiled,Option.map_some] using result)

theorem version239_recognized :
 recognizes GeneralDictionaryVersionLoopSource237.registry GeneralDictionaryVersionLoopSource237.root = true := by decide +kernel

theorem version240_recognized :
 recognizes GeneralDictionaryLooseLoopSource240.registry GeneralDictionaryLooseLoopSource240.root = true := by decide +kernel

theorem compound_not_claimed :
 compile GeneralDictionaryCompoundSource238.registry GeneralDictionaryJournalRefinement228Source.root
   GeneralRebaseSourceStrictFixture265.owners GeneralRebaseSourceStrictFixture265.pool = none := by decide +kernel

end Yulang.GeneralRebaseOutputFreeCompiler270
