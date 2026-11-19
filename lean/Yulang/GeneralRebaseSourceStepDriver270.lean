import Yulang.GeneralRebaseOutputFreeCompiler270
import Yulang.GeneralRebaseCompoundExecutable270

namespace Yulang.GeneralRebaseSourceStepDriver270
open GeneralRebaseStep258 (Fact State Observer Step initial done write tryWrite state_ext)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseCompression266 (Basis)
open GeneralRebaseWeakProgress268 (Weak)

def propose (basis : List Fact) (state : State basis) : List (List Fact) :=
 if state.remaining = basis then [basis] else []

def next (basis : List Fact) (state : State basis) : Option (State basis) :=
 (propose basis state).findSome? (tryWrite state)

theorem next_exact (basis : List Fact) (state target : State basis) :
 next basis state = some target ↔ Step (propose basis) state target := by
 by_cases full : state.remaining = basis
 · have listed : propose basis state = [basis] := by simp [propose,full]
   have reduce : next basis state = tryWrite state basis := by
     unfold next
     rw [listed]
     cases observed : tryWrite state basis <;> simp [observed]
   rw [reduce,GeneralRebaseStep258.tryWrite_exact]
   constructor
   · intro actual
     exact ⟨basis,listed.symm ▸ List.mem_singleton_self _,actual⟩
   · rintro ⟨candidate,member,correct,different⟩
     rw [listed] at member
     cases List.mem_singleton.mp member
     exact ⟨correct,different⟩
 · have absent : propose basis state = [] := by simp [propose,full]
   simp [next,Step,absent]

theorem drained (basis : List Fact) (source : State basis) : write source basis = done basis := by
 apply state_ext
 change source.remaining.filter (fun fact => !basis.contains fact) = []
 apply List.eq_nil_iff_forall_not_mem.mpr
 intro fact known
 have both := List.mem_filter.mp known
 rw [List.contains_iff_mem.mpr (source.canonical.subset both.1)] at both
 cases both.2

theorem terminal (basis : List Fact) (target : State basis) :
 ¬ Step (propose basis) (done basis) target := by
 rintro ⟨proposal,_,rfl,different⟩
 exact different rfl

namespace Compound
open GeneralDictionaryCompoundFrame238 (before installed)
open GeneralDictionaryCompoundSource238 (registry)
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralRebaseSourceStrictFixture265 (owners pool)
open GeneralRebaseCompoundProjection270 (all_weak_targets some_weak_target)
open GeneralRebaseCompoundExecutable270 (actualBasis actualBasis_exact)

abbrev support := Basis owners pool

def run := next actualBasis (initial actualBasis)

theorem computed_initial : project owners pool before = initial support :=
 GeneralRebaseSourceStrictFixture265.initial_projection

theorem computed : run = some (done actualBasis) := by
 unfold run
 apply (next_exact ..).mpr
 refine ⟨actualBasis,by simp [propose,initial],(drained ..).symm,?_⟩
 change [] ≠ actualBasis
 decide +kernel

theorem computed_on_source : next support (project owners pool before) = some (done support) := by
 rw [computed_initial]
 change next (Basis owners pool) (initial (Basis owners pool)) = some (done (Basis owners pool))
 rw [← actualBasis_exact]
 exact computed

theorem matches_concrete : next support (project owners pool before) = some (project owners pool installed) := by
 have eq := state_ext (project owners pool installed) (done support) (all_weak_targets installed some_weak_target)
 rw [computed_on_source,eq]

theorem exact_weak_targets (target : State support) :
 Step (propose support) (project owners pool before) target ↔
   ∃ concrete, Weak registry root owners pool before concrete ∧ project owners pool concrete = target := by
 rw [← next_exact,computed_on_source]
 constructor
 · intro same
   exact ⟨installed,some_weak_target,(state_ext _ _ (all_weak_targets installed some_weak_target)).trans (Option.some.inj same)⟩
 · rintro ⟨concrete,weak,rfl⟩
   exact congrArg some (state_ext _ _ (all_weak_targets concrete weak)).symm

theorem no_second (target : State support) :
 ¬ Step (propose support) (project owners pool installed) target := by
 have eq := state_ext (project owners pool installed) (done support) (all_weak_targets installed some_weak_target)
 rw [eq]
 exact terminal support target

end Compound

namespace OutputFree
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCandidates (Context)
open GeneralSourceState (Output)
open GeneralRebaseNoOutputs270 (fixed)

theorem no_original_weak (registry : Registry) (context : Context) (root : Occurrence roles)
 (accept : GeneralRebaseOutputFreeCompiler270.recognizes registry root = true)
 (path : B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root)
   (GeneralNominalVersionedJournal232.initial context root) living)
 (owners : List Nat) (pool : List Output) (target : GeneralNominalVersionedJournal232.State roles) :
 ¬ Weak registry root owners pool living target := by
 intro weak
 obtain ⟨empty,quiet⟩ := (GeneralRebaseOutputFreeCompiler270.recognizes_exact registry root).mp accept
 have left := fixed registry context root quiet empty path owners pool
 have right := fixed registry context root quiet empty
   (GeneralRebaseWeakTerminal268.append path (GeneralRebaseWeakProgress268.weak_source weak)) owners pool
 have less := GeneralRebaseWeakProgress268.decrease weak
 rw [left,right] at less
 exact (Nat.lt_irrefl _) less

theorem exact_empty_observer (registry : Registry) (context : Context) (root : Occurrence roles)
 (accept : GeneralRebaseOutputFreeCompiler270.recognizes registry root = true)
 (path : B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root)
   (GeneralNominalVersionedJournal232.initial context root) living)
 (owners : List Nat) (pool : List Output) (target : State (Basis owners pool)) :
 Step (fun _ => []) (project owners pool living) target ↔
   ∃ concrete, Weak registry root owners pool living concrete ∧ project owners pool concrete = target := by
 constructor
 · rintro ⟨_,notListed,_⟩
   cases notListed
 · rintro ⟨concrete,weak,_⟩
   exact False.elim (no_original_weak registry context root accept path owners pool concrete weak)

end OutputFree

end Yulang.GeneralRebaseSourceStepDriver270
