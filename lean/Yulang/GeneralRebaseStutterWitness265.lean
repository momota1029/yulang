import Yulang.GeneralRebaseSourceProjection264

namespace Yulang.GeneralRebaseStutterWitness265
open GeneralRebaseLiveProjection264 (SourceState project liveFacts)
open GeneralRebaseStep258 (Fact)
open GeneralSourceState (Output)

/-- Projection retains exactly basis facts not in the source's live slice. -/
theorem remaining_iff (owners : List Nat) (pool : List Output) (source : SourceState roles)
 (fact : Fact) : fact ∈ (project owners pool source).remaining ↔
 fact ∈ GeneralRebaseUniversalBasis263.basis owners pool ∧ fact ∉ liveFacts source := by
 change fact ∈ (GeneralRebaseUniversalBasis263.basis owners pool).filter _ ↔ _
 simp

/-- An actual path changes the fixed projection iff it introduces a live fact
that was absent initially and belongs to the fixed basis. -/
theorem steps_change_iff (owners : List Nat) (pool : List Output)
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {first last : SourceState roles}
 (steps : B4Target.Steps (GeneralNominalVersionedMixedKernel234.Step registry root) first last) :
 project owners pool last ≠ project owners pool first ↔
 ∃ fact ∈ GeneralRebaseUniversalBasis263.basis owners pool,
   fact ∉ liveFacts first ∧ fact ∈ liveFacts last := by
 classical
 rw [GeneralRebaseSourceProjection264.steps_square owners pool steps, ne_eq,
   GeneralRebaseWriteAlgebra259.fixed_iff]
 constructor
 · intro changed
   by_cases witness : ∃ fact ∈ GeneralRebaseUniversalBasis263.basis owners pool,
     fact ∉ liveFacts first ∧ fact ∈ liveFacts last
   · exact witness
   · exfalso
     apply changed
     intro fact member later
     obtain ⟨within,old⟩ := (remaining_iff owners pool first fact).mp member
     exact witness ⟨fact,within,old,later⟩
 · rintro ⟨fact,within,old,later⟩ exactStutter
   exact exactStutter fact ((remaining_iff owners pool first fact).mpr ⟨within,old⟩) later

end Yulang.GeneralRebaseStutterWitness265
