import Yulang.GeneralRebaseCompression266
import Yulang.GeneralRebaseFiniteStates263

namespace Yulang.GeneralRebaseProjectionObserver266
open GeneralRebaseStep258
open GeneralRebaseCompression266 (Basis)
open GeneralRebaseLiveProjection264 (SourceState project liveFacts)
open GeneralSourceState (Output)
variable {basis : List Fact}

/-- Re-encode a write by its resulting present facts. This also handles
a basis with duplicate entries, because write removes every matching copy. -/
theorem write_present (before : State basis) (proposal : Proposal) :
 write before (present (write before proposal)) = write before proposal := by
 apply state_ext
 change before.remaining.filter _ = before.remaining.filter _
 apply List.filter_congr
 intro fact prior
 have inside := before.canonical.subset prior
 have kept : fact ∈ (write before proposal).remaining ↔ fact ∉ proposal := by
   change fact ∈ before.remaining.filter _ ↔ _
   simp [prior]
 have recorded : fact ∈ present (write before proposal) ↔ fact ∈ proposal := by
   rw [GeneralRebaseFactSemantics259.present_iff, kept]
   simp [inside]
 apply congrArg Bool.not
 exact Bool.eq_iff_iff.mpr (by simpa using recorded)

def Witness (owners : List Nat) (pool : List Output)
 (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
 (first last : State (Basis owners pool)) : Prop :=
 ∃ before after : SourceState roles,
 GeneralNominalVersionedMixedKernel234.Step registry root before after ∧
 project owners pool before = first ∧ project owners pool after = last

/-- A mathematical finite specification observer, not executable source
discovery. Classical filtering asks whether source witnesses exist. -/
noncomputable def observe (owners : List Nat) (pool : List Output)
 (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
 (first : State (Basis owners pool)) : List Proposal := by
 classical
 exact ((GeneralRebaseFiniteStates263.states (Basis owners pool)).filter fun last =>
   decide (Witness owners pool registry root first last ∧ last ≠ first)).map present

theorem observe_mem (owners : List Nat) (pool : List Output)
 (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
 (first : State (Basis owners pool)) (proposal : Proposal) :
 proposal ∈ observe owners pool registry root first ↔
 ∃ last, Witness owners pool registry root first last ∧ last ≠ first ∧ present last = proposal := by
 classical
 unfold observe
 simp only [List.mem_map,List.mem_filter,decide_eq_true_eq]
 constructor
 · rintro ⟨last,⟨_,edge,different⟩,equal⟩
   exact ⟨last,edge,different,equal⟩
 · rintro ⟨last,edge,different,equal⟩
   exact ⟨last,⟨GeneralRebaseFiniteStates263.complete _ last,edge,different⟩,equal⟩

theorem witness_write (owners : List Nat) (pool : List Output)
 {registry : GeneralDeclarations.Registry} {root : GeneralSourceDictionaries.Occurrence roles}
 {first last : State (Basis owners pool)}
 (witness : Witness owners pool registry root first last) : write first (present last) = last := by
 obtain ⟨before,after,step,rfl,rfl⟩ := witness
 rw [GeneralRebaseSourceProjection264.step_square owners pool step]
 exact write_present _ _

/-- Exact one-edge correspondence. It does not assert that witnesses
of adjacent finite edges share the same concrete source representative. -/
theorem step_exact (owners : List Nat) (pool : List Output)
 (registry : GeneralDeclarations.Registry) (root : GeneralSourceDictionaries.Occurrence roles)
 (first last : State (Basis owners pool)) :
 Step (observe owners pool registry root) first last ↔
 Witness owners pool registry root first last ∧ last ≠ first := by
 constructor
 · rintro ⟨proposal,found,equal,_⟩
   obtain ⟨candidate,witness,different,rfl⟩ := (observe_mem owners pool registry root first proposal).mp found
   rw [witness_write owners pool witness] at equal
   cases equal
   exact ⟨witness,different⟩
 · rintro ⟨witness,different⟩
   refine ⟨present last,(observe_mem owners pool registry root first _).mpr ⟨last,witness,different,rfl⟩,
     (witness_write owners pool witness).symm,?_⟩
   exact fun same => different (state_ext _ _ same)

end Yulang.GeneralRebaseProjectionObserver266
