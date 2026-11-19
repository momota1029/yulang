import Yulang.GeneralRebaseSameInputs269
import Yulang.GeneralRebaseMergeScan267

namespace Yulang.GeneralRebaseMergeJournal269
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalCenters (Site SameInputs)
open GeneralRebaseJournalInequalities269 (Between)
open GeneralRebaseSameInputs269 (probe probe_sound)
open GeneralRebasePartialBool268 (Answer Reflect)
open GeneralRebaseMergeScan267 (scan linkedPairs scan_exact source_step)
open GeneralSourceDictionaries (Occurrence)
open GeneralDeclarations (Registry)
open GeneralNominalVersionedAdministrative232 (merge)

def candidates (state : State roles) (fallback : Nat → Nat → Answer) (first last : Site roles) : Bool :=
 probe state fallback first last == some true

theorem sound (state : State roles) (fallback : Nat → Nat → Answer)
 (cert : ∀ a b, Reflect (Between state a b) (fallback a b)) (first last : Site roles)
 (yes : candidates state fallback first last = true) : SameInputs (Models state) first last := by
 have h := probe_sound state fallback cert first last
 rw [show probe state fallback first last = some true by exact beq_iff_eq.mp yes] at h
 exact h

theorem known_exact (state : State roles) (fallback : Nat → Nat → Answer)
 (cert : ∀ a b, Reflect (Between state a b) (fallback a b)) (first last : Site roles)
 (known : probe state fallback first last ≠ none) :
 candidates state fallback first last = true ↔ SameInputs (Models state) first last := by
 refine ⟨sound state fallback cert first last,?_⟩
 intro matching
 have h := probe_sound state fallback cert first last
 cases result : probe state fallback first last with
 | none => exact False.elim (known result)
 | some bit =>
   rw [result] at h
   cases bit
   · exact False.elim (h matching)
   · simp [candidates,result]

theorem scan_sound (registry : Registry) (state : State roles) (root : Occurrence roles)
 (fallback : Nat → Nat → Answer) (cert : ∀ a b, Reflect (Between state a b) (fallback a b))
 (first last : Site roles) (listed : (first,last) ∈ scan state root (candidates state fallback)) :
 GeneralNominalVersionedMixedKernel234.Step registry root state (merge state first last) :=
 source_step registry state root _ first last listed (sound state fallback cert first last)

theorem scan_iff (state : State roles) (root : Occurrence roles)
 (fallback : Nat → Nat → Answer) (cert : ∀ a b, Reflect (Between state a b) (fallback a b))
 (first last : Site roles)
 (known : (first,last) ∈ linkedPairs state root → probe state fallback first last ≠ none) :
 (first,last) ∈ scan state root (candidates state fallback) ↔
 (first,last) ∈ linkedPairs state root ∧ SameInputs (Models state) first last := by
 rw [scan_exact]
 constructor
 · rintro ⟨pair,proof⟩
   exact ⟨pair,proof.elim (GeneralRebaseMergeCenters267.source_sound (Models state) first last)
     (sound state fallback cert first last)⟩
 · rintro ⟨pair,matching⟩
   exact ⟨pair,Or.inr ((known_exact state fallback cert first last (known pair)).mpr matching)⟩

end Yulang.GeneralRebaseMergeJournal269
