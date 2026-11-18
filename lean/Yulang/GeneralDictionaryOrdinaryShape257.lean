import Yulang.GeneralDictionaryFullExpansion257
namespace Yulang.GeneralDictionaryOrdinaryShape257
open Core.PresenceGeneration PresenceNormalForm
open GeneralDictionaryLooseFamilyNames240 (lower upper)
open GeneralDictionaryLooseIterationBook240 (atoms packet)

def crossAtom (n : Nat) : Atom Nat := .tyLe (.var (lower n)) (.var 4)
def selfAtom : Atom Nat := .tyLe (.var 3) (.var 3)
def lowerAtoms (n : Nat) := GeneralNominalAllocation.equations (lower (n+1)) (.union (.var (lower n)) (.var (lower n)))
def upperAtoms (n : Nat) := GeneralNominalAllocation.equations (upper n) (.inter (.var 4) (.var 4))

theorem added_exact (n : Nat) : GeneralNominalVersionedInstallation231.atoms (packet n) =
 [crossAtom n,crossAtom n,crossAtom n,crossAtom n] ++
 (lowerAtoms n ++ upperAtoms n ++ (lowerAtoms n ++ upperAtoms n)) ++
 [selfAtom,selfAtom,crossAtom n,crossAtom n] := by
 unfold GeneralNominalVersionedInstallation231.atoms
 rw [GeneralDictionaryLooseFamilyPacket240.bindings_exact]
 have report : GeneralNominalPacketSupport.report (packet n) =
   GeneralDictionaryLooseFamilyPacket240.calculated n
     (GeneralDictionaryLooseIterationBook240.allocations n)
     (GeneralDictionaryLooseIterationBook240.reservations n) (atoms n) :=
   GeneralDictionaryLooseFamilyPacket240.report_exact ..
 rw [report]
 congr 1
 simp only [GeneralNominalRecursiveInspection.selfChecks,
   List.map_cons,List.map_nil]
 change [Atom.tyLe (.var (GeneralDictionaryLooseFamilyBase240.source n (GeneralDictionaryLooseFamilyBase240.original n 3))) (.var (GeneralDictionaryLooseFamilyBase240.source n (GeneralDictionaryLooseFamilyBase240.original n 3))),
   Atom.tyLe (.var (GeneralDictionaryLooseFamilyBase240.source n (GeneralDictionaryLooseFamilyBase240.original n 3))) (.var (GeneralDictionaryLooseFamilyBase240.source n (GeneralDictionaryLooseFamilyBase240.original n 3))),
   Atom.tyLe (.var (GeneralDictionaryLooseFamilyBase240.source n (GeneralDictionaryLooseFamilyBase240.anchor n))) (.var (GeneralDictionaryLooseFamilyBase240.source n (GeneralDictionaryLooseFamilyBase240.original n 4))),
   Atom.tyLe (.var (GeneralDictionaryLooseFamilyBase240.source n (GeneralDictionaryLooseFamilyBase240.anchor n))) (.var (GeneralDictionaryLooseFamilyBase240.source n (GeneralDictionaryLooseFamilyBase240.original n 4)))] = _
 rw [GeneralDictionaryLooseFamilyBase240.source_original,GeneralDictionaryLooseFamilyBase240.source_original,GeneralDictionaryLooseFamilyBase240.source_anchor]
 rfl

theorem atom_cases (n : Nat) (atom : Atom Nat) (member : atom ∈ atoms n) :
 ∃ index, index < n ∧
 (atom = crossAtom index ∨ atom = selfAtom ∨ atom ∈ lowerAtoms index ∨ atom ∈ upperAtoms index) := by
 induction n with
 | zero => cases member
 | succ n ih =>
   rw [GeneralDictionaryLooseIterationBook240.atoms_next] at member
   rcases List.mem_append.mp member with old | fresh
   · obtain ⟨i,before,kind⟩ := ih old
     exact ⟨i,by omega,kind⟩
   · refine ⟨n,by omega,?_⟩
     rw [added_exact] at fresh
     simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at fresh
     rcases fresh with ((same | same | same | same) | (lo | hi) | lo | hi) | same | same | same | same
     all_goals first | exact Or.inl same | exact Or.inr (Or.inl same) | exact Or.inr (Or.inr (Or.inl lo)) | exact Or.inr (Or.inr (Or.inr hi))

theorem length_atoms (n : Nat) : (atoms n).length = 16*n := by
 induction n with
 | zero => rfl
 | succ n ih =>
   rw [GeneralDictionaryLooseIterationBook240.atoms_next,added_exact]
   simp only [List.length_append,List.length_cons,List.length_nil,lowerAtoms,upperAtoms,GeneralNominalAllocation.equations,ih]
   omega
end Yulang.GeneralDictionaryOrdinaryShape257
