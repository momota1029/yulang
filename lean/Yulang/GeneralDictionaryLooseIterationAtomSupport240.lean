import Yulang.GeneralDictionaryLooseFamilyInstallation240
import Yulang.GeneralDictionaryLooseFamilyFresh240
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryLooseIterationAtomSupport240
open GeneralDictionaryLooseFamilyPacket240
open GeneralDictionaryLooseFamilyBase240
open GeneralDictionaryLooseFamilySnapshot240
open GeneralDictionaryLooseFamilyNames240 (lower upper repeated)
open GeneralDictionaryLooseLoopSource240 (declaration registry root)
open GeneralNominalState (atomSources typeSources)
variable (n : Nat) (allocated : List GeneralNominalIdentities.Origin)
 (reserved : List Nat) (ordinary : List (PresenceNormalForm.Atom Nat))

theorem checks : GeneralNominalRecursiveInspection.selfChecks
 (snapshot n allocated reserved ordinary) (GeneralNominalPacketSupport.report (packet n allocated reserved ordinary)) =
 [.tyLe (.var 3) (.var 3),.tyLe (.var 3) (.var 3),
  .tyLe (.var (lower n)) (.var 4),.tyLe (.var (lower n)) (.var 4)] := by
 change GeneralNominalRecursiveInspection.selfChecks _
   (GeneralNominalRecursiveCandidates.report (context n allocated reserved ordinary) declaration [(original n 3,original n 3)]) = _
 rw [report_exact]
 simp only [GeneralNominalRecursiveInspection.selfChecks,List.map_cons,List.map_nil]
 change _ = _
 rw [source_original,source_anchor]
 rfl

theorem atom_sources : (GeneralNominalVersionedInstallation231.atoms (packet n allocated reserved ordinary)).flatMap atomSources ⊆
 [3,4,lower n,lower (n+1),upper n] := by
 unfold GeneralNominalVersionedInstallation231.atoms
 rw [bindings_exact,checks]
 change ((GeneralNominalAllocation.cross (repeated (lower n)) ++
  GeneralNominalAllocation.equations (lower (n+1)) (.union (.var (lower n)) (.var (lower n))) ++
  GeneralNominalAllocation.equations (upper n) (.inter (.var 4) (.var 4)) ++
  (GeneralNominalAllocation.equations (lower (n+1)) (.union (.var (lower n)) (.var (lower n))) ++
  GeneralNominalAllocation.equations (upper n) (.inter (.var 4) (.var 4)))) ++
  _).flatMap atomSources ⊆ _
 simp only [GeneralNominalAllocation.cross,repeated,GeneralNominalAllocation.equations,
  List.flatMap_cons,List.flatMap_nil,List.cons_append,List.nil_append,List.append_nil,
  atomSources,typeSources,ite_true]
 intro x member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢
 omega
end Yulang.GeneralDictionaryLooseIterationAtomSupport240
