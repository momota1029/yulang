import Yulang.GeneralDictionaryLooseIterationIteration240
import Yulang.GeneralDictionaryLooseFamilyInstallation240
import Yulang.GeneralNominalFrameAggregate256
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryReachableAggregate256
open GeneralDictionaryLooseLoopSource240 (roles registry root)
open GeneralDictionaryLooseIterationBook240 (atoms packet plan)
open GeneralDictionaryLooseFamilyNames240 (lower)
open GeneralDictionaryLooseIterationIteration240 (state stages)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open Core.PresenceGeneration

/-- The actual replay retains every earlier atom. -/
theorem old_atoms (n : Nat) : atoms n ⊆ atoms (n+1) := by
 rw [GeneralDictionaryLooseIterationBook240.atoms_next]
 exact List.subset_append_left ..

theorem lower_equations (n : Nat) :
 GeneralNominalAllocation.equations (lower (n+1)) (.union (.var (lower n)) (.var (lower n))) ⊆ atoms (n+1) := by
 exact GeneralDictionaryLooseFamilyInstallation240.replay_lower n _ _ _

/-- All models of the retained actual equation history identify this lower
endpoint with initial source 2, up to semantic equivalence. -/
theorem lower_value (n : Nat) (assignment : Assignment)
 (valid : PresenceNormalForm.All model assignment (atoms n)) :
 Equivalent (assignment (lower n)).1 (assignment 2).1 := by
 induction n with
 | zero => exact ⟨subtype_refl _,subtype_refl _⟩
 | succ n ih =>
   have before := ih (fun atom member => valid atom (old_atoms n member))
   have equation := (GeneralNominalCaptureMerges.equations_exact ..).mp
     (fun atom member => valid atom (lower_equations n member))
   change Equivalent (assignment (lower (n+1))).1 (.union (assignment (lower n)).1 (assignment (lower n)).1) at equation
   have joined := GeneralPresenceSnapshotGrowth251.union_self (assignment (lower n)).1
   exact ⟨subtype_trans equation.1 (subtype_trans joined.1 before.1),
     subtype_trans before.2 (subtype_trans joined.2 equation.2)⟩

theorem current_atoms (n : Nat) (assignment : Assignment)
 (valid : GeneralNominalVersionedJournal232.Models (state n) assignment) :
 PresenceNormalForm.All model assignment (atoms n) := by
 have current := valid.1.1
 rw [(stages n).shape.current] at current
 exact current.2.2

theorem source_lower (n : Nat) (assignment : Assignment)
 (valid : GeneralNominalVersionedJournal232.Models (state n) assignment) :
 Equivalent (assignment (lower n)).1 (assignment 2).1 :=
 lower_value n assignment (current_atoms n assignment valid)

def representative : GeneralNominalRebaseProjectionView243.Bounds := ⟨.var 2,.var 4⟩

theorem pairs_exact (n : Nat) :
 GeneralNominalFrameAggregate256.pairs (plan n) 0 = [(lower n,4),(lower n,4)] := by
 unfold GeneralNominalFrameAggregate256.pairs
 rw [GeneralDictionaryLooseFamilyPacket240.bindings_exact]
 rfl

theorem frame (n : Nat) :
 GeneralNominalVersionedEvidence231.Frame registry (state n).core root 0 (plan n) :=
 GeneralDictionaryLooseIterationFrame240.frame (stages n).shape (GeneralDictionaryLooseIterationFresh240.fresh n)

/-- This uses every stage model's actual retained equations. It is not a
claim that the original endpoints are identical under arbitrary assignments. -/
theorem fits_exact (n : Nat) (assignment : Assignment)
 (valid : GeneralNominalVersionedJournal232.Models (state n) assignment) (actual : Ty) :
 representative.Fits assignment actual ↔
 ∀ pair ∈ GeneralNominalFrameAggregate256.pairs (plan n) 0,
   GeneralNominalCaptureMerges.Fits assignment pair actual := by
 rw [pairs_exact]
 have same := source_lower n assignment valid
 constructor
 · intro fits pair member
   have equal : pair = (lower n,4) := by simpa only [List.mem_cons,List.not_mem_nil,or_false,or_self] using member
   subst pair
   exact ⟨subtype_trans same.1 fits.1,fits.2⟩
 · intro fits
   have first := fits (lower n,4) (List.mem_cons_self ..)
   exact ⟨subtype_trans same.2 first.1,first.2⟩

theorem reachable_all (n : Nat) : B4TargetV8.Reachable
 (GeneralNominalPointSourceBoundary240.boundary roles) GeneralDictionaryLooseLoopSource240.sourceRegistry root (state n) :=
 GeneralDictionaryLooseIterationIteration240.reachable n
end Yulang.GeneralDictionaryReachableAggregate256
