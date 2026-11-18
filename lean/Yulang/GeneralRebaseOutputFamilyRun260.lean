import Yulang.GeneralRebaseOutputFamily260
namespace Yulang.GeneralRebaseOutputFamilyRun260
open GeneralRebaseStep258
open GeneralRebaseOutputFamily260 (Layout basis)
open GeneralRebaseOwnedOutputKeys260 (keys)

def proposals (owners : List Nat) (layout : Layout) : List Proposal := owners.map fun owner => keys owner (layout owner)
def observe (owners : List Nat) (layout : Layout) : Observer (basis owners layout) := fun _ => proposals owners layout

theorem closed (owners : List Nat) (layout : Layout) : GeneralRebaseClosedObserver259.Closed (observe owners layout) := by
 intro state proposal member
 obtain ⟨owner,included,rfl⟩ := List.mem_map.mp member
 exact GeneralRebaseOutputFamily260.proposal_closed owners layout owner included

theorem flattened (owners : List Nat) (layout : Layout) : (proposals owners layout).flatten = basis owners layout := by
 simp [proposals,basis,List.flatMap]

theorem batch_initial (owners : List Nat) (layout : Layout) :
 GeneralRebaseWriteAlgebra259.batch (initial (basis owners layout)) (proposals owners layout) = done (basis owners layout) := by
 rw [GeneralRebaseWriteAlgebra259.batch_exact,flattened]
 apply state_ext
 simp [write,initial,done]

theorem settle_initial (owners : List Nat) (layout : Layout) :
 GeneralRebaseSettle259.settle (observe owners layout) (initial (basis owners layout)) = .ok (done (basis owners layout)) := by
 have result := GeneralRebaseBatchTerminal259.settle_batch (initial (basis owners layout)) (proposals owners layout)
   (closed owners layout (initial (basis owners layout)))
 rw [batch_initial] at result
 exact result

def untranslated (owners : List Nat) (layout : Layout) : List Nat := owners.filter fun owner => (layout owner).unknown

/-- Computes a finite constraint state, not a satisfying assignment or a
language acceptance decision. Unknown translations are explicitly separate. -/
def finish (owners : List Nat) (layout : Layout) : Except (List Nat) (State (basis owners layout)) :=
 if untranslated owners layout = [] then .ok (done (basis owners layout))
 else .error (untranslated owners layout)

theorem translated_iff (owners : List Nat) (layout : Layout) :
 untranslated owners layout = [] ↔ ∀ owner ∈ owners, (layout owner).unknown = false := by
 simp [untranslated,List.filter_eq_nil_iff]

theorem finish_exact (owners : List Nat) (layout : Layout) :
 finish owners layout = .ok (done (basis owners layout)) ↔
 ∀ owner ∈ owners, (layout owner).unknown = false := by
 unfold finish
 split
 · rename_i known
   exact ⟨fun _ => (translated_iff owners layout).mp known,fun _ => rfl⟩
 · rename_i unknown
   constructor
   · intro impossible; cases impossible
   · intro all; exact False.elim (unknown ((translated_iff owners layout).mpr all))

theorem finish_settle (owners : List Nat) (layout : Layout)
 (known : ∀ owner ∈ owners, (layout owner).unknown = false) :
 ∃ final, finish owners layout = .ok final ∧
 GeneralRebaseSettle259.settle (observe owners layout) (initial (basis owners layout)) = .ok final :=
 ⟨done _,(finish_exact ..).mpr known,settle_initial owners layout⟩
end Yulang.GeneralRebaseOutputFamilyRun260
