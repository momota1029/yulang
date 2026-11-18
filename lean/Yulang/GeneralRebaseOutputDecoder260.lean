import Yulang.GeneralRebaseOutputKeys260
namespace Yulang.GeneralRebaseOutputDecoder260
open GeneralRebaseStep258
open GeneralNominalCenters

inductive Failure where
 | unhandledReport
 | untranslatedOutputs
 deriving DecidableEq, Repr

/-- Internal coverage diagnostics, not a language rejection. The equation
keys start after the two capture-binding obligations at indices0 and1. -/
def compile (plan : Plan roles) (owner : Nat)
 (atom : Fin plan.packet.context.state.base.slots → Option Nat) : Except Failure Proposal :=
 if (GeneralNominalVersionedPlans231.emittedSchema plan).unknown then .error .untranslatedOutputs
 else match GeneralRebaseFiniteReport259.compile owner atom (GeneralNominalPacketSupport.report plan.packet) with
 | none => .error .unhandledReport
 | some capture => .ok (capture ++ GeneralRebaseOutputKeys260.keys 2 (GeneralNominalVersionedPlans231.emittedSchema plan))

theorem translated (plan : Plan roles) (owner : Nat) (atom) (proposal : Proposal)
 (success : compile plan owner atom = .ok proposal) :
 (GeneralNominalVersionedPlans231.emittedSchema plan).unknown = false := by
 unfold compile at success
 split at success
 · cases success
 · rename_i known
   simpa only [Bool.not_eq_true] using known

theorem successful (plan : Plan roles) (owner : Nat) (atom) (proposal : Proposal) :
 compile plan owner atom = .ok proposal ↔
 (GeneralNominalVersionedPlans231.emittedSchema plan).unknown = false ∧
 ∃ capture, GeneralRebaseFiniteReport259.compile owner atom (GeneralNominalPacketSupport.report plan.packet) = some capture ∧
 proposal = capture ++ GeneralRebaseOutputKeys260.keys 2 (GeneralNominalVersionedPlans231.emittedSchema plan) := by
 unfold compile
 split
 · rename_i unknown
   constructor
   · intro impossible; cases impossible
   · rintro ⟨known,_⟩; simp_all
 · rename_i known
   have knownFalse : (GeneralNominalVersionedPlans231.emittedSchema plan).unknown = false := by
     simpa only [Bool.not_eq_true] using known
   split
   · rename_i missing
     constructor
     · intro impossible; cases impossible
     · rintro ⟨_,capture,found,_⟩; rw [missing] at found; cases found
   · rename_i capture found
     constructor
     · intro same; exact ⟨knownFalse,capture,found,(Except.ok.inj same).symm⟩
     · rintro ⟨_,other,otherFound,same⟩
       rw [found] at otherFound
       cases Option.some.inj otherFound
       rw [same]
end Yulang.GeneralRebaseOutputDecoder260
