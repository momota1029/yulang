import Yulang.GeneralNominalRebasePublicModel242
import Yulang.GeneralNominalRebaseRawView243
import Yulang.GeneralPresenceOrderedSubstitution247
import Yulang.GeneralPresenceCommonLaws245
namespace Yulang.GeneralNominalOrderedRawPublic256
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244 (Entry block)
open GeneralPresenceOrderedSubstitution247 (mapping)
open GeneralPresenceOrderedBlock247 (solve)
open GeneralNominalRebaseRawView243 (compile read)
open GeneralNominalRebasePublicModel242 (PublicAgree)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

theorem compiled_solved (raw : GeneralNominalState.State) (entries : List (Entry Nat))
 (assignment : Assignment) :
 (compile raw (mapping entries)).Models assignment ↔
 GeneralNominalState.Models raw (solve model entries assignment) := by
 rw [GeneralNominalRebaseRawView243.compile_exact]
 have same : read (mapping entries) assignment = solve model entries assignment :=
   funext (GeneralPresenceOrderedSubstitution247.mapping_eval entries model assignment)
 rw [same]

/-- Recovery at the same assignment uses satisfied equations, not a fresh
block solvability claim and not an assumed whole-state implication. -/
theorem recovered (raw : GeneralNominalState.State) (entries : List (Entry Nat))
 (assignment : Assignment) (valid : PresenceNormalForm.All model assignment (block entries)) :
 (compile raw (mapping entries)).Models assignment ↔ GeneralNominalState.Models raw assignment :=
 (compiled_solved raw entries assignment).trans
   (GeneralNominalRawCongruence238.models_iff raw
     (GeneralPresenceOrderedRecovery247.solve_compatible model GeneralPresenceCommonLaws245.common_laws entries assignment valid))

theorem solve_public (entries : List (Entry Nat)) (hidden : List Nat)
 (privateTargets : ∀ entry ∈ entries, entry.1 ∈ hidden)
 (assignment boundary : Assignment) (agrees : PublicAgree hidden assignment boundary) :
 PublicAgree hidden (solve model entries assignment) boundary := by
 constructor
 · intro name outside
   have unchanged : solve model entries assignment name = assignment name := by
     apply GeneralPresenceOrderedBlock247.solve_outside
     intro entry member same
     exact outside (same ▸ privateTargets entry member)
   exact unchanged.trans (agrees.1 name outside)
 · intro name
   exact (GeneralPresenceOrderedBlock247.solve_rows model entries assignment name).trans (agrees.2 name)

/-- Ordered elimination of actual retained definitions preserves the complete
public model projection, including all rows. It does not replace that block
with fresh equations or prove a finite syntax invariant. -/
theorem public_models (raw : GeneralNominalState.State) (entries : List (Entry Nat))
 (included : block entries ⊆ raw.ordinary) (hidden : List Nat)
 (privateTargets : ∀ entry ∈ entries, entry.1 ∈ hidden) (boundary : Assignment) :
 (∃ assignment, PublicAgree hidden assignment boundary ∧ GeneralNominalState.Models raw assignment) ↔
 (∃ assignment, PublicAgree hidden assignment boundary ∧ (compile raw (mapping entries)).Models assignment) := by
 constructor
 · rintro ⟨assignment,agrees,valid⟩
   have equations : PresenceNormalForm.All model assignment (block entries) :=
     fun atom member => valid.2.2 atom (included member)
   exact ⟨assignment,agrees,(recovered raw entries assignment equations).mpr valid⟩
 · rintro ⟨assignment,agrees,valid⟩
   exact ⟨solve model entries assignment,solve_public entries hidden privateTargets assignment boundary agrees,
     (compiled_solved raw entries assignment).mp valid⟩
end Yulang.GeneralNominalOrderedRawPublic256
