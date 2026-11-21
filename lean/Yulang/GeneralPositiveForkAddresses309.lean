import Yulang.GeneralCommittedReadAddress309
import Yulang.GeneralPositiveForkPackedMinimum309

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24500
set_option maxHeartbeats 14500000
namespace Yulang.GeneralPositiveForkAddresses309
open GeneralPositiveForkSource309 (registry compiled root)
open GeneralPositiveForkInstall309 (after)
open GeneralPositiveForkNodes309 (focus)
open GeneralPositiveForkCompiler309 (read decode)
open GeneralPositiveForkEvidence309 (payload)
open GeneralPositiveForkCertifiedTrace309 (exact_trace)
open GeneralPositiveForkCheck309 (read_root read_low read_high)
open GeneralCommittedReadAddress309 (cursor subtree subtrace here)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedEvidence231 (Certificate)
open GeneralDeclarationExamples (roles)
open GeneralNominalCenters (Plan)

theorem left_path : cursor read 0 [0] = some 1 ∧ subtree payload [0] = some (.node 2 []) := by
  constructor
  · simp [cursor,read_root]
  · rfl

theorem right_path : cursor read 0 [1] = some 2 ∧ subtree payload [1] = some (.node 3 []) := by
  constructor
  · simp [cursor,read_root]
  · rfl

theorem invalid_path : cursor read 0 [2] = none ∧ subtree payload [2] = none := by
  constructor
  · simp [cursor,read_root]
  · rfl

theorem left_proof (m : Assignment) (valid : Models after m) :
    ∃ p : Plan roles, Certificate compiled after.core m (focus .low) 2 [] p := by
  have addressed := subtrace (exact_trace m valid).1 left_path.1 left_path.2
  obtain ⟨_,e,_,⟨hit,p,cert⟩,_⟩ := here addressed
  have eq := Option.some.inj (hit.symm.trans read_low)
  subst e
  exact ⟨p,cert⟩

theorem right_proof (m : Assignment) (valid : Models after m) :
    ∃ p : Plan roles, Certificate compiled after.core m (focus .high) 3 [] p := by
  have addressed := subtrace (exact_trace m valid).1 right_path.1 right_path.2
  obtain ⟨_,e,_,⟨hit,p,cert⟩,_⟩ := here addressed
  have eq := Option.some.inj (hit.symm.trans read_high)
  subst e
  exact ⟨p,cert⟩

end Yulang.GeneralPositiveForkAddresses309
