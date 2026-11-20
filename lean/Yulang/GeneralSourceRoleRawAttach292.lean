import Yulang.GeneralSourceRoleActualAttach292
import Yulang.GeneralSourceMetadataPublicationFixture291

/-! Exact role/registry attachment permits reusing the existing raw fixture.
No additional path, state, certificate, or installed relation is inferred. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralSourceRoleRawAttach292
open GeneralRebaseRowChildSource287 (roles registry before root)
open GeneralRebaseRowParentFrame287 (after)
open GeneralRebaseRowParentPacket287 (child)
open GeneralSourceRoleAttach292 (compose)
open GeneralSourceRoleActualAttach292 (suppliedEnv attachInput exact_actual_bundle)
open GeneralSourceMetadataBundle291 (SourceBundle Attached inspect)
open GeneralSourceMetadataBundleFixture291 (attached_actual)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralRebaseReceiptWitness289 (ActualPath)
open GeneralNominalVersionedJournal232 (State)
open GeneralObservedMetadataSeal290 (Seal)
open GeneralRebaseReceiptCompile289 (Mark actualMark)
open GeneralObservedMetadataReleaseFixture290 (normalized)

theorem exact_registry_readback (branch : Bool) (bundle : SourceBundle)
    (built : compose suppliedEnv (attachInput branch) = some bundle) :
    GeneralSourceMetadataBundle291.registry bundle = registry branch := by
  have exactBundle := Option.some.inj (built.symm.trans (exact_actual_bundle branch))
  subst bundle
  exact GeneralSourceMetadataBundle291.actual_registry (attached_actual branch)

theorem same_existing_step (branch : Bool) (bundle : SourceBundle)
    (built : compose suppliedEnv (attachInput branch) = some bundle) :
    Step (GeneralSourceMetadataBundle291.registry bundle) root before (after branch) := by
  rw [exact_registry_readback branch bundle built]
  exact GeneralRebaseRowParentStep287.actual_step branch

theorem same_existing_strict_release (branch : Bool) (bundle : SourceBundle)
    (built : compose suppliedEnv (attachInput branch) = some bundle) {s : State roles}
    (path : ActualPath branch s) (receiptToken : Seal) (mark : Mark) :
    GeneralSourceMetadataPublication291.publish (GeneralSourceMetadataBundle291.registry bundle)
      s root (child branch) (GeneralRebaseReceiptFixture289.request branch)
      (GeneralSourceMetadataRows291.interpretation bundle.snapshot) receiptToken = .released mark ↔
        branch = true ∧ s = after true ∧ receiptToken = normalized ∧ mark = actualMark := by
  have exactBundle := Option.some.inj (built.symm.trans (exact_actual_bundle branch))
  rw [exact_registry_readback branch bundle built,exactBundle]
  exact GeneralSourceMetadataPublicationFixture291.checked_source_release branch path receiptToken mark

theorem global_readiness_does_not_gate_actual_step :
    ∃ bundle, compose suppliedEnv (attachInput false) = some bundle ∧
      (inspect bundle).ready = false ∧
      Step (GeneralSourceMetadataBundle291.registry bundle) root before (after false) := by
  refine ⟨_,exact_actual_bundle false,GeneralSourceMetadataBundleFixture291.executable_both false,?_⟩
  exact same_existing_step false _ (exact_actual_bundle false)

end Yulang.GeneralSourceRoleRawAttach292
