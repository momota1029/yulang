import Yulang.GeneralSharedNamedCurrent310
import Yulang.GeneralNominalRepeatedLocal190
import Yulang.GeneralNominalSemanticRawFrame236

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralSharedNamedModelSeparation310
open GeneralSharedNamedPlan310 (z)
open GeneralSharedNamedSource310 (root initial)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalExamples (context state model state_models)
open GeneralDeclarationExamples (roles)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalSemanticRawFrame236 (sources source_models_same)

def different : Assignment := fun name =>
  if name = z then (.base .bool, (model name).2) else model name

theorem z_fresh_raw : z ∉ sources (state true) := by decide +kernel

theorem public_same :
    ∀ source ∈ sources (state true), model source = different source := by
  intro source member
  have neo : source ≠ z := fun same => z_fresh_raw (same ▸ member)
  simp only [different,ite_eq_right neo]

theorem initial_ok : Models initial different :=
  (GeneralNominalVersionedJournal232.initial_models ..).mpr
    ⟨(source_models_same (state true) public_same).mp (state_models true),
      GeneralNominalCenters.point_root_holds _ _ (fun _ => rfl) _⟩

theorem different_values : ¬ Equivalent (different 1).1 (different z).1 := by
  have separate : (1 : Nat) ≠ z := by decide +kernel
  change ¬ Equivalent (if (1 : Nat) = z then (.base .bool, (model 1).2) else model 1).1
    (if z = z then (.base .bool, (model z).2) else model z).1
  simp only [ite_eq_right separate]
  intro eq
  exact GeneralNominalRepeatedLocal190.bool_not_below_int eq.2

theorem cannot_use_before_model : ¬ Models GeneralSharedNamedInstall310.after different :=
  fun valid => different_values (GeneralSharedNamedInstall310.installed_equality _ valid)

theorem live_model_strict :
    (∃ m, Models initial m ∧ ¬ Models GeneralSharedNamedInstall310.after m) ∧
    (∃ m, Models GeneralSharedNamedMerge310.merged m) :=
  ⟨⟨different,initial_ok,cannot_use_before_model⟩,⟨_,GeneralSharedNamedMerge310.inhabited⟩⟩

end Yulang.GeneralSharedNamedModelSeparation310
