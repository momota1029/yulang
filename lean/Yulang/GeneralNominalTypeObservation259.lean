import Yulang.GeneralDictionaryRebaseRun259
namespace Yulang.GeneralNominalTypeObservation259
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection

theorem observes (first last : Assignment) (same : ∀ name, (first name).1 = (last name).1)
 (seen : Observes first origin value) : Observes last origin value := by
 induction seen with
 | source identity => rw [same identity]; exact .source identity
 | nominal _ equal found ih => exact .nominal ih equal found
 | structural _ length equal found ih => exact .structural ih length equal found

theorem observes_iff (first last : Assignment) (same : ∀ name, (first name).1 = (last name).1) :
 Observes first origin value ↔ Observes last origin value :=
 ⟨observes first last same,observes last first (fun n => (same n).symm)⟩
end Yulang.GeneralNominalTypeObservation259
