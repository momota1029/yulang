import Yulang.GeneralNominalTemplateChoices255
import Yulang.GeneralDictionaryDefaultExpression209
namespace Yulang.GeneralNominalTemplateCongruence255
open GeneralNominalTemplateChoices255 (Raw reads readsMany)
open GeneralNominalMaterialization (Mode)
open GeneralNominalCenteredHeadMatExpressions (value values)
open CommonNominalFullCarrier
open CommonRoleOutermostResolver (All₂)
open GeneralDictionaryDefaultExpression209 (primitive_equivalent nominal_equivalent)

mutual
 theorem value_equivalent (first last : Mode → Nat → Ty) (mode : Mode) (term : Raw)
 (agree : ∀ entry ∈ reads mode term, Equivalent (first entry.1 entry.2) (last entry.1 entry.2)) :
 Equivalent (value first mode term) (value last mode term) := by
 cases term with
 | «variable» name => exact agree (mode,name) (List.mem_singleton_self _)
 | primitive constructor arguments => exact primitive_equivalent constructor (values_equivalent first last mode arguments agree)
 | nominal name arguments => exact nominal_equivalent name (values_equivalent first last .actual arguments agree)
 | record label payload tail =>
   have one := value_equivalent first last mode payload (fun entry member => agree entry (List.mem_append_left _ member))
   have two := value_equivalent first last mode tail (fun entry member => agree entry (List.mem_append_right _ member))
   exact ⟨common_record_mono label one.1 two.1,common_record_mono label one.2 two.2⟩
 | variant tag payload =>
   have one := value_equivalent first last mode payload agree
   exact ⟨(common_variant_iff tag ..).mpr one.1,(common_variant_iff tag ..).mpr one.2⟩
 | join a b =>
   have one := value_equivalent first last mode a (fun entry member => agree entry (List.mem_append_left _ member))
   have two := value_equivalent first last mode b (fun entry member => agree entry (List.mem_append_right _ member))
   exact ⟨common_union_mono one.1 two.1,common_union_mono one.2 two.2⟩
 theorem values_equivalent (first last : Mode → Nat → Ty) (mode : Mode) (terms : List Raw)
 (agree : ∀ entry ∈ readsMany mode terms, Equivalent (first entry.1 entry.2) (last entry.1 entry.2)) :
 All₂ Equivalent (values first mode terms) (values last mode terms) := by
 cases terms with
 | nil => exact .nil
 | cons head rest =>
   exact .cons (value_equivalent first last mode head (fun entry member => agree entry (List.mem_append_left _ member)))
     (values_equivalent first last mode rest (fun entry member => agree entry (List.mem_append_right _ member)))
end

theorem compiled_equivalent
 (first last : Mode → Nat → Core.PresenceGeneration.TyTerm Nat)
 (mode : Mode) (term : Raw) (assignment : GeneralNominalCommonBridge.Assignment)
 (agree : ∀ entry ∈ reads mode term, Equivalent
   ((first entry.1 entry.2).eval model assignment) ((last entry.1 entry.2).eval model assignment)) :
 Equivalent (GeneralNominalRebaseEffectView243.eval assignment (GeneralNominalRebaseEffectView243.compile first mode term))
 (GeneralNominalRebaseEffectView243.eval assignment (GeneralNominalRebaseEffectView243.compile last mode term)) := by
 rw [GeneralNominalRebaseEffectView243.compile_exact,GeneralNominalRebaseEffectView243.compile_exact]
 exact value_equivalent _ _ mode term agree
end Yulang.GeneralNominalTemplateCongruence255
