import Yulang.GeneralDeclarativeVersionedPhysical342
import Yulang.GeneralStoppedShape335

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 15000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralDeclarativeVersionedRootRead342
open GeneralWherePhysicalActive319 (active ctx refines embed)
open GeneralWherePhysicalCurrentRead319 (zero desc nominal0)
open GeneralWherePhysicalPast319 (point two)
open GeneralWherePhysicalCommit319 (final)
open GeneralWhereVersionInstall317 (Models)
open GeneralNominalRefinements (renameDescriptor)
open GeneralStoppedShape335 (descriptorExpr descriptor_semantics)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCommonBridge (Assignment)

noncomputable abbrev here := refines.base.embed zero
noncomputable abbrev descriptor := renameDescriptor refines.base.embed desc
abbrev publicRow : Equation := ⟨0,.nominal 0 [.variable 2,.variable 2]⟩

theorem recorded : active.nominals here = some descriptor :=
  refines.nominals _ _ nominal0

theorem same_type_name : active.base.source (refines.base.embed two) = 2 :=
  (refines.base.source two).trans rfl

theorem same_root_name : active.base.source here = 0 := (refines.base.source zero).trans rfl

theorem encoded :
    descriptorExpr active.base descriptor = some publicRow.right := by
  have args : descriptor.arguments =
      [.type (refines.base.embed two,refines.base.embed two),
       .type (refines.base.embed two,refines.base.embed two)] := rfl
  unfold descriptorExpr
  rw [args]
  simp [GeneralStoppedShape335.point,GeneralStoppedShape335.one,same_type_name,
    show descriptor.declaration.name = 0 from rfl]

/-- Ordinary point readback is available from the *recorded current
descriptor*. This certificate does not promote the row to a literal
parser-authored source origin. -/
theorem raw_root (m : Assignment) (valid : Models final m) :
    GeneralDeclarativeEntailment320.Holds m publicRow := by
  have physical : GeneralNominalState.Models active m := valid.1.1.1
  have known := physical.2.1 here descriptor recorded
  have equivalent := (descriptor_semantics active.base here descriptor m encoded).mp known
  rw [same_root_name] at equivalent
  exact equivalent

end Yulang.GeneralDeclarativeVersionedRootRead342
