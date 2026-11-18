import Yulang.GeneralVersionRowsStages259
import Yulang.GeneralNominalVersionedSourceCongruence238
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralVersionBoundaryCompletion259
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryVersionLoopSource237 (snapshot model S)
open CommonNominalFullCarrier
open GeneralVersionRowsRaw259 (withRows)

def complete (boundary : Assignment) : Assignment := fun name =>
 if name ≤ 3 then boundary name else ((model name).1,(boundary name).2)

def Agree (first last : Assignment) : Prop :=
 (∀ name, name ≤ 3 → first name = last name) ∧ ∀ name, (first name).2 = (last name).2

theorem agrees (boundary : Assignment) : Agree (complete boundary) boundary := by
 constructor
 · intro name small; simp only [complete,small,ite_true]
 · intro name; unfold complete; split <;> rfl

theorem second_scalar (boundary : Assignment) (valid : GeneralNominalState.Models snapshot boundary) :
 Equivalent (boundary 1).1 S := by
 constructor
 · exact valid.1.1 (.tyLe (.var 1) (.base .int)) (by decide)
 · exact valid.1.1 (.tyLe (.base .int) (.var 1)) (by decide)

theorem initial_types (boundary : Assignment) (valid : GeneralNominalState.Models snapshot boundary)
 (name : Nat) (small : name ≤ 3) : Equivalent (boundary name).1 (model name).1 := by
 have cases : name = 0 ∨ name = 1 ∨ name = 2 ∨ name = 3 := by omega
 rcases cases with rfl | rfl | rfl | rfl
 · exact GeneralDictionaryVersionLoopInitial238.scalar_fixed boundary valid
 · exact second_scalar boundary valid
 · exact GeneralDictionaryVersionLoopInitial238.foo_fixed boundary valid
 · exact GeneralDictionaryVersionLoopInitial238.root_fixed boundary valid

theorem equivalent (boundary : Assignment) (valid : GeneralNominalState.Models snapshot boundary) :
 GeneralNominalAssignmentCongruence238.Same (complete boundary) (withRows (fun name => (boundary name).2)) := by
 intro name
 constructor
 · by_cases small : name ≤ 3
   · simpa only [complete,small,ite_true,withRows] using initial_types boundary valid name small
   · simp only [complete,small,ite_false,withRows]
     exact ⟨subtype_refl _,subtype_refl _⟩
 · exact (agrees boundary).2 name

theorem all_stages (boundary : Assignment) (valid : GeneralNominalState.Models snapshot boundary) (n : Nat) :
 GeneralNominalVersionedJournal232.Models (GeneralDictionaryVersionLoopIteration239.state n) (complete boundary) :=
 (GeneralNominalVersionedSourceCongruence238.source_models_iff (equivalent boundary valid)
   (GeneralDictionaryVersionLoopIteration239.reachable n)).mpr (GeneralVersionRowsStages259.all_stages _ n)

theorem packet_holds (boundary : Assignment) (valid : GeneralNominalState.Models snapshot boundary) (n : Nat) :
 GeneralNominalVersionedPlans231.Holds (GeneralDictionaryVersionLoopBook239.plan n) (complete boundary) :=
 (GeneralNominalVersionedPacketCongruence238.holds_iff (equivalent boundary valid) _).mpr
   (GeneralVersionRowsStages259.packet_holds _ n)
end Yulang.GeneralVersionBoundaryCompletion259
