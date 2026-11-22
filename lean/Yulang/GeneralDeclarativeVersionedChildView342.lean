import Yulang.GeneralWherePhysicalEvidence319
import Yulang.GeneralDeclarativeVersionedRows342
import Yulang.GeneralDeclarativeTaggedDictionary340

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 37000
set_option maxHeartbeats 49000000
namespace Yulang.GeneralDeclarativeVersionedChildView342
open GeneralWhereOriginSingleCells318 (loNow hi loOld lower_moves sig)
open GeneralMixedCompoundChildEquality307 (mid)
open GeneralWherePhysicalCommit319 (final newChild)
open GeneralWherePhysicalCurrentRead319 (plan child_bounds)
open GeneralWherePhysicalChildModel319 (ports mid_value child_center site_holds)
open GeneralWherePhysicalEvidence319 (recorded)
open GeneralWhereVersionInstall317 (Models)
open GeneralDictionaryJournalRefinement228Source (roles root interpretation)
open GeneralWhereOriginSingleSource318 (sourceRegistry declaration oldPlan)
open GeneralLiveCompoundRegistry316 (leaf otherChild)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCommonBridge (Assignment)

abbrev code : Expr := .variant 0 (.variable 2)
noncomputable abbrev lower : Equation := ⟨loNow,code⟩
abbrev actual : Equation := ⟨mid,code⟩
abbrev upper : Equation := ⟨hi,code⟩
noncomputable abbrev arg : Capture := ⟨loNow,mid,hi⟩
noncomputable abbrev d : Demand := ⟨1,[arg],[]⟩
noncomputable abbrev basis : State := ⟨⟨[],[(loNow,mid),(mid,hi)]⟩,[lower,actual,upper]⟩

/-- Every old model satisfies this shaped current view, with original
names in every row. The corresponding rows are not parser-authored:
the two mode-specific receipts and the actual centre come from the
distinct checked versioned transaction. -/
theorem in_every_model (m : Assignment) (valid : Models final m) :
    GeneralDeclarativeHead320.Models basis m := by
  have shape := ports m valid
  have actualShape := mid_value m valid
  have b := site_holds m valid 0
  change CommonNominalFullCarrier.Subtype (m (newChild.occurrence.demand.arguments 0).1).1
    (m (newChild.center 0)).1 ∧ CommonNominalFullCarrier.Subtype (m (newChild.center 0)).1
    (m (newChild.occurrence.demand.arguments 0).2).1 at b
  rw [child_bounds,child_center] at b
  refine ⟨⟨(by intro row h; cases h),?_⟩,?_⟩
  · intro ends found
    rcases List.mem_cons.mp found with rfl|rest
    · exact b.1
    · cases List.mem_singleton.mp rest
      exact b.2
  · intro row known
    rcases List.mem_cons.mp known with rfl|others
    · exact shape.1
    · rcases List.mem_cons.mp others with rfl|last
      · exact actualShape
      · cases List.mem_singleton.mp last
        exact shape.2

def done (key : Nat) : Prop := key = root.identity ∧ plan ∈ final.versionedWhere

noncomputable def support : Supported basis done :=
  ⟨fun row whereFrom => row ∈ basis.equations ∧ whereFrom = .output root.identity,And.left⟩

theorem supported (row : Equation) (there : row ∈ basis.equations) :
    row ∈ (restriction support).equations := by
  apply (GeneralDeclarativeOrigins321.backed_iff support row).mpr
  exact ⟨.output root.identity,⟨there,rfl⟩,.completed ⟨rfl,recorded⟩⟩

theorem not_authored (row : Equation) : ¬ support.derivesFrom row .source := by
  rintro ⟨_,no⟩
  cases no

theorem actual_arguments : GeneralStoppedOrdinarySite335.demand newChild = d := by
  have center := child_center
  have bd := child_bounds
  unfold GeneralStoppedOrdinarySite335.demand GeneralStoppedOrdinarySite335.argument
  simp only [List.ofFn_succ]
  change (⟨1,[⟨(newChild.occurrence.demand.arguments 0).1,newChild.center 0,(newChild.occurrence.demand.arguments 0).2⟩],[]⟩ : Demand) = d
  rw [bd,center]

theorem range : Bounds basis arg :=
  ⟨.interval List.mem_cons_self,.interval (List.mem_cons_of_mem _ List.mem_cons_self)⟩

end Yulang.GeneralDeclarativeVersionedChildView342
