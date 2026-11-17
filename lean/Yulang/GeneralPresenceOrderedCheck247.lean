import Yulang.GeneralPresenceOrderedBlock247
import Yulang.GeneralPresenceCommonLaws245
namespace Yulang.GeneralPresenceOrderedCheck247
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOrderedBlock247
open GeneralPresenceUsedSupport245 (typedReads)
variable {Name : Type} [DecidableEq Name]

def check : List (Entry Name) → Bool
 | [] => true
 | entry :: rest =>
   !(typedReads entry.2).contains entry.1 &&
   rest.all (fun later => decide (later.1 ≠ entry.1)) &&
   rest.all (fun later => !(typedReads entry.2).contains later.1) && check rest

theorem check_exact (entries : List (Entry Name)) : check entries = true ↔ SafeOrder entries := by
 induction entries with
 | nil => simp [check,SafeOrder]
 | cons entry rest ih => simp [check,SafeOrder,ih,and_assoc]

theorem checked_model (model : Model) (refl : ∀ value, model.subTy value value)
 (entries : List (Entry Name)) (checked : check entries = true) (boundary : Name → Comp model) :
 All model (solve model entries boundary) (block entries) :=
 block_satisfied model refl entries ((check_exact entries).mp checked) boundary

/-- The list contains unguarded alias, union and intersection definitions,
followed by an arrow whose rows read private names, including its own target. -/
def exampleEntries : List (Entry Nat) :=
 [(2,.var 0), (3,.union (.var 2) (.var 1)), (4,.inter (.var 3) (.var 0)),
  (5,.arrow (.var 4) (.var 3) (.var 2) (.var 5))]

theorem example_checked : check exampleEntries = true := by decide

theorem example_model (boundary : Nat → Comp CommonNominalFullCarrier.model) :
 All CommonNominalFullCarrier.model (solve CommonNominalFullCarrier.model exampleEntries boundary) (block exampleEntries) :=
 checked_model _ GeneralPresenceCommonLaws245.common_laws.refl exampleEntries example_checked boundary

theorem example_rows (boundary : Nat → Comp CommonNominalFullCarrier.model) (name : Nat) :
 (solve CommonNominalFullCarrier.model exampleEntries boundary name).2 = (boundary name).2 :=
 solve_rows _ _ boundary name

theorem self_row_kept (boundary : Nat → Comp CommonNominalFullCarrier.model) :
 (RowTerm.var 5).eval CommonNominalFullCarrier.model (solve CommonNominalFullCarrier.model exampleEntries boundary) =
 (boundary 5).2 := example_rows boundary 5

theorem forward_dependency_rejected : check ([(3,.var 2),(2,.var 0)] : List (Entry Nat)) = false := by decide

theorem provider_first_passes : check ([(2,.var 0),(3,.var 2)] : List (Entry Nat)) = true := by decide
end Yulang.GeneralPresenceOrderedCheck247
