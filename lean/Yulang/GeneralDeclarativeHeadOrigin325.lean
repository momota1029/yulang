import Yulang.GeneralDeclarativeNFHead324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeHeadOrigin325
open GeneralDeclarativeHead320 (State Equation Models byMode)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEqualities322 (Derives entails semantic)
open GeneralDeclarativeExactWalk323 (Exact)
open GeneralDeclarativeTermWalk322 (Occurrence)
open GeneralDeclarativeTermOccurrences322 (source_binders actual_positions)
open GeneralDeclarativeRepeatedActual323 (BindsAt OccursAt)
open GeneralDeclarativeNFHead324 (Scan fact produces)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarationPatterns (Constructors Pattern normalize)
open GeneralNominalInspection (Interpretation)
open CommonRoleOutermostResolver (All₂)

/-- Every actual walk occurrence uses the very mode and binder found
at that position. A derivation from ordinary equations, not an assumed
all-model equality, connects it to the selected capture name. -/
def ReadsUse (s : State) (cap : Nat → Capture) (o : Occurrence) : Prop :=
  Derives s o.term (.variable (byMode (cap o.binder) o.mode))

theorem observed_binders (translated : translate c i (normalize p) = some code)
    (walked : Exact .actual actual code uses) :
    uses.map Occurrence.binder = (normalize p).variables ∧
      ∀ o ∈ uses, o.mode = .actual := by
  exact ⟨(source_binders translated walked.walked).1,(actual_positions walked.walked).2⟩

structure Read (s : State) (c : Constructors) (i : Interpretation) (cap : Nat → Capture)
    (a : Capture) (p : Pattern) : Prop where
  range : Bounds s a
  source : ∃ actual code uses,
    Derives s (.variable a.center) actual ∧
    translate c i (normalize p) = some code ∧ Exact .actual actual code uses ∧
    ∀ occurrence ∈ uses, ReadsUse s cap occurrence

theorem by_equations {s : State} (read : Read s c i cap a p) :
    Bounds s a ∧ Result s (fact c i cap a p) := by
  obtain ⟨actual,code,uses,origin,printed,walked,positions⟩ := read.source
  exact ⟨read.range,produces (⟨read.range,actual,code,entails origin,printed,walked⟩ : Scan s c i a p uses)
    (fun m valid o used => semantic (positions o used) m valid)⟩

theorem ordered {s : State} (reads : All₂ (Read s c i cap) args patterns) :
    All₂ (fun a p => Bounds s a ∧ Result s (fact c i cap a p)) args patterns := by
  induction reads with
  | nil => exact .nil
  | cons head tail ih => exact .cons (by_equations head) ih

end Yulang.GeneralDeclarativeHeadOrigin325
