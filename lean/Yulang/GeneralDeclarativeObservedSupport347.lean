import Yulang.GeneralDeclarativeObservedSyntax347
import Yulang.GeneralDeclarativeWherePairView346

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeObservedSupport347
open GeneralNominalState (State Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeObservedSyntax347 (Appears holds)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeOrigins321 (Origin Supported restriction Backed backed_iff)
open GeneralDeclarativeEntailment320 (appendFacts model_append)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWherePairView346 (extendBounds preserve bounds bounded_models)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralNominalCenters (Site)

def Record (s : State) (author : Equation → Origin → Prop) (row : Equation) (origin : Origin) : Prop :=
  Appears s row ∧ author row origin

/-- Accepted syntax and trustworthy source are independent conjuncts.
The subrelation is an input witness supplied by a caller, not an
inference of authorship from current raw model truth. -/
def attach {base : GeneralDeclarativeHead320.State} (priorSupport : Supported base done)
    (s : State) (author : Equation → Origin → Prop) (rows : List Equation) :
    Supported (appendFacts base rows) done where
  derivesFrom row origin := priorSupport.derivesFrom row origin ∨ row ∈ rows ∧ Record s author row origin
  ordinary := by
    intro row origin found
    rcases found with prior|current
    · exact List.mem_append_left _ (priorSupport.ordinary prior)
    · exact List.mem_append_right _ current.1

theorem exact_backing {base : GeneralDeclarativeHead320.State} (priorSupport : Supported base done)
    (s : State) (author : Equation → Origin → Prop) (rows : List Equation) (row : Equation) :
    row ∈ (restriction (attach priorSupport s author rows)).equations ↔
      Backed priorSupport row ∨ (row ∈ rows ∧ ∃ origin, Record s author row origin ∧ GeneralDeclarativeOrigins321.Available done origin) := by
  rw [backed_iff]
  constructor
  · rintro ⟨origin,prior|⟨placed,both⟩,valid⟩
    · exact .inl ⟨origin,prior,valid⟩
    · exact .inr ⟨placed,origin,both,valid⟩
  · rintro (⟨origin,prior,valid⟩|⟨placed,origin,both,valid⟩)
    · exact ⟨origin,.inl prior,valid⟩
    · exact ⟨origin,.inr ⟨placed,both⟩,valid⟩

theorem both_models {s : State} {rows : List Equation} {m : Assignment}
    {base : GeneralDeclarativeHead320.State} (valid : GeneralDeclarativeHead320.Models base m)
    (fit : Models s m) (proved : ∀ row ∈ rows, Appears s row) :
    GeneralDeclarativeHead320.Models (appendFacts base rows) m :=
  (model_append m).mpr ⟨valid,fun row present => holds (proved row present) m fit⟩

def arg (site : Site rs) (i : Fin (rs site.occurrence.demand.role).arity) : Capture :=
  ⟨(site.occurrence.demand.arguments i).1,site.center i,(site.occurrence.demand.arguments i).2⟩

/-- A real stored site can extend an ordinary projection with the
actual named center bounds. The append uses model preservation of
the *real* bounds, not replacement of a missing center head. -/
theorem child_view {s : State} {base : GeneralDeclarativeHead320.State}
    (priorSupport : Supported base done) (site : Site rs) (i : Fin (rs site.occurrence.demand.role).arity)
    (author : Equation → Origin → Prop) (rows : List Equation)
    (m : Assignment) (typed : site.Holds m) (valid : GeneralDeclarativeHead320.Models base m)
    (fit : Models s m) (readAll : ∀ row ∈ rows, Appears s row) :
    let cap := arg site i
    let observed := appendFacts (extendBounds base cap) rows
    Bounds observed cap ∧ GeneralDeclarativeHead320.Models observed m ∧
    (∀ row, row ∈ (restriction (attach (preserve priorSupport cap) s author rows)).equations ↔
      Backed priorSupport row ∨ (row ∈ rows ∧ ∃ origin, Record s author row origin ∧ GeneralDeclarativeOrigins321.Available done origin)) := by
  have bound := typed i
  have eligible : Bounds (appendFacts (extendBounds base (arg site i)) rows) (arg site i) :=
    ⟨.interval (List.mem_append_right _ List.mem_cons_self),
      .interval (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩
  exact ⟨eligible,both_models (bounded_models m valid bound.1 bound.2) fit readAll,
    fun row => exact_backing (preserve priorSupport (arg site i)) s author rows row⟩

end Yulang.GeneralDeclarativeObservedSupport347
