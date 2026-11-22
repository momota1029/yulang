import Yulang.GeneralDeclarativeTxnTrace348
import Yulang.GeneralDeclarativeTxnReceipt348

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTxnHistory348
open GeneralDeclarations (Registry)
open GeneralNominalCenters (Plan Site)
open GeneralWhereOriginDelta318 (Cell)
open GeneralWhereOriginTrace318 (rawOf)
open GeneralWhereVersionInstall317 (Journal Models)
open GeneralDeclarativeWhereEndpoint346 (At)
open GeneralDeclarativeTxnTrace348 (Step)
open GeneralDeclarativeTxnObserve348 (retains_actor)
open GeneralDeclarativeTxnNormalized348 (Observed same_rhs)
open GeneralDeclarativeObservedSyntax347 (structural)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCommonBridge (Assignment)

theorem found_stamp {a b : Journal rs} {p : Plan rs} {k : Nat}
    (step : Step r keep a b) (present : a.versionedWhere[k]? = some p) :
    b.versionedWhere[k]? = some p := by
  cases step with
  | transaction _ _ _ _ =>
    change (_ ++ [_])[k]? = _
    rwa [List.getElem?_append_left (List.getElem?_eq_some_iff.mp present).1]
  | observe _ _ => exact present
  | reobserve _ _ _ => exact present

theorem found_site {a b : Journal rs} {s : Site rs} {k : Nat}
    (step : Step r keep a b) (present : a.mixed.core.sites[k]? = some s) :
    b.mixed.core.sites[k]? = some s := by
  cases step with
  | transaction _ _ _ _ => exact GeneralDeclarativeTxnReceipt348.keeps_prior present
  | observe _ _ => exact present
  | reobserve _ _ _ => exact present

theorem born_step {basis a b : Journal rs} {p : Plan rs} {c : Cell p} {ord : Nat} {s : Site rs}
    (step : Step r keep a b) (born : At basis a p c ord s) : At basis b p c ord s :=
  ⟨found_stamp step born.stamp,found_site step born.physical,born.emittedHere,born.childHere,
    born.canonical,born.clauseRole,born.inputHere,born.written⟩

theorem born_path {basis a b : Journal rs} {p : Plan rs} {c : Cell p} {ord : Nat} {s : Site rs}
    (path : B4Target.Steps (Step r keep) a b) (born : At basis a p c ord s) :
    At basis b p c ord s := by
  induction path with
  | refl => exact born
  | tail _ next ih => exact born_step next ih

/-- The full certificate of authorship survives the checked fragment,
including subsequent transactions, but the actual visible spelling is
checked again against the final state. -/
theorem current_after_path {basis a b : Journal rs} {p : Plan rs} {c : Cell p}
    {ord : Nat} {s : Site rs} {row : Equation}
    (path : B4Target.Steps (Step r keep) a b) (born : At basis a p c ord s)
    (visible : structural (rawOf b) c.row.target = some row) :
    Observed basis b p c ord s row :=
  ⟨born_path path born,visible⟩

theorem typed_after_path {basis a b : Journal rs} {p : Plan rs} {c : Cell p}
    {ord : Nat} {s : Site rs} {row : Equation}
    (path : B4Target.Steps (Step r keep) a b) (born : At basis a p c ord s)
    (visible : structural (rawOf b) c.row.target = some row)
    (m : Assignment) (fit : Models b m) :
    GeneralDeclarativeEntailment320.Holds m row ∧
      GeneralDeclarativeEntailment320.Holds m (GeneralDeclarativeWhereAttributed346.literal c) :=
  let valid := same_rhs (current_after_path path born visible) m fit
  ⟨valid.1,valid.2.1⟩

end Yulang.GeneralDeclarativeTxnHistory348
