import Yulang.GeneralDeclarativeTxnCell348
import Yulang.GeneralDeclarativeObservedSyntax347
import Yulang.GeneralDeclarativeWhereAttributed346
import Yulang.GeneralDeclarativeJournalRelease347

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTxnNormalized348
open GeneralNominalCenters (Plan Site)
open GeneralWhereOriginDelta318 (Cell)
open GeneralWhereVersionInstall317 (Journal Models)
open GeneralWhereOriginTrace318 (rawOf)
open GeneralDeclarativeWhereEndpoint346 (At)
open GeneralDeclarativeObservedSyntax347 (structural structural_exact structural_sound)
open GeneralDeclarativeWhereAttributed346 (literal model_exact)
open GeneralDeclarativeHead320 (State Equation environment)
open GeneralDeclarativeOrigins321 (Origin Supported Backed restriction backed_iff)
open GeneralDeclarativeEntailment320 (Holds appendFacts model_append)
open GeneralNominalCenteredHeadMatExpressions (value)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_symm eqv_trans)
open GeneralNominalVersionedPlans231 (variables)

/-- A normalized observation and a stored compiler row can differ in
RHS spelling, e.g. one reads an aggregate coordinate and the other
a named projection. Neither one substitutes for the other as
authorship: the exact mode/current/ordinal is witnessed by At, and
the raw structural lookup checks the literal same target. -/
structure Observed {rs : Roles.RoleDecls} (j after : Journal rs) (p : Plan rs) (c : Cell p)
    (ord : Nat) (site : Site rs) (row : Equation) : Prop where
  birth : At j after p c ord site
  printed : structural (rawOf after) c.row.target = some row

theorem target {j after : Journal rs} {p : Plan rs} {c : Cell p} {ord : Nat} {site : Site rs} {row : Equation}
    (readback : Observed j after p c ord site row) : row.left = c.row.target := by
  obtain ⟨_,_,_,_,_,_,rfl⟩ := structural_exact readback.printed
  rfl

theorem same_rhs {j after : Journal rs} {p : Plan rs} {c : Cell p} {ord : Nat} {site : Site rs} {row : Equation}
    (readback : Observed j after p c ord site row) (m : Assignment) (fit : Models after m) :
    Holds m row ∧ Holds m (literal c) ∧
    Equivalent (value (environment m) .actual row.right) (value (environment m) .actual (literal c).right) := by
  have scanned := structural_sound readback.printed m fit.1.1.1
  have listed : p ∈ after.versionedWhere := List.mem_iff_getElem?.mpr ⟨_,readback.birth.stamp⟩
  have stored := (model_exact c m).mpr ((fit.2 p listed).1.rows _ readback.birth.written)
  refine ⟨scanned,stored,?_⟩
  change Equivalent (m row.left).1 (value (environment m) .actual row.right) at scanned
  rw [target readback] at scanned
  exact eqv_trans (eqv_symm scanned) stored

/-- Only the checked physical observation may enter the source slice
and then only when the matching owner is completed. The ordinary
retained compiler equation is not automatically exported as input. -/
def attach {s : State} (prior : Supported s done)
    {j after : Journal rs} {p : Plan rs} {c : Cell p} {ord : Nat} {site : Site rs} {row : Equation}
    (_seen : Observed j after p c ord site row) :
    Supported (appendFacts s [row,literal c]) done where
  derivesFrom use o := prior.derivesFrom use o ∨
    use = row ∧ o = .output p.packet.site.occurrence.identity
  ordinary := by
    rintro use _ (old|⟨rfl,_⟩)
    · exact List.mem_append_left _ (prior.ordinary old)
    · exact List.mem_append_right _ List.mem_cons_self

theorem typed {s : State} {j after : Journal rs} {p : Plan rs} {c : Cell p} {ord : Nat} {site : Site rs}
    {row : Equation} (seen : Observed j after p c ord site row) (m : Assignment) (fit : Models after m)
    (base : GeneralDeclarativeHead320.Models s m) :
    GeneralDeclarativeHead320.Models (appendFacts s [row,literal c]) m := by
  have h := same_rhs seen m fit
  refine (model_append m).mpr ⟨base,?_⟩
  intro e there
  rcases List.mem_cons.mp there with rfl|rest
  · exact h.1
  · cases List.mem_singleton.mp rest
    exact h.2.1

theorem exact_support {s : State} (prior : Supported s done)
    {j after : Journal rs} {p : Plan rs} {c : Cell p} {ord : Nat} {site : Site rs} {row use : Equation}
    (seen : Observed j after p c ord site row) :
    use ∈ (restriction (attach prior seen)).equations ↔
      Backed prior use ∨ (use = row ∧ done p.packet.site.occurrence.identity) := by
  rw [backed_iff]
  constructor
  · rintro ⟨o,old|⟨rfl,rfl⟩,available⟩
    · exact .inl ⟨o,old,available⟩
    · cases available with
      | completed h => exact .inr ⟨rfl,h⟩
  · rintro (⟨o,old,available⟩|⟨rfl,finished⟩)
    · exact ⟨o,.inl old,available⟩
    · exact ⟨_,.inr ⟨rfl,rfl⟩,.completed finished⟩

end Yulang.GeneralDeclarativeTxnNormalized348
