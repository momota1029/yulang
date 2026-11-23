import Yulang.GeneralDeclarativeI65Selection367
import Yulang.GeneralDeclarativeWitnessOrigins350

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessOrigins350 (Table Attached support)
open GeneralDeclarativeOrigins321 (restriction backed_iff)

def releaseAt (table : Table) (owner : Nat) : Table :=
  { table with released := owner :: table.released }

/-- The independent ready bit does not install or change any ordinary
row. This constructs no authorization for a real release; the relation
must be sourced at the declared boundary. -/
def releaseAttachment {s : GeneralDeclarativeHead320.State} {table : Table}
    (a : Attached s table) (owner : Nat) : Attached s (releaseAt table owner) :=
  ⟨a.authored,a.produced⟩

theorem exact_ready_differs_on_unchanged_current {s : State} {table : Table}
    (a : Attached s.current.ordinary table) {row : Equation} {owner : Nat}
    (written : (row,owner) ∈ table.produced)
    (noSource : row ∉ table.authored)
    (noPrior : ∀ x ∈ table.released, (row,x) ∉ table.produced) :
    row ∈ s.current.ordinary.equations ∧
      row ∉ (restriction (support a)).equations ∧
      row ∈ (restriction (support (releaseAttachment a owner))).equations := by
  refine ⟨a.produced _ written,?_,?_⟩
  · intro read
    obtain ⟨kind,certificate,good⟩ := (backed_iff (support a) row).mp read
    cases good with
    | source => exact noSource certificate
    | @completed prior ready => exact noPrior prior ready certificate
  · apply (backed_iff (support (releaseAttachment a owner)) row).mpr
    exact ⟨.output owner,written,.completed List.mem_cons_self⟩

/-- Any proposition depending only on the unchanged declarative
current and the row cannot read both independent source tables
exactly. This is a representation theorem, not a language verdict. -/
theorem no_erasure_of_ready_authority {s : State} {table : Table}
    (a : Attached s.current.ordinary table) {row : Equation} {owner : Nat}
    (written : (row,owner) ∈ table.produced)
    (noSource : row ∉ table.authored)
    (noPrior : ∀ x ∈ table.released, (row,x) ∉ table.produced)
    (check : State → Equation → Prop) :
    ¬((check s row ↔ row ∈ (restriction (support a)).equations) ∧
      (check s row ↔ row ∈ (restriction (support (releaseAttachment a owner))).equations)) := by
  rintro ⟨before,after⟩
  obtain ⟨_,notThen,now⟩ := exact_ready_differs_on_unchanged_current a written noSource noPrior
  exact notThen (before.mp (after.mpr now))

end Yulang.GeneralDeclarativeI65
