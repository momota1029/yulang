import Yulang.GeneralDeclarativeI65I74ExactStampedEligible462

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PreparedDeclarations463
open Yulang.GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (Current authoredRegistry)
open GeneralDeclarativeWitnessClassifyVariance357 (DeclarationReady)
open Checker408 (Problem)
open RetainedFull445 (FullProblem)

/-- The GD producer is independent and external. This interface asks for
soundness of finite data validation; this module does not implement GD's
complete production of such data. -/
structure CertificateProtocol (cur : Current) where
  Data : Type
  verify : Declaration → Data → Bool
  sound : ∀ d wire, verify d wire = true → DeclarationReady (authoredRegistry cur) d

structure CheckedTable (cur : Current) where
  rows : List Declaration
  prepared : ∀ d ∈ rows, DeclarationReady (authoredRegistry cur) d

def prepareOne {cur : Current} (gd : CertificateProtocol cur) (d : Declaration) (w : gd.Data) :
    Option {out : Declaration // DeclarationReady (authoredRegistry cur) out} :=
  if ok : gd.verify d w = true then some ⟨d,gd.sound d w ok⟩ else none

def prepareTable {cur : Current} (gd : CertificateProtocol cur) :
    List (Declaration × gd.Data) → Option (CheckedTable cur)
  | [] => some ⟨[],fun _ impossible => False.elim (List.not_mem_nil impossible)⟩
  | (d,w) :: src => do
    let first ← prepareOne gd d w
    let rest ← prepareTable gd src
    return ⟨first.val :: rest.rows,by
      intro chosen h
      rcases List.mem_cons.mp h with eq | later
      · exact eq.symm ▸ first.property
      · exact rest.prepared chosen later⟩

/-- Exact resolved declaration equality (not only numeric ID) and the
same original registry. No certificate, verifier or capture is read
while answering requests. -/
def tableContains {cur : Current} (tab : CheckedTable cur) (d : Declaration) : Bool :=
  decide (d ∈ tab.rows)

theorem table_contains_returns_exact_readiness {cur : Current}
    (tab : CheckedTable cur) (d : Declaration) (ok : tableContains tab d = true) :
    DeclarationReady (authoredRegistry cur) d :=
  tab.prepared d (of_decide_eq_true ok)

theorem prepared_table_retains_only_exact_declaration_order {cur : Current}
    (gd : CertificateProtocol cur) (all : List (Declaration × gd.Data)) (t : CheckedTable cur) :
    prepareTable gd all = some t → t.rows = all.map Prod.fst := by
  induction all generalizing t with
  | nil =>
    intro done
    obtain rfl := Option.some.inj done
    rfl
  | cons first rest ih =>
    obtain ⟨d,w⟩ := first
    intro done
    by_cases ok : gd.verify d w = true
    · cases now : prepareTable gd rest with
      | none => simp [prepareTable,prepareOne,ok,now,Option.bind] at done
      | some table =>
        simp [prepareTable,prepareOne,ok,now,Option.bind] at done
        subst t
        simp [ih table now]
    · simp [prepareTable,prepareOne,ok,Option.bind] at done

structure Input where
  problem : FullProblem
  checked : CheckedTable problem.state.base.core.current

theorem missPrepared {cur : Current} (tab : CheckedTable cur) (d : Declaration)
    (absent : d ∉ tab.rows) : tableContains tab d = false := by
  simp [tableContains,absent]

end Yulang.GeneralDeclarativeI65.I72.PreparedDeclarations463
