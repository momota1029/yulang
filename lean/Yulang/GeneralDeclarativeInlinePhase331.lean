import Yulang.GeneralDeclarativeInlineTwoOwners331
import Yulang.GeneralDeclarativeUnfinishedRoot330
import Yulang.GeneralDeclarativeRank321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInlinePhase331
open GeneralDeclarativeInlineTwoOwners331
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeLowerKnown321 (Delayed Ready)
open GeneralDeclarativePriority321 (Recurs Candidates)
open GeneralDeclarativeGraphRows321 (observed shapeOf fields)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeRank321 (graph_no_cycle)
open GeneralDeclarativeUnfinishedRoot330 (Local59)
open CommonRoleOutermostResolver (Classify)
open GeneralDeclarativeOpaqueNominal328 (point)

abbrev goal : Demand := ⟨1,[point 0],[]⟩

theorem ordinary_root_safe : ∀ n, ¬AliasCycle table (observed table) n := by
  apply graph_no_cycle (fun _ => 0) (fun _ _ h => rfl)
  rintro root code child ⟨rhs,present,shape⟩ part
  change (⟨root,rhs⟩ : Equation) ∈ [aliasRow,recordRow] at present
  rcases List.mem_cons.mp present with one|other
  · cases one
    cases shape
  · cases List.mem_singleton.mp other
    cases shape

theorem no_current_cycles (r : GeneralDeclarations.Registry) (i : GeneralNominalInspection.Interpretation)
    (tests : Candidates) : ¬Recurs table r i tests goal := by
  rintro (⟨a,_,cycle⟩|⟨_,_,_,_,_,_,_,_,_,site,_,cycle⟩)
  · exact ordinary_root_safe a.lower cycle
  · exact ordinary_root_safe site cycle

theorem suspended_until_both (done : Nat → Prop) (missing : ¬(done 21 ∧ done 22)) :
    Delayed (support done) goal := by
  refine ⟨point 0,List.mem_cons_self,?_⟩
  intro tag known
  exact missing ((lower_exact done).mp ⟨tag,known⟩)

theorem ready_when_both (done : Nat → Prop) (both : done 21 ∧ done 22) :
    Ready (support done) goal := by
  intro a h
  cases List.mem_singleton.mp h
  exact (lower_exact done).mpr both

/-- In the precise acyclic raw example the approved new I-59 reason
does not fire. Either missing original owner leaves a single pending
leaf; when both complete the independent actual read is available.
The ordinary table has the same satisfying model throughout. -/
theorem real_pending (done : Nat → Prop) (missing : ¬(done 21 ∧ done 22))
    (r : GeneralDeclarations.Registry) (i : GeneralNominalInspection.Interpretation)
    (tests : Candidates) (generate : Demand → GeneralDeclarations.Declaration → List Demand → Prop) :
    Classify (Local59 table r i (support done) tests generate) goal .pending :=
  ⟨.pending,.pending (.prior (.unsupported (suspended_until_both done missing) (no_current_cycles r i tests))),
    .pending⟩

end Yulang.GeneralDeclarativeInlinePhase331
