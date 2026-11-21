import Yulang.GeneralDeclarativeInlineBoundary331
import Yulang.GeneralDeclarativeUnfinishedRoot330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInlineReplay331
open GeneralDeclarations (Checked Clause)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeInlineCompiler331 (Source compile)
open GeneralDeclarativeStableCompiler329 (Frame)
open GeneralDeclarativeCurrentReceipt330 (Receipt Staged exact_proposal)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarativeUnfinishedRoot330 (Local59)
open GeneralDeclarativeGrowth327 (Extends)
open GeneralDeclarativeOpaqueBatch328 (check check_exact)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeNFComplete324 (facts)
open GeneralDeclarativeAssembly320 (Meaning)

/-- Compile before seeing the proposed list or the currently selected
outcome. The independent current proof of original support/election
and the exact ordinary receipt are kept separate. A rejected/reordered
proposal cannot use the validated selected branch of this construction.
No completeness of current election or receipt extraction is assumed
to follow from arbitrary source syntax. -/
theorem independent_readback {s : State} {d : Demand} {p : Supported s done}
    (checked : Checked r) (coverage : Coverage r i) (owns : impl ∈ r.declarations)
    (role : impl.role = d.role) (wanted : Declared r d)
    (actuals : Source p r.constructors i d.arguments impl.head) (keep : List Nat)
    (fallback : Nat → Capture) (targets : Clause → Nat → Nat) :
    ∃ (expected : State) (actualKids : List Demand) (frame : Frame expected r i d impl actualKids),
      Extends s expected ∧ frame.targets = targets ∧
      expected = appendFacts (appendFacts frame.prepared frame.whereRows) frame.rootRows ∧
      ∀ (current : State) {settled : Nat → Prop} (origin : Supported current settled) tests,
        Receipt expected current → Elected current r i origin tests d impl →
        ∀ proposed, (check actualKids proposed = true ↔ proposed = actualKids) ∧
          (check actualKids proposed = true →
            Local59 current r i origin tests (Staged current r i) d (.selected impl.id proposed) ∧
            Result current (facts r i frame.capture impl d proposed) ∧
            ∀ m, Models current m → Meaning r i m d impl frame.capture proposed) := by
  obtain ⟨expected,actualKids,frame,grows,exactTargets,exactWrites,_,_,_⟩ :=
    compile checked coverage owns role wanted actuals keep fallback targets
  refine ⟨expected,actualKids,frame,grows,exactTargets,exactWrites,?_⟩
  intro current doneNow origin tests receipt currentChoice proposal
  refine ⟨?_,?_⟩
  · exact ⟨fun h => (check_exact.mp h).symm,fun h => check_exact.mpr h.symm⟩
  · intro checkedList
    have ⟨localRule,result,meaning⟩ := exact_proposal checked coverage wanted frame receipt currentChoice checkedList
    exact ⟨.prior localRule,result,meaning⟩

end Yulang.GeneralDeclarativeInlineReplay331
