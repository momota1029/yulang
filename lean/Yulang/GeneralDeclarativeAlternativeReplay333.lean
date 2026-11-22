import Yulang.GeneralDeclarativeAlternativeCapture333
import Yulang.GeneralDeclarativeNestedBody332
import Yulang.GeneralDeclarativeCurrentReceipt330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAlternativeReplay333
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarations (Registry Declaration Clause Checked)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarativeAlternativeView333 (Index)
open GeneralDeclarativeAlternativeHeads333 (Centers center_bounds endpoint endpoint_plan)
open GeneralDeclarativeAlternativeCapture333 (captureAll capture_sound)
open GeneralDeclarativeAlternativeNeeds333 (Planned Eventually eventually_pair)
open GeneralDeclarativeInlineEndpoint331 (Matches)
open GeneralDeclarativeNestedBody332 (compileBody compiler_exact)
open GeneralDeclarativeStableCompiler329 (Frame)
open GeneralDeclarativeCurrentReceipt330 (Receipt Rule exact_proposal)
open GeneralDeclarativePriority321 (Candidates)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativeNFComplete324 (facts)
open GeneralDeclarativeAssembly320 (Meaning)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarativeOpaqueBatch328 (check)
open GeneralDeclarativeClauseBatch327 (reflexive)
open GeneralDeclarativeGrowth327 (Extends)
open CommonRoleOutermostResolver (All₂)

/-- Return all compiler receipts from positive evidence. The result is
not a ranked selection. A later exact current receipt may witness one
of these results; a failure of any one alternative is not a diagnostic. -/
def replay (src : Index source) (depth : Nat) (r : Registry) (i : Interpretation) (d : Demand)
    (impl : Declaration) (s : State) (keep : List Nat) (fallback : Nat → Capture)
    (targets : Clause → Nat → Nat) : List (State × List Demand) :=
  if endpoint src depth r.constructors i d.arguments impl.head then
    (captureAll src depth r.constructors i keep s d.arguments impl.head).filterMap fun (after,spans) =>
      compileBody r i d impl after spans keep fallback targets
  else []

theorem frame_from_replay {s : State} {p : Supported s done}
    (src : Index (restriction p)) (checked : Checked r) (cover : Coverage r i)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role) (declared : Declared r d)
    (fit : ∀ a ∈ d.arguments, Bounds s a)
    (actual : (after,kids) ∈ replay src fuel r i d impl s keep fallback targets) :
    ∃ frame : Frame after r i d impl kids, frame.targets = targets := by
  unfold replay at actual
  split at actual
  · rcases List.mem_filterMap.mp actual with ⟨⟨middle,spans⟩,used,compiled⟩
    obtain ⟨_,observed,valid⟩ := capture_sound src (reflexive s) fit used
    obtain ⟨expected,computed,frame,wrote,_,_,same,_,_,_⟩ :=
      compiler_exact checked cover visible role declared keep fallback targets observed valid
    cases Option.some.inj (wrote.symm.trans compiled)
    exact ⟨frame,same⟩
  · cases actual

/-- Finite witness sufficiency for the actual old normalized reads and
body. The input does not assume a compiler frame, rows, output
delegations or a child list. It also does not assert that the matched
candidate may be selected in an arbitrary state. -/
theorem replay_plan {s : State} {p : Supported s done}
    (checked : Checked r) (cover : Coverage r i)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role) (declared : Declared r d)
    (probed : All₂ (Matches (restriction p) r.constructors i) d.arguments impl.head)
    (actual : Centers p r.constructors i d.arguments impl.head)
    (keep : List Nat) (fallback : Nat → Capture) (targets : Clause → Nat → Nat) :
    Planned (fun src : Index (restriction p) =>
      Eventually (fun depth => ∃ result, result ∈ replay src depth r i d impl s keep fallback targets)) := by
  apply ((endpoint_plan probed).both (GeneralDeclarativeAlternativeCapture333.capture_plan actual keep)).map
  intro src available
  obtain ⟨least,works⟩ := eventually_pair available.1 available.2
  refine ⟨least,fun f enough => ?_⟩
  obtain ⟨observed,got⟩ := works f enough
  obtain ⟨⟨middle,spans⟩,seen⟩ := got s (reflexive s)
  obtain ⟨_,shapes,fits⟩ := capture_sound src (reflexive s) (center_bounds actual) seen
  obtain ⟨after,kids,chosen,write,rebuilt,_,_,_,_,_⟩ :=
    compiler_exact checked cover visible role declared keep fallback targets shapes fits
  refine ⟨(after,kids),?_⟩
  change (after,kids) ∈ replay src f r i d impl s keep fallback _
  unfold replay
  rw [ite_eq_left observed]
  exact List.mem_filterMap.mpr ⟨(middle,spans),seen,write⟩

theorem consume_current {s t : State} {p : Supported s done} {q : Supported t now}
    (src : Index (restriction p)) (checked : Checked r) (cover : Coverage r i)
    (declared : Declared r d) (fit : ∀ a ∈ d.arguments, Bounds s a)
    (actual : (after,kids) ∈ replay src fuel r i d impl s keep fallback targets)
    (receipt : Receipt after t) (chosen : Elected t r i q tests d impl)
    (ordered : check kids proposed = true) :
    ∃ frame : Frame after r i d impl kids,
      frame.targets = targets ∧ Rule t r i q tests d (.selected impl.id proposed) ∧
      Result t (facts r i frame.capture impl d proposed) ∧
      (∀ m, Models t m → Meaning r i m d impl frame.capture proposed) := by
  obtain ⟨frame,named⟩ := frame_from_replay src checked cover chosen.viable.1.1 chosen.viable.1.2 declared fit actual
  exact ⟨frame,named,exact_proposal checked cover declared frame receipt chosen ordered⟩

end Yulang.GeneralDeclarativeAlternativeReplay333
