import Yulang.GeneralDeclarativeNestedHeadList332
import Yulang.GeneralDeclarativeNestedBody332
import Yulang.GeneralDeclarativeCurrentReceipt330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNestedReplay332
open GeneralDeclarations (Registry Declaration Clause Checked)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (Supported restriction)
open GeneralDeclarativeNestedView332 (Sources)
open GeneralDeclarativeNestedHeadList332 (captureArgs capture_sound probe)
open GeneralDeclarativeNestedBody332 (compileBody compiler_exact)
open GeneralDeclarativeStableReads329 (ranges)
open GeneralDeclarativeStableCompiler329 (Frame)
open GeneralDeclarativeCurrentReceipt330 (Receipt Rule exact_proposal)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativePriority321 (Candidates)
open GeneralDeclarativeNFComplete324 (facts)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeAssembly320 (Meaning)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeOpaqueBatch328 (check)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadWFSource (Coverage)

/-- This is a finite syntax-driven positive replay, not the candidate
search. A missing read does not select a diagnostic. The only caller-
chosen names are the explicitly reserved names and the declared
logical target map; the outgoing child list is computed, not supplied. -/
def replay (r : Registry) (i : Interpretation) (d : Demand) (impl : Declaration)
    (src : Sources source) (start : State) (fixed : List Nat)
    (fallback : Nat → Capture) (targets : Clause → Nat → Nat) :
    Option (State × List Demand) := do
  if !probe src r.constructors i d.arguments impl.head then none
  else
    let (current,spans) ← captureArgs src r.constructors i fixed start d.arguments impl.head
    compileBody r i d impl current spans fixed fallback targets

theorem replay_frame {s : State} {p : Supported s done}
    (src : Sources (restriction p)) (checked : Checked r) (cover : Coverage r i)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role) (declared : Declared r d)
    (fit : ∀ a ∈ d.arguments, Bounds s a)
    (ran : replay r i d impl src s fixed fallback targets = some (after,kids)) :
    ∃ frame : Frame after r i d impl kids, frame.targets = targets := by
  by_cases recognized : probe src r.constructors i d.arguments impl.head = true
  · cases heads : captureArgs src r.constructors i fixed s d.arguments impl.head with
    | none => simp [replay,recognized,heads] at ran
    | some got =>
      rcases got with ⟨current,spans⟩
      obtain ⟨_,actual,actualBounds⟩ := capture_sound src (GeneralDeclarativeClauseBatch327.reflexive s) fit heads
      obtain ⟨expected,proposed,frame,printed,_,_,target,_,_,_⟩ :=
        compiler_exact checked cover visible role declared fixed fallback targets actual actualBounds
      have exactBody : compileBody r i d impl current spans fixed fallback targets = some (after,kids) := by
        simpa [replay,recognized,heads] using ran
      have same := Option.some.inj (printed.symm.trans exactBody)
      cases same
      exact ⟨frame,target⟩
  · simp [replay,recognized] at ran

/-- Current-state ordinary evidence is accepted only for the same
computed demands, in the same order and with the same fixed targets.
Current election and name-identical receipt remain independent inputs. -/
theorem current_after_replay {s t : State} {p : Supported s done} {q : Supported t now}
    (src : Sources (restriction p)) (checked : Checked r) (cover : Coverage r i)
    (declared : Declared r d) (fit : ∀ a ∈ d.arguments, Bounds s a)
    (ran : replay r i d impl src s fixed fallback targets = some (after,kids))
    (receipt : Receipt after t) (chosen : Elected t r i q tests d impl)
    (ordered : check kids proposed = true) :
    ∃ frame : Frame after r i d impl kids,
      frame.targets = targets ∧ Rule t r i q tests d (.selected impl.id proposed) ∧
      Result t (facts r i frame.capture impl d proposed) ∧
      (∀ m, Models t m → Meaning r i m d impl frame.capture proposed) := by
  obtain ⟨frame,named⟩ := replay_frame src checked cover chosen.viable.1.1 chosen.viable.1.2 declared fit ran
  exact ⟨frame,named,exact_proposal checked cover declared frame receipt chosen ordered⟩

end Yulang.GeneralDeclarativeNestedReplay332
