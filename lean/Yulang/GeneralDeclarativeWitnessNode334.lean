import Yulang.GeneralDeclarativeWitnessHead334
import Yulang.GeneralDeclarativeUnfinishedRoot330

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessNode334
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarations (Registry Declaration Clause Checked)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeWitnessHead334 (Slice Actuals actuals_sound)
open GeneralDeclarativeStableAttempt329 (Elected independent_election)
open GeneralDeclarativePriority321 (Candidates)
open GeneralDeclarativeInlineEndpoint331 (candidates)
open GeneralDeclarativeNestedBody332 (compileBody compiler_exact)
open GeneralDeclarativeStableCompiler329 (Frame)
open GeneralDeclarativeCurrentReceipt330 (Receipt relays_models complete Staged)
open GeneralDeclarativeGrowth327 (restrict)
open GeneralDeclarativeStableAssemble329 (tieState firsts)
open GeneralDeclarativeStableCanonical329 (EqualUses uses_existing exact)
open GeneralDeclarativeStableTies329 (rows pairOf)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCenteredHeadWFSource (Coverage)

/-- Ordinary generation data, independently of the choice guard, so
an implementation can project it without assuming a verdict. No
Frame, Meaning, Evidence or model premise is stored. -/
structure Generation {s : State} (p : Supported s done) (r : Registry) (i : Interpretation)
    (d : Demand) (impl : Declaration) (kids : List Demand) where
  slice : Slice p
  protect : List Nat
  fallback : Nat → Capture
  targets : Clause → Nat → Nat
  named : State
  spans : List (Nat × Capture)
  source : Actuals slice.support r.constructors i protect slice.base d.arguments impl.head named spans
  ordinary : State
  compiled : compileBody r i d impl named spans protect fallback targets = some (ordinary,kids)
  receipt : Receipt ordinary s

structure Witness {s : State} (p : Supported s done) (r : Registry) (i : Interpretation)
    (waiting : Demand → Declaration → Prop) (d : Demand) (impl : Declaration) (kids : List Demand)
    extends Generation p r i d impl kids where
  chosen : Elected s r i p (candidates p r i waiting) d impl

theorem Generation.frame {s : State} {p : Supported s done} (w : Generation p r i d impl kids)
    (checked : Checked r) (cover : Coverage r i) (wanted : Declared r d)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role) :
    ∃ frame : Frame w.ordinary r i d impl kids,
      frame.spans = w.spans ∧ frame.targets = w.targets ∧
      GeneralDeclarativeGrowth327.Extends (tieState w.named w.spans w.fallback) w.ordinary := by
  have ⟨_,observed,known⟩ := actuals_sound w.source (GeneralDeclarativeClauseBatch327.reflexive _)
  obtain ⟨ordinary,kids',frame,verified,_,sameSpans,sameTargets,_,writeTies,_⟩ :=
    compiler_exact checked cover visible role wanted
      w.protect w.fallback w.targets observed known
  cases Option.some.inj (verified.symm.trans w.compiled)
  exact ⟨frame,sameSpans,sameTargets,writeTies⟩

theorem Witness.frame {s : State} {p : Supported s done} (w : Witness p r i waiting d impl kids)
    (checked : Checked r) (cover : Coverage r i) (wanted : Declared r d) :
    ∃ frame : Frame w.ordinary r i d impl kids,
      frame.spans = w.spans ∧ frame.targets = w.targets ∧
      GeneralDeclarativeGrowth327.Extends (tieState w.named w.spans w.fallback) w.ordinary :=
  w.toGeneration.frame checked cover wanted w.chosen.viable.1.1 w.chosen.viable.1.2

theorem Witness.staged {s : State} {p : Supported s done} (w : Witness p r i waiting d impl kids)
    (checked : Checked r) (cover : Coverage r i) (wanted : Declared r d) : Staged s r i d impl kids := by
  obtain ⟨frame,_,_,_⟩ := w.frame checked cover wanted
  exact ⟨w.ordinary,⟨frame⟩,w.receipt⟩

/-- I-58 is not inferred from compatible endpoints. The real emitted
selected tie equations remain ordinary consequences in the current
state, so the very same model agrees on the actual occurrences. -/
theorem Witness.ties_in_current {s : State} {p : Supported s done}
    (w : Witness p r i waiting d impl kids)
    (checked : Checked r) (cover : Coverage r i) (wanted : Declared r d)
    (m) (fit : Models s m) : EqualUses m w.spans := by
  obtain ⟨_,_,_,extra⟩ := w.frame checked cover wanted
  have written := restrict extra m (relays_models w.receipt m fit)
  exact ((exact w.named (firsts w.spans w.fallback) w.spans
    (uses_existing w.spans w.fallback) m).mp written).2

end Yulang.GeneralDeclarativeWitnessNode334
