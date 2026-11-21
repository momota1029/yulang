import Yulang.GeneralDeclarativeStableHybrid329

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStableReplay329
open GeneralDeclarations (Checked Clause)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeGrowth327 (Extends trans fits restrict)
open GeneralDeclarativeStableReads329 (weakened)
open GeneralDeclarativeStableCompiler329 (Frame read)
open GeneralDeclarativeStableSelect329 (Rule)
open GeneralDeclarativeStableAttempt329 (Elected independent_election)
open GeneralDeclarativeStableHybrid329 (Source run ordered)
open GeneralDeclarativeStableInputs329 (demandNames)
open GeneralDeclarativeStableAssemble329 (frame_after)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeNFComplete324 (facts)
open GeneralDeclarativeAssembly320 (Meaning)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarativeOpaqueBatch328 (check check_exact)

/-- Later ordinary additions preserve a recorded compilation frame,
not the independent candidate decision. The same exact output rows
and literal ordered child list are reused. -/
def carry {s t : State} {d : Demand} (commit : Frame s r i d impl kids)
    (kept : Extends s t) : Frame t r i d impl kids :=
  { base := commit.base
    spans := commit.spans
    observed := weakened kept commit.observed
    tied := fun e inList m valid => commit.tied e inList m (restrict kept m valid)
    ranges := fun q h => fits kept (commit.ranges q h)
    targets := commit.targets
    keep := commit.keep
    inputState := commit.inputState
    prepared := commit.prepared
    ports := commit.ports
    inputRead := commit.inputRead
    current := trans commit.current kept
    whereRows := commit.whereRows
    whereWritten := commit.whereWritten
    whereHere := fun _ h => kept.equations (commit.whereHere h)
    rootRows := commit.rootRows
    rootWritten := commit.rootWritten
    rootHere := fun _ h => kept.equations (commit.rootHere h)
    ordered := commit.ordered }

theorem fixed_names {s t : State} {d : Demand}
    (commit : Frame s r i d impl kids) (kept : Extends s t) :
    (carry commit kept).capture = commit.capture := rfl

/-- The exact proposal check plus the independent current election
validates the emitted node. Nothing infers current readiness from an
old election or licensing a delayed output. -/
theorem replay {s t : State} {d : Demand} {p : Supported t done}
    (checked : Checked r) (coverage : Coverage r i)
    (declared : Declared r d)
    (commit : Frame s r i d impl kids) (kept : Extends s t)
    (stillElected : Elected t r i p tests d impl)
    (listOk : check kids proposed = true) :
    Rule t r i p tests d (.selected impl.id proposed) ∧
      Result t (facts r i commit.capture impl d proposed) ∧
      (∀ m, Models t m → Meaning r i m d impl commit.capture proposed) ∧
      ∀ child ∈ proposed, Declared r child := by
  have same := check_exact.mp listOk
  subst proposed
  exact ⟨independent_election stillElected ⟨carry commit kept⟩,
    read checked coverage stillElected.viable.1.1 stillElected.viable.1.2 declared (carry commit kept)⟩

/-- Start from actual source lookups, permitting a checked opaque
endpoint path when covered. No binding or compiler certificate is
in the premises. The returned ordinary state is constructed, not
an assertion that arbitrary runtime or source selections use it. -/
theorem from_sources {s : State} {d : Demand} {p : Supported s done}
    (checked : Checked r) (coverage : Coverage r i)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role) (declared : Declared r d)
    (observed : Source s r.constructors i p d.arguments impl.head)
    (keep : List Nat) (fallback : Nat → Capture) (targets : Clause → Nat → Nat) :
    ∃ (current : State) (kids : List Demand) (frame : Frame current r i d impl kids),
      Extends s current ∧
      Result current (facts r i frame.capture impl d kids) ∧
      (∀ m, Models current m → Meaning r i m d impl frame.capture kids) ∧
      ∀ child ∈ kids, Declared r child := by
  obtain ⟨tasks,_,projection,head,ranges⟩ := ordered observed keep
  let prior := (run (demandNames d ++ keep) s tasks).state
  obtain ⟨now,kids,frame,_,_,written,_⟩ :=
    frame_after (s := prior) checked coverage visible role declared (demandNames d ++ keep)
      fallback targets head ranges
  refine ⟨now,kids,frame,trans (trans projection.grows (GeneralDeclarativeGrowth327.facts _ _)) written,?_⟩
  exact read checked coverage visible role declared frame

end Yulang.GeneralDeclarativeStableReplay329
