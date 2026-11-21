import Yulang.GeneralDeclarativeStableCompiler329
import Yulang.GeneralDeclarativeEvidenceFold325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStableSelect329
open GeneralDeclarations (Registry Checked Declaration)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeLowerKnown321 (Ready)
open GeneralDeclarativePriority321 (Candidates Local Survives Blocked Recurs selected_generated)
open GeneralDeclarativeStableCompiler329 (Frame read)
open GeneralDeclarativeStableReads329 (Heads)
open GeneralDeclarativeStableTies329 (pairOf Consequence rows)
open GeneralDeclarativeEvidenceFold325 (LocalWitness same_model)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarativeEntailment320 (appendFacts)
open CommonRoleOutermostResolver (Frontier Classify)

def Generated (s : State) (r : Registry) (i : Interpretation) (d : Demand)
    (impl : Declaration) (kids : List Demand) : Prop :=
  Nonempty (Frame s r i d impl kids)

/-- Controlled error branch for an actually elected candidate's ordinary
center writes. This is proof of a conflict in the candidate's batch;
lacking a proof of a tie is not this error and does not imply pending.
Other combinations of support/K2/ambiguity are not decided here. -/
structure TieClash (s : State) (r : Registry) (i : Interpretation) (d : Demand)
    (impl : Declaration) : Prop where
  witness : ∃ (spans : List (Nat × Capture)) (base : Nat → Capture), Heads s r.constructors i d.arguments impl.head spans ∧
    (∀ key ∈ impl.inputNames, ∃ a, (key,a) ∈ spans ∧ a.center = (base key).center) ∧
    (∃ m, Models s m) ∧ ¬∃ m, Models (appendFacts s (rows base (spans.map pairOf))) m

/-- Proof-facing stable successful fragment of the independent Local
boundary; it uses the existing diagnostic guards. The provision of an
arbitrary stable readback is still a separate source theorem.
For a clash witness see the narrowly scoped predicate below. -/
abbrev Rule (s : State) (r : Registry) (i : Interpretation)
    {done : Nat → Prop} (p : Supported s done) (tests : Candidates) : Demand → Frontier Demand → Prop :=
  Local s r i p tests (Generated s r i)

theorem local_witness {s : State} {p : Supported s done} (checked : Checked r) (coverage : Coverage r i) :
    LocalWitness r i s (Rule s r i p tests) := by
  intro m valid d wanted key children choice
  obtain ⟨impl,id,⟨⟨visible,role⟩,_⟩,⟨frame⟩⟩ := selected_generated choice
  obtain ⟨_,meaning,child⟩ := read checked coverage visible role wanted frame
  exact ⟨⟨impl,frame.capture,id,meaning m valid⟩,child⟩

theorem sound {s : State} {p : Supported s done} (checked : Checked r) (coverage : Coverage r i)
    (wanted : Declared r d) (valid : Models s m)
    (tree : Classify (Rule s r i p tests) d (.selected dict)) : Evidence r i m d dict :=
  same_model (local_witness checked coverage) valid wanted tree

end Yulang.GeneralDeclarativeStableSelect329
