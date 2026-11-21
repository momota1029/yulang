import Yulang.GeneralDeclarativeAritySource330
import Yulang.GeneralDeclarativeStableReplay329

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeArityCompiler330
open GeneralDeclarations (Checked Clause)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeGrowth327 (Extends trans)
open GeneralDeclarativeStableCompiler329 (Frame read)
open GeneralDeclarativeAritySource330 (Source run ordered)
open GeneralDeclarativeStableInputs329 (demandNames)
open GeneralDeclarativeStableAssemble329 (frame_after)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeNFComplete324 (facts)
open GeneralDeclarativeAssembly320 (Meaning)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralNominalCenteredHeadWFSource (Coverage)

/-- Start from actual source lookups, permitting a checked opaque
endpoint path when covered. No binding or compiler certificate is
in the premises. The returned ordinary state is constructed, not
an assertion that arbitrary runtime or source selections use it. -/
theorem compile {s : State} {d : Demand} {p : Supported s done}
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

end Yulang.GeneralDeclarativeArityCompiler330
