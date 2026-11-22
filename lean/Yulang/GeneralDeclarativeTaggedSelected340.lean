import Yulang.GeneralDeclarativeTaggedElection340

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTaggedSelected340
open GeneralDeclarations (Registry Declaration Checked Clause)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeTaggedInputs340 (Inputs complete observed)
open GeneralDeclarativeExactDictionary337 (Node ties_exact)
open GeneralDeclarativeWitnessHead334 (Slice)
open GeneralDeclarativeEndpointBody336 (Body calculate sound)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeEndpointOverlay336 (Entry)
open GeneralDeclarativeExactOverlay337 (ModelsExact)
open GeneralDeclarativeCurrentReceipt330 (Receipt relays_models)
open GeneralDeclarativeTaggedElection340 (Election)
open GeneralDeclarativeInlineEndpoint331 (candidates)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarativeStableAssemble329 (tieState)
open GeneralDeclarativeGrowth327 (Extends restrict trans facts)
open GeneralDeclarativeClauseBatch327 (reflexive)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCommonBridge (Assignment)

/-- Positive certificate only. The independent source election gives
visibility/unique candidate, not current typed captures or receipts. -/
structure Selected {s : State} (p : Supported s done) (sidecar : List Entry)
    (r : Registry) (i : Interpretation) (waiting : Demand → Declaration → Prop)
    (d : Demand) (impl : Declaration) (kids : List Demand) where
  slice : Slice p
  keep : List Nat
  named : State
  spans : List (Nat × Capture)
  reads : List Entry
  input : Inputs slice.support r.constructors i keep slice.base d.arguments impl.head named spans reads
  fallback : Nat → Capture
  targets : Clause → Nat → Nat
  ordinary : State
  compiler : compileBody r i d impl named spans keep fallback targets = some (ordinary,kids)
  receipt : Receipt ordinary s
  retained : reads ⊆ sidecar
  elected : Election p r i waiting d impl

theorem reconstruct {s : State} {p : Supported s done}
    (chosen : Selected p sidecar r i waiting d impl kids)
    (checked : Checked r) (covered : Coverage r i) (wanted : Declared r d) :
    ∃ b : @Body r i d impl chosen.ordinary kids,
      b.spans = chosen.spans ∧ b.targets = chosen.targets ∧
      Extends (tieState chosen.named chosen.spans chosen.fallback) chosen.ordinary := by
  obtain ⟨_,fits,ordered⟩ := complete chosen.input (reflexive _)
  obtain ⟨ordinary,children,b,computed,_,names,targets,_,growth⟩ :=
    calculate checked covered chosen.elected.viable.1.1 chosen.elected.viable.1.2 wanted
      chosen.keep chosen.fallback chosen.targets (show chosen.spans.map Prod.fst = impl.inputNames from ordered) fits
  cases Option.some.inj (computed.symm.trans chosen.compiler)
  exact ⟨b,names,targets,growth⟩

theorem local_sound {s : State} {p : Supported s done}
    (chosen : Selected p sidecar r i waiting d impl kids)
    (checked : Checked r) (covered : Coverage r i) (wanted : Declared r d)
    (m : Assignment) (fit : ModelsExact s sidecar m) :
    (∃ cap, Node r i m d impl cap kids chosen.spans) ∧ ∀ child ∈ kids, Declared r child := by
  obtain ⟨b,names,_,growth⟩ := reconstruct chosen checked covered wanted
  have current := relays_models chosen.receipt m fit.1
  have named := (ties_exact chosen.named chosen.reads chosen.spans chosen.fallback m).mp
    ⟨restrict growth m current,fun e used => fit.2 e (chosen.retained used)⟩
  have physical := trans (facts chosen.named _) growth
  have head := observed chosen.input (reflexive _) physical m current (fun e h => fit.2 e (chosen.retained h))
  have visible := chosen.elected.viable.1.1
  obtain ⟨body,children⟩ := sound b checked covered visible chosen.elected.viable.1.2 wanted m current
  refine ⟨⟨b.capture,head,body,named.2,?_⟩,children⟩
  intro x used
  have placed : GeneralDeclarativeStableTies329.pairOf x ∈ b.spans.map GeneralDeclarativeStableTies329.pairOf :=
    List.mem_map.mpr ⟨x,names.symm ▸ used,rfl⟩
  have linked := GeneralDeclarativeStableTies329.from_use b.tied placed m current
  have declaredName : x.1 ∈ impl.inputNames := by
    rw [GeneralDeclarations.Declaration.inputNames,← (complete chosen.input (reflexive _)).2.2]
    exact List.mem_map.mpr ⟨x,used,rfl⟩
  unfold GeneralDeclarativeEndpointBody336.Body.capture GeneralDeclarativeFrameReadback325.sourceNames
  rw [GeneralDeclarativeProducedNames325.exact_input (checked.2 impl visible) declaredName]
  exact linked

end Yulang.GeneralDeclarativeTaggedSelected340
