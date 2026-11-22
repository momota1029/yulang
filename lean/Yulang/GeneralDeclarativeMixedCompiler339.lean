import Yulang.GeneralDeclarativeMixedInputs339
import Yulang.GeneralDeclarativeExactDictionary337

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeMixedCompiler339
open GeneralDeclarations (Registry Declaration Clause Checked)
open GeneralDeclarativeHead320 (State)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeCompoundTree338 (World Span)
open GeneralDeclarativeMixedInputs339 (Inputs Observed input_exact observed)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeGrowth327 (Extends restrict)
open GeneralDeclarativeEndpointOverlay336 (Entry)
open GeneralDeclarativeExactOverlay337 (ModelsExact)
open GeneralDeclarativeEndpointBody336 (Body Meaning calculate sound)
open GeneralDeclarativeWitnessHead334 (Slice)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativeStableAssemble329 (tieState)
open GeneralDeclarativeStableCanonical329 (EqualUses)
open GeneralDeclarativeInlineEndpoint331 (candidates)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarativeCurrentReceipt330 (Receipt relays_models)
open GeneralDeclarativeExactDictionary337 (ties_exact)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Equivalent)
open CommonRoleOutermostResolver (All₂)

/-- Actual ordinary compileBody consumes independent, deep-first
occurrences. Intermediate record layout indices are not impl binders. -/
theorem body_ready {w v : World done} {r : Registry} {d : Demand} {impl : Declaration}
    (source : Inputs r.constructors i keep w d.arguments impl.head v spans)
    (checked : Checked r) (covered : Coverage r i) (visible : impl ∈ r.declarations)
    (role : impl.role = d.role) (wanted : Declared r d) (fallback) (targets) :
    ∃ ordinary kids, ∃ body : @Body r i d impl ordinary kids,
      compileBody r i d impl v.state spans keep fallback targets = some (ordinary,kids) ∧
      body.spans = spans ∧ body.targets = targets ∧ Extends (tieState v.state spans fallback) ordinary := by
  obtain ⟨_,ordered,bounds⟩ := input_exact source
  obtain ⟨out,kids,body,compiled,_,routes,fixed,_,grown⟩ := calculate checked covered visible role wanted
    keep fallback targets (show spans.map Prod.fst = impl.inputNames from ordered) bounds
  exact ⟨out,kids,body,compiled,routes,fixed,grown⟩

def rootWorld {s : State} {p : Supported s done} (slice : Slice p) (seed : List Entry) : World done :=
  ⟨slice.base,slice.support,seed⟩

structure Selected {s : State} (p : Supported s done) (sidecar : List Entry)
    (r : Registry) (i : Interpretation) (waiting : Demand → Declaration → Prop)
    (d : Demand) (impl : Declaration) (kids : List Demand) where
  slice : Slice p
  seed : List Entry
  keep : List Nat
  named : World done
  spans : List Span
  inputs : Inputs r.constructors i keep (rootWorld slice seed) d.arguments impl.head named spans
  fallback : Nat → Capture
  targets : Clause → Nat → Nat
  ordinary : State
  compiler : compileBody r i d impl named.state spans keep fallback targets = some (ordinary,kids)
  receipt : Receipt ordinary s
  retained : named.reads ⊆ sidecar
  chosen : Elected s r i p (candidates p r i waiting) d impl

theorem read_back {s : State} {p : Supported s done}
    (w : Selected p sidecar r i waiting d impl kids)
    (checked : Checked r) (covered : Coverage r i) (wanted : Declared r d) :
    ∃ body : @Body r i d impl w.ordinary kids, body.spans = w.spans ∧ body.targets = w.targets ∧
      Extends (tieState w.named.state w.spans w.fallback) w.ordinary := by
  have viable := w.chosen.viable
  obtain ⟨_,_,body,equation,sameSpans,sameTargets,grown⟩ :=
    body_ready (d := d) (impl := impl) w.inputs checked covered viable.1.1 viable.1.2 wanted w.fallback w.targets
  cases Option.some.inj (equation.symm.trans w.compiler)
  exact ⟨body,sameSpans,sameTargets,grown⟩

structure Node (r : Registry) (i : Interpretation) (m : Assignment) (d : Demand)
    (impl : Declaration) (cap : Nat → Capture) (kids : List Demand) (spans : List Span) : Prop where
  head : All₂ (Observed r.constructors i m) d.arguments impl.head
  body : Meaning r i m d impl cap kids
  shares : EqualUses m spans
  actual : ∀ x ∈ spans, Equivalent (m x.2.center).1 (m (cap x.1).center).1

theorem selected_sound {s : State} {p : Supported s done}
    (w : Selected p sidecar r i waiting d impl kids)
    (checked : Checked r) (covered : Coverage r i) (wanted : Declared r d)
    (m) (fit : ModelsExact s sidecar m) :
    (∃ cap, Node r i m d impl cap kids w.spans) ∧ ∀ child ∈ kids, Declared r child := by
  obtain ⟨b,sameSpans,_,grown⟩ := read_back w checked covered wanted
  have fitOrdinary := relays_models w.receipt m fit.1
  have tied : ModelsExact (tieState w.named.state w.spans w.fallback) w.named.reads m :=
    ⟨restrict grown m fitOrdinary,fun e used => fit.2 e (w.retained used)⟩
  obtain ⟨fitNamed,shared⟩ := (ties_exact w.named.state w.named.reads w.spans w.fallback m).mp tied
  have visible := w.chosen.viable.1.1
  have role := w.chosen.viable.1.2
  obtain ⟨body,children⟩ := sound b checked covered visible role wanted m fitOrdinary
  refine ⟨⟨b.capture,observed w.inputs m fitNamed,body,shared,?_⟩,children⟩
  intro x used
  have selected : GeneralDeclarativeStableTies329.pairOf x ∈ b.spans.map GeneralDeclarativeStableTies329.pairOf :=
    List.mem_map.mpr ⟨x,sameSpans.symm ▸ used,rfl⟩
  have same := GeneralDeclarativeStableTies329.from_use b.tied selected m fitOrdinary
  have inNames : x.1 ∈ impl.inputNames := by
    rw [GeneralDeclarations.Declaration.inputNames,← (input_exact w.inputs).2.1]
    exact List.mem_map.mpr ⟨x,used,rfl⟩
  unfold GeneralDeclarativeEndpointBody336.Body.capture GeneralDeclarativeFrameReadback325.sourceNames
  rw [GeneralDeclarativeProducedNames325.exact_input (checked.2 impl visible) inNames]
  exact same

end Yulang.GeneralDeclarativeMixedCompiler339
