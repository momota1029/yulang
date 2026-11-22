import Yulang.GeneralDeclarativeEndpointInput336
import Yulang.GeneralDeclarativeEndpointBody336
import Yulang.GeneralDeclarativeWitnessClassify334

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEndpointSelected336
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeEndpointOverlay336 (Entry Holds ModelsWith)
open GeneralDeclarativeEndpointInput336 (Inputs Observed sources observed)
open GeneralDeclarativeEndpointBody336 (Body Meaning calculate sound)
open GeneralDeclarativeWitnessHead334 (Slice)
open GeneralDeclarativeGrowth327 (Extends trans restrict)
open GeneralDeclarativeNestedBody332 (compileBody)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativeStableAssemble329 (tieState firsts)
open GeneralDeclarativeStableCanonical329 (EqualUses exact uses_existing)
open GeneralDeclarativePriority321 (Local)
open GeneralDeclarativeInlineEndpoint331 (candidates)
open GeneralDeclarativeUnfinishedRoot330 (UnfinishedRoot)
open GeneralDeclarations (Registry Declaration Clause Checked)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeCurrentReceipt330 (Receipt relays_models)
open GeneralDeclarationPatterns (normalizeArgs variablesArgs)
open CommonRoleOutermostResolver (Frontier All₂)
open GeneralNominalCommonBridge (Assignment)

structure Generated {s : State} (p : Supported s done) (sidecar : List Entry)
    (r : Registry) (i : Interpretation) (d : Demand) (impl : Declaration) (kids : List Demand) where
  slice : Slice p
  protect : List Nat
  fallback : Nat → Capture
  targets : Clause → Nat → Nat
  named : State
  spans : List (Nat × Capture)
  reads : List Entry
  source : Inputs slice.support r.constructors i protect slice.base d.arguments impl.head named spans reads
  ordinary : State
  compiler : compileBody r i d impl named spans protect fallback targets = some (ordinary,kids)
  receipt : Receipt ordinary s
  readback : reads ⊆ sidecar

structure Selected {s : State} (p : Supported s done) (sidecar : List Entry)
    (r : Registry) (i : Interpretation) (waiting : Demand → Declaration → Prop)
    (d : Demand) (impl : Declaration) (kids : List Demand)
    extends Generated p sidecar r i d impl kids where
  chosen : Elected s r i p (candidates p r i waiting) d impl

theorem Generated.body {s : State} {p : Supported s done} (g : Generated p sidecar r i d impl kids)
    (checked : Checked r) (covered : Coverage r i) (wanted : Declared r d)
    (visible : impl ∈ r.declarations) (role : impl.role = d.role) :
    ∃ b : @Body r i d impl g.ordinary kids, b.spans = g.spans ∧ b.targets = g.targets ∧
      Extends (tieState g.named g.spans g.fallback) g.ordinary := by
  obtain ⟨_,atNames,order⟩ := sources g.source (GeneralDeclarativeClauseBatch327.reflexive _)
  obtain ⟨expected,kidsNew,b,compiled,_,spans,targets,_,tied⟩ := calculate checked covered visible role wanted
    g.protect g.fallback g.targets (show g.spans.map Prod.fst = impl.inputNames from order) atNames
  cases Option.some.inj (compiled.symm.trans g.compiler)
  exact ⟨b,spans,targets,tied⟩

/-- Unlike the old literal-record node, the intermediate head proves
approved interval projection at every occurrence; the ordinary body
still has its original children and associated output semantics. -/
structure Node (r : Registry) (i : Interpretation) (m : Assignment) (d : Demand)
    (impl : Declaration) (cap : Nat → Capture) (kids : List Demand) (spans : List (Nat × Capture)) : Prop where
  head : All₂ (Observed r.constructors i m) d.arguments impl.head
  shares : EqualUses m spans
  body : Meaning r i m d impl cap kids

theorem selected_sound {s : State} {p : Supported s done} (w : Selected p sidecar r i waiting d impl kids)
    (checked : Checked r) (covered : Coverage r i) (wanted : Declared r d)
    (m) (fit : ModelsWith s sidecar m) :
    (∃ cap, Node r i m d impl cap kids w.spans) ∧ ∀ child ∈ kids, Declared r child := by
  have visible := w.chosen.viable.1.1
  have role := w.chosen.viable.1.2
  obtain ⟨b,_,_,tied⟩ := w.toGenerated.body checked covered wanted visible role
  have current := relays_models w.receipt m fit.1
  have afterTie := restrict tied m current
  have uses : EqualUses m w.spans :=
    ((exact w.named (firsts w.spans w.fallback) w.spans (uses_existing w.spans w.fallback) m).mp afterTie).2
  have grows := trans (GeneralDeclarativeGrowth327.facts w.named _) tied
  have actual := observed w.source (GeneralDeclarativeClauseBatch327.reflexive _) grows m current
    (fun e selected => fit.2 e (w.readback selected))
  obtain ⟨body,children⟩ := sound b checked covered visible role wanted m current
  exact ⟨⟨_,actual,uses,body⟩,children⟩

/-- Exact I-58 test, *after* selection and naming. A model violating
the selected actual-center equalities is removed at precisely this
append. Sidecar projection does not compare binder centers in probing. -/
theorem ties_exact (s : State) (sidecar : List Entry) (spans : List (Nat × Capture)) (fallback) (m) :
    ModelsWith (tieState s spans fallback) sidecar m ↔
      ModelsWith s sidecar m ∧ EqualUses m spans := by
  have eq := exact s (firsts spans fallback) spans (uses_existing spans fallback) m
  exact ⟨fun h => ⟨⟨(eq.mp h.1).1,h.2⟩,(eq.mp h.1).2⟩,
    fun h => ⟨eq.mpr ⟨h.1.1,h.2⟩,h.1.2⟩⟩

def Clash (before : State) (reads : List Entry) (spans : List (Nat × Capture)) (fallback : Nat → Capture) : Prop :=
  (∃ m, ModelsWith before reads m) ∧ ¬∃ m, ModelsWith (tieState before spans fallback) reads m

theorem clash_exact (before : State) (reads : List Entry) (spans : List (Nat × Capture)) (fallback) :
    Clash before reads spans fallback ↔
    (∃ m, ModelsWith before reads m) ∧ ∀ m, ModelsWith before reads m → ¬EqualUses m spans := by
  constructor
  · rintro ⟨g,no⟩
    exact ⟨g,fun m fit same => no ⟨m,(ties_exact _ _ _ _ _).mpr ⟨fit,same⟩⟩⟩
  · rintro ⟨g,no⟩
    exact ⟨g,fun ⟨m,bad⟩ => let parts := (ties_exact _ _ _ _ _).mp bad; no m parts.1 parts.2⟩

/-- Mixed declarative rule. A contradiction from an actual elected
candidate's computed projected occurrence list is rejection, never an
extra missing-center pending outcome. Other diagnostic completeness
and old Local correspondence are separate. -/
inductive Rule {s : State} (p : Supported s done) (sidecar : List Entry) (r : Registry)
    (i : Interpretation) (waiting : Demand → Declaration → Prop) : Demand → Frontier Demand → Prop where
  | selected : Selected p sidecar r i waiting d impl kids → Rule p sidecar r i waiting d (.selected impl.id kids)
  | existing : Local s r i p (candidates p r i waiting) (fun _ _ _ => False) d result →
      Rule p sidecar r i waiting d result
  | rootK2 : UnfinishedRoot p d → Rule p sidecar r i waiting d .rejected
  | tieClash {slice : Slice p} :
      Elected s r i p (candidates p r i waiting) d impl →
      Inputs slice.support r.constructors i keep slice.base d.arguments impl.head named spans reads →
      Clash named reads spans fallback → Rule p sidecar r i waiting d .rejected

theorem selected_witness {s : State} {p : Supported s done}
    (verdict : Rule p sidecar r i waiting d (.selected key kids)) :
    ∃ impl, impl.id = key ∧ Nonempty (Selected p sidecar r i waiting d impl kids) := by
  cases verdict with
  | selected w => exact ⟨_,rfl,⟨w⟩⟩
  | existing old =>
    obtain ⟨_,_,_,no⟩ := GeneralDeclarativePriority321.selected_generated old
    exact no.elim

end Yulang.GeneralDeclarativeEndpointSelected336
