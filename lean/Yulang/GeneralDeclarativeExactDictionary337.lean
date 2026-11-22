import Yulang.GeneralDeclarativeExactOverlay337
import Yulang.GeneralDeclarativeEndpointDictionary336

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeExactDictionary337
open GeneralDeclarations (Registry Declaration Checked)
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeDemand320 (Demand bounds_sound)
open GeneralDeclarativeWhere319 (Capture InInterval)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeEndpointOverlay336 (Entry)
open GeneralDeclarativeExactOverlay337 (Holds ModelsExact)
open GeneralDeclarativeEndpointInput336 (Inputs RecordRecipe input sources shape_grows)
open GeneralDeclarativeGrowth327 (Extends trans restrict)
open GeneralDeclarativeEndpointSelected336 (Selected)
open GeneralDeclarativeEndpointBody336 (Meaning)
open GeneralDeclarativeEndpointRecord336 (interp)
open GeneralDeclarativeCurrentReceipt330 (relays_models)
open GeneralDeclarativeEqualities322 (semantic)
open GeneralDeclarativeOpaqueNested328 (occurrences)
open GeneralDeclarativeTermWalk322 (Walk)
open GeneralDeclarativeStableCanonical329 (EqualUses exact uses_existing)
open GeneralDeclarativeStableAssemble329 (tieState firsts)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativePriority321 (Local)
open GeneralDeclarativeUnfinishedRoot330 (UnfinishedRoot)
open GeneralDeclarativeInlineEndpoint331 (candidates)
open GeneralDeclarativeStableAttempt329 (Elected)
open GeneralDeclarativeWitnessHead334 (Slice)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarationPatterns (Constructors Pattern normalize)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralNominalCenteredHeadWFSource (Coverage)
open CommonNominalFullCarrier (Equivalent)
open CommonRoleOutermostResolver (Frontier Tree Dictionary Classify Resolves Summarizes All₂ Result)

inductive Observed (c : Constructors) (i : Interpretation) (m : Assignment) : Capture → Pattern → Prop where
  | literal : InInterval (m a.lower).1 (m a.upper).1 (m a.center).1 →
    translate c i (normalize pat) = some code → Equivalent (m a.center).1 (interp m target) →
    Walk .actual target code (occurrences used) →
    Observed c i m a pat
  | record : InInterval (m a.lower).1 (m a.upper).1 (m a.center).1 →
    RecordRecipe a pat used reads → (∀ e ∈ reads, Holds m e) →
    Observed c i m a pat

theorem observed {s before : State} {p : Supported s done}
    (seen : Inputs p c i keep before args pats after used reads)
    (old : Extends s before) (current : Extends after t) (m) (fit : Models t m)
    (exactReads : ∀ e ∈ reads, Holds m e) :
    All₂ (Observed c i m) args pats := by
  induction seen with
  | nil => exact .nil
  | cons one more ih =>
    obtain ⟨step,shape,_,_⟩ := input one old
    have remain := (sources more (trans old step)).1
    have currentShape := shape_grows (trans remain current) shape
    refine .cons ?_ (ih (trans old step) current (fun e had => exactReads e (List.mem_append_right _ had)))
    rcases currentShape.form with ⟨target,code,someCode,actual,walk,none⟩|recipe
    · exact .literal (bounds_sound currentShape.range m fit) someCode (semantic actual m fit) walk
    · exact .record (bounds_sound currentShape.range m fit) recipe
        (fun e had => exactReads e (List.mem_append_left _ had))

theorem ties_exact (s : State) (reads : List Entry) (spans : List (Nat × Capture))
    (fallback : Nat → Capture) (m) :
    ModelsExact (tieState s spans fallback) reads m ↔
      ModelsExact s reads m ∧ EqualUses m spans := by
  have err := exact s (firsts spans fallback) spans (uses_existing spans fallback) m
  exact ⟨fun h => ⟨⟨(err.mp h.1).1,h.2⟩,(err.mp h.1).2⟩,
    fun h => ⟨err.mpr ⟨h.1.1,h.2⟩,h.1.2⟩⟩

structure Node (r : Registry) (i : Interpretation) (m : Assignment) (d : Demand)
    (impl : Declaration) (cap : Nat → Capture) (kids : List Demand) (spans : List (Nat × Capture)) : Prop where
  head : All₂ (Observed r.constructors i m) d.arguments impl.head
  body : Meaning r i m d impl cap kids
  shares : EqualUses m spans
  links : ∀ x ∈ spans, Equivalent (m x.2.center).1 (m (cap x.1).center).1

theorem local_sound {s : State} {p : Supported s done} (w : Selected p sidecar r i waiting d impl kids)
    (checked : Checked r) (covered : Coverage r i) (wanted : Declared r d)
    (m) (fit : ModelsExact s sidecar m) :
    (∃ capture, Node r i m d impl capture kids w.spans) ∧ ∀ child ∈ kids, Declared r child := by
  have visible := w.chosen.viable.1.1
  have role := w.chosen.viable.1.2
  obtain ⟨b,sameSpans,_,tied⟩ := w.toGenerated.body checked covered wanted visible role
  have current := relays_models w.receipt m fit.1
  have shares := ((ties_exact w.named sidecar w.spans w.fallback m).mp ⟨restrict tied m current,fit.2⟩).2
  have grows := trans (GeneralDeclarativeGrowth327.facts w.named _) tied
  have actual := observed w.source (GeneralDeclarativeClauseBatch327.reflexive _) grows m current
    (fun e selected => fit.2 e (w.readback selected))
  obtain ⟨body,children⟩ := GeneralDeclarativeEndpointBody336.sound b checked covered visible role wanted m current
  refine ⟨⟨b.capture,actual,body,shares,?_⟩,children⟩
  intro x member
  have use : GeneralDeclarativeStableTies329.pairOf x ∈ b.spans.map GeneralDeclarativeStableTies329.pairOf :=
    List.mem_map.mpr ⟨x,sameSpans.symm ▸ member,rfl⟩
  have linked := GeneralDeclarativeStableTies329.from_use b.tied use m current
  have visibleName : x.1 ∈ impl.inputNames := by
    rw [GeneralDeclarations.Declaration.inputNames,
      ← (sources w.source (GeneralDeclarativeClauseBatch327.reflexive _)).2.2]
    exact List.mem_map.mpr ⟨x,member,rfl⟩
  unfold GeneralDeclarativeEndpointBody336.Body.capture GeneralDeclarativeFrameReadback325.sourceNames
  rw [GeneralDeclarativeProducedNames325.exact_input (checked.2 impl visible) visibleName]
  exact linked

def Clash (s : State) (reads : List Entry) (used : List (Nat × Capture)) (fallback : Nat → Capture) : Prop :=
  (∃ m, ModelsExact s reads m) ∧ ¬∃ m, ModelsExact (tieState s used fallback) reads m

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

def LocalNode (r : Registry) (i : Interpretation) (m : Assignment) (d : Demand) (key : Nat)
    (kids : List Demand) : Prop :=
  ∃ impl cap spans, impl.id = key ∧ Node r i m d impl cap kids spans

inductive Evidence (r : Registry) (i : Interpretation) (m : Assignment) : Demand → Dictionary → Prop where
  | node : LocalNode r i m d key kids → All₂ (Evidence r i m) kids entries →
      Evidence r i m d (.node key entries)

section
variable {r : Registry} {i : Interpretation} {s : State} {p : Supported s done} {m : Assignment}
  {waiting : Demand → Declaration → Prop}
mutual
theorem tree_sound (checked : Checked r) (covered : Coverage r i) (fit : ModelsExact s sidecar m)
    (d : Demand) (wanted : Declared r d) (diag : Tree) (dict : Dictionary)
    (steps : Resolves (Rule p sidecar r i waiting) d diag)
    (returned : Summarizes diag (.selected dict)) : Evidence r i m d dict := by
  cases steps with
  | pending _ => cases returned
  | rejected _ => cases returned
  | ambiguous _ => cases returned
  | selected candidate all =>
    obtain ⟨impl,_,⟨choice⟩⟩ := selected_witness candidate
    obtain ⟨⟨cap,actual⟩,children⟩ := local_sound choice checked covered wanted m fit
    cases returned with
    | selected allReturned merged =>
      cases merged with
      | selected childMatch =>
        subst_vars
        exact .node ⟨impl,cap,choice.spans,rfl,actual⟩
          (forest_sound checked covered fit _ children _ _ all allReturned)
termination_by sizeOf diag

theorem forest_sound (checked : Checked r) (covered : Coverage r i) (fit : ModelsExact s sidecar m)
    (ds : List Demand) (wanted : ∀ child ∈ ds, Declared r child) (diags : List Tree) (dicts : List Dictionary)
    (steps : All₂ (Resolves (Rule p sidecar r i waiting)) ds diags)
    (returned : All₂ Summarizes diags (dicts.map Result.selected)) : All₂ (Evidence r i m) ds dicts := by
  cases dicts with
  | nil => cases returned; cases steps; exact .nil
  | cons one rest =>
    cases returned with
    | cons first last =>
      cases steps with
      | cons item after =>
        exact .cons (tree_sound checked covered fit _ (wanted _ List.mem_cons_self) _ _ item first)
          (forest_sound checked covered fit _ (fun _ used => wanted _ (List.mem_cons_of_mem _ used))
            _ _ after last)
termination_by sizeOf diags
end

theorem dictionary_sound (checked : Checked r) (covered : Coverage r i) (wanted : Declared r d)
    (accepted : Classify (Rule p sidecar r i waiting) d (.selected dict)) :
    ∀ m, ModelsExact s sidecar m → Evidence r i m d dict := by
  intro model fit
  obtain ⟨tree,seen,result⟩ := accepted
  exact tree_sound checked covered fit d wanted tree dict seen result
end

end Yulang.GeneralDeclarativeExactDictionary337
