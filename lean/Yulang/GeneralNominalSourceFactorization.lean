import Yulang.GeneralNominalPatersonLineage
import Yulang.GeneralNominalSettledGrowth
import Yulang.GeneralNominalHoleElimination
import Yulang.GeneralNominalSourceFrontier
import Yulang.GeneralNominalSettlementHeight

/-! A finite-instantiation simulation and its numeric consequence.
The contract contains no ancestry, signature-cover, or accessibility bound.
It is an abstract sufficient interface, not a construction of semantic source
readbacks. Its realization from actual refinement remains open. -/
namespace Yulang.GeneralNominalSourceFactorization
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalActualInspectionSteps
open GeneralNominalOriginTerms GeneralNominalSharedEnumeration
open GeneralNominalHoleElimination GeneralNominalPatersonLineage

structure Data (context : GeneralNominalCandidates.Context) where
  start : Inventory
  tests : List GeneralNominalRecursiveInspection.Test
  decode : Expr Nat → List GeneralDeclarationPatterns.Pattern
  holes : start.holes = List.range (GeneralNominalSourceFrontier.frontier context.state).length
  valid : Valid tests start

def inputBound (data : Data context) (depth : Nat) : Nat :=
  (enumerate data.start.holes data.tests depth).foldr (fun term rest => max (mass (data.decode term)) rest) 0

def expressionBound (data : Data context) (depth : Nat) : Nat :=
  (enumerate data.start.holes data.tests depth).foldr
    (fun term rest => max (GeneralNominalRecipeBounds.weight term) rest) 0

def templateBound (registry : Registry) (context : GeneralNominalCandidates.Context) : Nat :=
  GeneralNominalRecipeBounds.treeBound (GeneralNominalSchemaBudget.registryBudget context registry)
    (GeneralNominalSchemaBudget.registryBudget context registry)

def replacementBound (registry : Registry) (data : Data context) (depth : Nat) : Nat :=
  GeneralNominalSettledGrowth.growth (templateBound registry context) (expressionBound data depth)
    (inputBound data depth + 1)

theorem expression_bounded (data : Data context)
    (member : term ∈ enumerate data.start.holes data.tests depth) :
    GeneralNominalRecipeBounds.weight term ≤ expressionBound data depth := by
  have general (terms : List (Expr Nat)) (member : term ∈ terms) :
      GeneralNominalRecipeBounds.weight term ≤ terms.foldr
        (fun term rest => max (GeneralNominalRecipeBounds.weight term) rest) 0 := by
    induction terms with
    | nil => cases member
    | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_max_left ..
      · exact Nat.le_trans (ih member) (Nat.le_max_right ..)
  exact general _ member

/-- Conversion from a finite assembly to the exact bound used by elimination.
The assembly and its height are premises, not extracted from settlement here. -/
theorem assembled_replacement (data : Data context)
    (assembled : GeneralNominalSettledGrowth.Assembly (templateBound registry context)
      (expressionBound data depth) height term)
    (heightBound : height ≤ inputBound data depth + 1)
    (vocabulary : Bounded holes data.tests localDepth term) :
    Bounded holes data.tests (replacementBound registry data depth) term := by
  have positive : 0 < templateBound registry context := GeneralNominalRecipeBounds.treeBound_pos ..
  have weight := GeneralNominalSettledGrowth.assembly_bound assembled positive
  have bound := GeneralNominalSettledGrowth.growth_mono positive (expressionBound data depth) heightBound
  exact bounded_mono (GeneralNominalRecipeBounds.weight_depth vocabulary) (Nat.le_trans weight bound)

structure Realized (data : Data context) (root : Occurrence roles) (state : Tracked roles) (inventory : Inventory) where
  labels : Occurrence roles → List GeneralDeclarationPatterns.Pattern
  rootTerm : Expr Nat
  rootMember : rootTerm ∈ inventory.terms
  rootExact : GeneralDeclarationPatterns.counted (labels root) =
    GeneralDeclarationPatterns.counted (data.decode rootTerm)
  packets : ∀ packet ∈ state.current.packets, Nonempty (Instantiation labels packet)
  aliases : GeneralNominalSettlementHeight.AliasMass state.current labels

/-- One source producer obligation. An observation may use the empty trace;
a refinement must delete existing holes and substitute globally. Neither new
numeric IDs nor new observations themselves become extra source holes. -/
structure Producer (registry : Registry) (context : GeneralNominalCandidates.Context) (root : Occurrence roles) where
  data : Data context
  invariant : Tracked roles → Inventory → Prop
  initialInvariant : invariant (GeneralNominalSupport.initial context root) data.start
  initial : Nonempty (Realized data root (GeneralNominalSupport.initial context root) data.start)
  next : ∀ state, B4Target.Steps (Step registry root) (GeneralNominalSupport.initial context root) state →
    ∀ inventory count, Trace data.tests (replacementBound registry data) data.start inventory count →
    invariant state inventory → Realized data root state inventory → ∀ after, Step registry root state after →
    ∃ nextInventory additions,
      Trace data.tests (replacementBound registry data) inventory nextInventory additions ∧
      invariant after nextInventory ∧ Nonempty (Realized data root after nextInventory)

theorem trace_trans (first : Trace tests growth before middle n) (last : Trace tests growth middle after m) :
    Trace tests growth before after (n+m) := by
  induction first with
  | refl => simpa only [Nat.zero_add] using last
  | next hole value present closed bounded trace ih =>
    simpa only [Nat.add_assoc,Nat.add_comm 1 m] using
      Trace.next hole value present closed bounded (ih last)

theorem replay (producer : Producer registry context (root : Occurrence roles))
    (path : B4Target.Steps (Step registry root) (GeneralNominalSupport.initial context root) state) :
    ∃ inventory count, Trace producer.data.tests (replacementBound registry producer.data)
      producer.data.start inventory count ∧ producer.invariant state inventory ∧
      Nonempty (Realized producer.data root state inventory) := by
  induction path with
  | refl => exact ⟨producer.data.start,0,.refl _,producer.initialInvariant,producer.initial⟩
  | @tail before after path step ih =>
    obtain ⟨inventory,count,trace,invariant,⟨realized⟩⟩ := ih
    obtain ⟨nextInventory,additions,updated,next⟩ := producer.next before path inventory count trace invariant realized after step
    exact ⟨nextInventory,count+additions,trace_trans trace updated,next⟩

def depthBudget (registry : Registry) (data : Data context) : Nat :=
  budget (replacementBound registry data) data.start.holes.length data.start.depth

def invocationBudget (registry : Registry) (data : Data context) : Nat :=
  inputBound data (depthBudget registry data)

theorem enumerated_mass (data : Data context)
    (member : term ∈ enumerate data.start.holes data.tests depth) : mass (data.decode term) ≤ inputBound data depth := by
  have general (terms : List (Expr Nat)) (member : term ∈ terms) :
      mass (data.decode term) ≤ terms.foldr (fun term rest => max (mass (data.decode term)) rest) 0 := by
    induction terms with
    | nil => cases member
    | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_max_left ..
      · exact Nat.le_trans (ih member) (Nat.le_max_right ..)
  exact general _ member

theorem root_budget (trace : Trace data.tests (replacementBound registry data) data.start inventory count)
    (realized : Realized data root state inventory) :
    count ≤ data.start.holes.length ∧ mass (realized.labels root) ≤ invocationBudget registry data := by
  have result := conditional_budget trace data.valid
  refine ⟨result.1,?_⟩
  have member := result.2.2 realized.rootTerm realized.rootMember
  have bound := enumerated_mass data member
  unfold mass
  rw [realized.rootExact]
  exact bound

theorem installed_depth_bound (producer : Producer registry context (root : Occurrence roles))
    (source : GeneralNominalSourceFormation.InitialSource registry context root) :
    GeneralNominalInvocationAncestry.InstalledDepthBound registry context root
      (invocationBudget registry producer.data) := by
  intro state path packet support generated enabled novel guard
  obtain ⟨inventory,count,trace,_,⟨realized⟩⟩ := replay producer path
  obtain ⟨depth,ancestry,bounded⟩ := reachable_depth source path realized.labels realized.packets packet.site enabled.1.2.2.1
  have rootBound := (root_budget trace realized).2
  exact ⟨depth,by omega,ancestry⟩

theorem accessible (producer : Producer registry context (root : Occurrence roles))
    (checked : Checked registry) (source : GeneralNominalSourceFormation.InitialSource registry context root) :
    Acc (fun next current => Step registry root current next) (GeneralNominalSupport.initial context root) :=
  GeneralNominalActualBudget.accessible_of_installed_depth_bound checked source (installed_depth_bound producer source)

def ClassPProducer (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, Checked registry → ∀ context (root : Occurrence roles),
    GeneralNominalSourceFormation.InitialSource registry context root →
    GeneralNominalActualBudget.PointSource context root → Nonempty (Producer registry context root)

theorem class_p_invocation_bound (produced : ClassPProducer roles) : GeneralNominalActualBudget.ClassPInvocationBound roles := by
  intro registry checked context root source point
  obtain ⟨producer⟩ := produced registry checked context root source point
  exact ⟨invocationBudget registry producer.data,installed_depth_bound producer source⟩

theorem sourceBudget_of_producer (produced : ClassPProducer roles) : GeneralNominalActualBudget.SourceBudget roles :=
  GeneralNominalActualBudget.sourceBudget_of_invocation_bound (class_p_invocation_bound produced)

theorem class_p_accessible (produced : ClassPProducer roles) (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (point : GeneralNominalActualBudget.PointSource context root) :
    Acc (fun next current => Step registry root current next) (GeneralNominalSupport.initial context root) :=
  GeneralNominalActualBudget.class_p_accessible (class_p_invocation_bound produced) checked source point

end Yulang.GeneralNominalSourceFactorization
