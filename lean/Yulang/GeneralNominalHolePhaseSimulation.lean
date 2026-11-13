import Yulang.GeneralNominalHolePhases
import Yulang.GeneralNominalSourceFactorization

/-! Local symbolic readback suffices for the phase cover. Normalized packet
labels replace raw-template equalities; no alias-height or global growth
bound is part of this sufficient source interface. -/
namespace Yulang.GeneralNominalHolePhaseSimulation
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalActualInspectionSteps GeneralNominalHoleElimination
open GeneralNominalOriginTerms GeneralNominalPatersonLineage
open GeneralNominalPhaseLabels (PacketLabels)

variable {roles : Roles.RoleDecls}
abbrev Data := GeneralNominalSourceFactorization.Data

structure Realized (data : Data context) (root : Occurrence roles) (state : Tracked roles) (inventory : Inventory) where
  labels : Occurrence roles → List Pattern
  rootTerm : Expr Nat
  member : rootTerm ∈ inventory.terms
  rootExact : counted (labels root) = counted (data.decode rootTerm)
  packets : ∀ packet ∈ state.current.packets, Nonempty (PacketLabels labels packet)

def inventoryBound (data : Data context) (inventory : Inventory) : Nat :=
  inventory.terms.foldr (fun term rest => max (mass (data.decode term)) rest) 0

theorem listed_bound (data : Data context) (member : term ∈ inventory.terms) :
    mass (data.decode term) ≤ inventoryBound data inventory := by
  have general (terms : List (Expr Nat)) (member : term ∈ terms) :
      mass (data.decode term) ≤ terms.foldr (fun term rest => max (mass (data.decode term)) rest) 0 := by
    induction terms with
    | nil => cases member
    | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact Nat.le_max_left ..
      · exact Nat.le_trans (ih member) (Nat.le_max_right ..)
  exact general _ member

theorem root_bound (realized : Realized data root state inventory) :
    mass (realized.labels root) ≤ inventoryBound data inventory := by
  have equal := congrArg Roles.argsSize realized.rootExact
  change mass (realized.labels root) = mass (data.decode realized.rootTerm) at equal
  rw [equal]
  exact listed_bound data realized.member

/-- The open source construction. The invariant must interpret shared holes
and actual origins. Every update either retains the inventory or globally
substitutes and deletes existing holes, using the established Trace relation. -/
structure Simulation (registry : Registry) (context : GeneralNominalCandidates.Context) (root : Occurrence roles) where
  data : Data context
  invariant : Tracked roles → Inventory → Prop
  initialInvariant : invariant (GeneralNominalSupport.initial context root) data.start
  initial : Nonempty (Realized data root (GeneralNominalSupport.initial context root) data.start)
  next : ∀ state, B4Target.Steps (Step registry root) (GeneralNominalSupport.initial context root) state →
    ∀ inventory, Valid data.tests inventory → invariant state inventory → Realized data root state inventory →
    ∀ after, Step registry root state after →
      ∃ updated growth count, Trace data.tests growth inventory updated count ∧
        invariant after updated ∧ Nonempty (Realized data root after updated)

def phase_cover (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (simulation : Simulation registry context root) : GeneralNominalHolePhases.PhaseCover registry context root where
  start := simulation.data.start
  tests := simulation.data.tests
  holes := simulation.data.holes
  valid := simulation.data.valid
  invariant := fun state inventory => Valid simulation.data.tests inventory ∧
    simulation.invariant state inventory ∧ Nonempty (Realized simulation.data root state inventory)
  initial := ⟨simulation.data.valid,simulation.initialInvariant,simulation.initial⟩
  basis := fun inventory => GeneralNominalSnapshotCover.signatures checked source (inventoryBound simulation.data inventory)
  next := by
    intro state path inventory ⟨valid,invariant,⟨realized⟩⟩ after step
    obtain ⟨updated,growth,count,trace,next⟩ := simulation.next state path inventory valid invariant realized after step
    exact ⟨updated,growth,count,trace,trace_valid trace valid,next⟩
  covers := by
    intro state path inventory ⟨valid,invariant,⟨realized⟩⟩ packet support generated enabled novel guard
    have parents := GeneralNominalPhaseLabels.parents source path realized.labels realized.packets (root_bound realized)
    exact GeneralNominalSnapshotCover.covers checked source path parents enabled

theorem accessible (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (simulation : Simulation registry context root) :
    Acc (fun next current => Step registry root current next) (GeneralNominalSupport.initial context root) :=
  GeneralNominalHolePhases.accessible (phase_cover checked source simulation) source

/-- If a uniform replacement growth estimate is later obtained, the same
normalized realization also gives the requested iterated numerical bound. -/
theorem fixed_growth_budget (data : Data context)
    (trace : Trace data.tests growth data.start inventory count)
    (realized : Realized data root state inventory) :
    count ≤ data.start.holes.length ∧ mass (realized.labels root) ≤
      GeneralNominalSourceFactorization.inputBound data (budget growth data.start.holes.length data.start.depth) := by
  have result := conditional_budget trace data.valid
  have bound := GeneralNominalSourceFactorization.enumerated_mass data (result.2.2 realized.rootTerm realized.member)
  have equal := congrArg Roles.argsSize realized.rootExact
  change mass (realized.labels root) = mass (data.decode realized.rootTerm) at equal
  exact ⟨result.1,by rw [equal]; exact bound⟩

theorem fixed_growth_parent_depth (data : Data context)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (path : B4Target.Steps (Step registry root) (GeneralNominalSupport.initial context root) state)
    (trace : Trace data.tests growth data.start inventory count)
    (realized : Realized data root state inventory)
    (site : GeneralNominalDemandMerging.Site roles) (member : site ∈ state.current.sites) :
    ∃ depth, depth ≤ GeneralNominalSourceFactorization.inputBound data (budget growth data.start.holes.length data.start.depth) ∧
      GeneralNominalInvocationAncestry.AtDepth registry context.state.seed root.identity depth site.occurrence.identity := by
  obtain ⟨depth,lineage⟩ := sites_lineage source path site member
  have descent := GeneralNominalPhaseLabels.lineage_descent lineage realized.labels realized.packets
  have bound := (fixed_growth_budget data trace realized).2
  exact ⟨depth,by omega,lineage_ancestry lineage⟩

def ClassPHoleReadback (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, Checked registry → ∀ context (root : Occurrence roles),
    GeneralNominalSourceFormation.InitialSource registry context root → GeneralNominalActualBudget.PointSource context root →
      Nonempty (Simulation registry context root)

theorem phases_of_readback (readback : ClassPHoleReadback roles) : GeneralNominalHolePhases.ClassPHolePhases roles := by
  intro registry checked context root source point
  obtain ⟨simulation⟩ := readback registry checked context root source point
  exact ⟨phase_cover checked source simulation⟩

theorem class_p_accessible (readback : ClassPHoleReadback roles) (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (point : GeneralNominalActualBudget.PointSource context root) :
    Acc (fun next current => Step registry root current next) (GeneralNominalSupport.initial context root) :=
  GeneralNominalHolePhases.class_p_accessible (phases_of_readback readback) checked source point

end Yulang.GeneralNominalHolePhaseSimulation
