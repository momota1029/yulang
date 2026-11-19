import Yulang.GeneralRebaseChartStep281

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
namespace Yulang.GeneralRebaseChartBudget281
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralRebaseMixedCounts277 (Actual quietCap)
open GeneralRebaseProjectedEdgeCount279 (Seen Fresh)
open GeneralRebaseChartStep281 (Chart Recorded Step uncount)
open GeneralRebaseQuietBound277 (Counted remaining_le)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable split reachable_step administrative_plans)
open GeneralNominalFiniteProgress (remaining remaining_monotone remaining_decreases)
open GeneralRebaseSourceEdgeBasis279 (project finite_projected_edges)
open GeneralRebaseBoundedInstallAcc277 (bounded_steps accessible_of_bound)
open GeneralRebaseSemanticChart281 (Gain)

noncomputable def Budget (chart : Chart F V) (edges : List (Nat × Nat)) (s : State roles) : Nat :=
  remaining (Recorded chart) chart.facts s + remaining Seen edges s

theorem budget_le (chart : Chart F V) (edges : List (Nat × Nat)) (s : State roles) :
    Budget chart edges s ≤ chart.facts.length + edges.length := by
  exact Nat.add_le_add (remaining_le ..) (remaining_le ..)

theorem state_budget {r : Registry} {root : Occurrence roles} {start finish : State roles}
    {chart : Chart F V} {keys : List (Nat × Nat)}
    (origin : (boundary roles).Initial r root start)
    (covered : ∀ s, B4Target.Steps (Actual r root) start s → ∀ e, Seen s e → e ∈ keys)
    (walk : Counted (Step chart r root) start n finish) :
    finish.plans.length + Budget chart keys finish ≤ start.plans.length + Budget chart keys start := by
  induction walk with
  | nil => exact Nat.le_refl _
  | @tail n before after history step ih =>
    have chartMono := remaining_monotone (Recorded chart) chart.facts (GeneralRebaseChartStep281.monotone chart step.1)
    have graphMono := remaining_monotone Seen keys (GeneralRebaseProjectedEdgeCount279.monotone step.1)
    have oldPath := GeneralRebaseWitnessRegressions279.uncount (uncount history)
    have reached : Reachable r root before := ⟨start,origin,oldPath⟩
    have balanced : after.plans.length = before.plans.length ∨
        after.plans.length = before.plans.length + 1 := by
      rcases split reached step.1 with quiet|⟨effect,ready,novel,rfl⟩
      · exact Or.inl (congrArg List.length (administrative_plans quiet))
      · exact Or.inr rfl
    rcases balanced with quiet | added
    · unfold Budget at ih ⊢
      omega
    · have strict := step.2.resolve_left (by omega)
      rcases strict with ⟨edge,wasMissing,isSeen⟩ | ⟨fact,inPool,wasMissing,nowHeld⟩
      · have known := covered after (.tail oldPath step.1) edge isSeen
        have falls := remaining_decreases Seen keys (GeneralRebaseProjectedEdgeCount279.monotone step.1) known wasMissing isSeen
        unfold Budget at ih ⊢
        omega
      · have falls := remaining_decreases (Recorded chart) chart.facts (GeneralRebaseChartStep281.monotone chart step.1)
          inPool wasMissing nowHeld
        unfold Budget at ih ⊢
        omega

theorem source_pool {r : Registry} {root : Occurrence roles} {start : State roles}
    (origin : (boundary roles).Initial r root start) :
    ∃ keys : List (Nat × Nat), ∀ s, B4Target.Steps (Actual r root) start s →
      ∀ e, Seen s e → e ∈ keys := by
  obtain ⟨keys,cover⟩ := finite_projected_edges origin
  refine ⟨keys,?_⟩
  intro s path edge seen
  obtain ⟨raw,stored,rfl⟩ := List.mem_map.mp seen
  exact cover s path raw stored

theorem max_steps {r : Registry} {root : Occurrence roles} {start : State roles}
    (chart : Chart F V) (origin : (boundary roles).Initial r root start) :
    ∃ cap : Nat, ∀ s n, Counted (Step chart r root) start n s → n ≤ cap := by
  obtain ⟨keys,cover⟩ := source_pool origin
  let k := chart.facts.length + keys.length
  refine ⟨k + (k+1) * quietCap r start k,?_⟩
  intro finish n walk
  have only : ∀ n done, Counted (Step chart r root) start n done →
      done.plans.length ≤ start.plans.length + k := by
    intro n done trace
    have h := state_budget origin cover trace
    have wide := budget_le chart keys start
    dsimp only [k]
    omega
  -- The existing raw-length estimate uses the bound for this trace prefix,
  -- not a full raw accessibility assertion.
  obtain ⟨j,recorded,upper⟩ := GeneralRebaseMixedLength277.actual_length
    (⟨start,origin,.refl⟩ : Reachable r root start) (uncount walk)
  have small : j ≤ k := by have max := only n finish walk; omega
  exact Nat.le_trans upper (Nat.add_le_add small
    (Nat.mul_le_mul (by omega) (GeneralRebaseBoundedInstallAcc277.cap_mono j k small)))

theorem accessible {r : Registry} {root : Occurrence roles} {start : State roles}
    (chart : Chart F V) (origin : (boundary roles).Initial r root start) :
    Acc (fun after before => Step chart r root before after) start := by
  obtain ⟨cap,limit⟩ := max_steps chart origin
  exact accessible_of_bound _ start cap fun n s reached => limit s n reached

end Yulang.GeneralRebaseChartBudget281
