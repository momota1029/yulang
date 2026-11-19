import Yulang.GeneralRebasePhaseKeys281

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
namespace Yulang.GeneralRebasePhaseMachine281
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralRebasePhaseKeys281 (Codec Key Added)
open GeneralRebaseChartStep281 (Chart Recorded)
open GeneralRebaseMixedCounts277 (Actual quietCap)
open GeneralRebaseQuietBound277 (Counted remaining_le)
open GeneralRebaseBoundedInstallAcc277 (accessible_of_bound cap_mono)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable split administrative_plans)
open GeneralNominalFiniteProgress (remaining remaining_monotone remaining_decreases)

def Step (chart : Chart F V) (codec : Codec roles Q) (r : Registry) (root : Occurrence roles)
    (before after : State roles) : Prop :=
  GeneralRebaseChartStep281.Step chart r root before after ∨
    Actual r root before after ∧ Added codec before after

theorem raw (h : Step chart codec r root before after) : Actual r root before after :=
  h.elim And.left And.left

theorem phase_kept (actual : Actual r root before after) (admitsPhase : Added codec before after) :
    Step chart codec r root before after :=
  Or.inr ⟨actual,admitsPhase⟩

theorem ledger_only (h : Step chart codec r root before after)
    (silence : ¬ GeneralRebaseChartStep281.Step chart r root before after) :
    Added codec before after :=
  (h.resolve_left silence).2

theorem uncount {start finish : State roles} {chart : Chart F V} {codec : Codec roles Q}
    (trace : Counted (Step chart codec r root) start n finish) :
    Counted (Actual r root) start n finish := by
  induction trace with
  | nil => exact .nil
  | tail _ step ih => exact .tail ih (raw step)

noncomputable def budget (chart : Chart F V) (codec : Codec roles Q)
    (edges : List (Nat × Nat)) (phases : List (Key Q)) (s : State roles) : Nat :=
  remaining (Recorded chart) chart.facts s +
   remaining GeneralRebaseProjectedEdgeCount279.Seen edges s +
   remaining (GeneralRebasePhaseKeys281.Seen codec) phases s

theorem budget_le (chart : Chart F V) (codec : Codec roles Q)
    (edges : List (Nat × Nat)) (phases : List (Key Q)) (s : State roles) :
    budget chart codec edges phases s ≤ chart.facts.length + edges.length + phases.length :=
  Nat.add_le_add (Nat.add_le_add (remaining_le ..) (remaining_le ..)) (remaining_le ..)

theorem trace_budget {r : Registry} {root : Occurrence roles} {start finish : State roles}
    {chart : Chart F V} {codec : Codec roles Q} {edges : List (Nat × Nat)} {phases : List (Key Q)}
    (init : (boundary roles).Initial r root start)
    (edgeCover : ∀ s, B4Target.Steps (Actual r root) start s →
      ∀ edge, GeneralRebaseProjectedEdgeCount279.Seen s edge → edge ∈ edges)
    (phaseCover : ∀ s, B4Target.Steps (Actual r root) start s →
      ∀ key, GeneralRebasePhaseKeys281.Seen codec s key → key ∈ phases)
    (trace : Counted (Step chart codec r root) start n finish) :
    finish.plans.length + budget chart codec edges phases finish ≤
      start.plans.length + budget chart codec edges phases start := by
  induction trace with
  | nil => exact Nat.le_refl _
  | @tail n before after history action ih =>
    let actual := raw action
    let chartUp := GeneralRebaseChartStep281.monotone chart actual
    let graphUp := GeneralRebaseProjectedEdgeCount279.monotone actual
    let phaseUp := GeneralRebasePhaseKeys281.monotone codec actual
    have chartMono := remaining_monotone _ chart.facts chartUp
    have edgesMono := remaining_monotone _ edges graphUp
    have phasesMono := remaining_monotone _ phases phaseUp
    have oldPath := GeneralRebaseWitnessRegressions279.uncount (uncount history)
    have newPath := B4Target.Steps.tail oldPath actual
    have reach : Reachable r root before := ⟨start,init,oldPath⟩
    have only : after.plans.length = before.plans.length ∨
        after.plans.length = before.plans.length + 1 := by
      rcases split reach actual with admin|⟨effect,enabled,novel,rfl⟩
      · exact Or.inl (congrArg List.length (administrative_plans admin))
      · exact Or.inr rfl
    unfold budget at ih ⊢
    rcases only with eq|plus
    · omega
    · rcases action with h|⟨_,added⟩
      · have visible := h.2.resolve_left (by omega)
        rcases visible with ⟨edge,missing,present⟩|⟨fact,listed,missing,held⟩
        · have strict := remaining_decreases _ edges graphUp (edgeCover after newPath edge present) missing present
          omega
        · have strict := remaining_decreases _ chart.facts chartUp listed missing held
          omega
      · obtain ⟨key,missing,present⟩ := added
        have strict := remaining_decreases _ phases phaseUp (phaseCover after newPath key present) missing present
        omega

theorem length_bound {r : Registry} {root : Occurrence roles} {start : State roles}
    (chart : Chart F V) (codec : Codec roles Q) (init : (boundary roles).Initial r root start) :
    ∃ cap : Nat, ∀ s n, Counted (Step chart codec r root) start n s → n ≤ cap := by
  obtain ⟨es,edgeCover⟩ := GeneralRebaseChartBudget281.source_pool init
  obtain ⟨ps,phaseCover⟩ := GeneralRebasePhaseKeys281.finite_seen init codec
  let k := chart.facts.length + es.length + ps.length
  refine ⟨k + (k+1) * quietCap r start k,?_⟩
  intro s n walk
  have sum := trace_budget init edgeCover phaseCover walk
  have initial := budget_le chart codec es ps start
  obtain ⟨j,count,upper⟩ := GeneralRebaseMixedLength277.actual_length
    (⟨start,init,.refl⟩ : Reachable r root start) (uncount walk)
  have small : j ≤ k := by dsimp only [k]; omega
  exact Nat.le_trans upper (Nat.add_le_add small (Nat.mul_le_mul (by omega) (cap_mono j k small)))

theorem accessible {r : Registry} {root : Occurrence roles} {start : State roles}
    (chart : Chart F V) (codec : Codec roles Q) (init : (boundary roles).Initial r root start) :
    Acc (fun after before => Step chart codec r root before after) start := by
  obtain ⟨cap,limit⟩ := length_bound chart codec init
  exact accessible_of_bound _ start cap (fun n s reached => limit s n reached)

end Yulang.GeneralRebasePhaseMachine281
