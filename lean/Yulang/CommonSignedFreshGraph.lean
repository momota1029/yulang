import Yulang.CommonEffectFreshExpression
import Yulang.CommonSignedGraphSolver

/-! Conservative fresh-coordinate extension of the real finite signed row
graph. Path reflection, computed safety and solver rejection all commute.
Original rows are embedded explicitly; this is not an identification of all
new-scope row parameters with the image of the old-scope embedding. -/
namespace Yulang.CommonSignedFreshGraph
open Common (Occurrence Row)
open CommonEffectFreshRows (liftOccurrence liftRow lift_injective)
open CommonSignedFlowFamily (Action Edge Graph Path Safe)

def action : Action → Action
  | .identity => .identity
  | .shift scope permission delta => .shift (scope + 1) permission delta
  | .residual handled => .residual handled

theorem action_run (original : Action) (occurrence : Occurrence) :
    (action original).run (liftOccurrence occurrence) = (original.run occurrence).map liftOccurrence := by
  cases original with
  | identity => rfl
  | shift scope permission delta =>
    exact congrArg some (CommonEffectFreshRows.lift_shift scope permission delta occurrence).symm
  | residual handled =>
    have captureSame : CommonSignedFlowFamily.captured handled (liftOccurrence occurrence) = CommonSignedFlowFamily.captured handled occurrence := by
      simp [CommonSignedFlowFamily.captured, liftOccurrence]
    simp only [action, Action.run, captureSame]
    split <;> rfl

theorem action_reflect (original : Action) (source target : Occurrence)
    (runs : (action original).run (liftOccurrence source) = some target) :
    ∃ next, original.run source = some next ∧ liftOccurrence next = target := by
  rw [action_run, Option.map_eq_some_iff] at runs
  exact runs

def edge (original : Edge n) : Edge n := ⟨original.source, original.target, action original.action⟩

def graph (original : Graph n) : Graph n := ⟨original.edges.map edge, original.pure⟩

theorem path_lift {original : Graph n} {source target : Fin n} {first last : Occurrence}
    (path : Path original source first target last) :
    Path (graph original) source (liftOccurrence first) target (liftOccurrence last) := by
  induction path with
  | nil => exact .nil _ _
  | @cons originalEdge first next last target member runs rest ih =>
    exact .cons (edge := edge originalEdge) (List.mem_map.mpr ⟨originalEdge, member, rfl⟩)
      (by simp only [edge, action_run, runs, Option.map_some]) ih

theorem path_reflect {original : Graph n} {source target : Fin n} {first last : Occurrence}
    (path : Path (graph original) source first target last) :
    ∀ before, first = liftOccurrence before → ∃ after, last = liftOccurrence after ∧ Path original source before target after := by
  induction path with
  | nil => intro before same; exact ⟨before, same, .nil _ _⟩
  | @cons liftedEdge first next last target member runs rest ih =>
    intro before same
    obtain ⟨originalEdge, originalMember, rfl⟩ := List.mem_map.mp member
    rw [same] at runs
    obtain ⟨middle, originalRun, middleSame⟩ := action_reflect originalEdge.action before next runs
    obtain ⟨after, afterSame, afterPath⟩ := ih middle middleSame.symm
    exact ⟨after, afterSame, .cons originalMember originalRun afterPath⟩

theorem path_exact (original : Graph n) (source target : Fin n) (first last : Occurrence) :
    Path (graph original) source (liftOccurrence first) target (liftOccurrence last) ↔ Path original source first target last := by
  constructor
  · intro path
    obtain ⟨after, same, originalPath⟩ := path_reflect path first rfl
    have equal := lift_injective same
    exact equal ▸ originalPath
  · exact path_lift

theorem safe_exact (original : Graph n) (slot : Fin n) (occurrence : Occurrence) :
    Safe (graph original) slot (liftOccurrence occurrence) ↔ Safe original slot occurrence := by
  constructor
  · intro safe target moved path
    exact safe target (liftOccurrence moved) (path_lift path)
  · intro safe target moved path
    obtain ⟨after, _, originalPath⟩ := path_reflect path occurrence rfl
    exact safe target after originalPath

theorem safety_check (original : Graph n) (slot : Fin n) (occurrence : Occurrence) :
    CommonSignedSafetyDecision.check (graph original) slot (liftOccurrence occurrence) = CommonSignedSafetyDecision.check original slot occurrence := by
  apply Bool.eq_iff_iff.mpr
  rw [CommonSignedSafetyDecision.check_exact, CommonSignedSafetyDecision.check_exact, safe_exact]

theorem models_exact (original : Graph n) (rows : Fin n → Row) :
    CommonSignedFlowFamily.Models (graph original) (fun index => liftRow (rows index)) ↔ CommonSignedFlowFamily.Models original rows := by
  constructor
  · intro model
    constructor
    · intro originalEdge member first last present runs
      obtain ⟨source, accepted, same⟩ := model.1 (edge originalEdge) (List.mem_map.mpr ⟨originalEdge, member, rfl⟩)
        (liftOccurrence first) (liftOccurrence last) ⟨first, present, rfl⟩
        (by simp only [edge, action_run, runs, Option.map_some])
      exact lift_injective same ▸ accepted
    · intro sink member occurrence present
      exact model.2 sink member (liftOccurrence occurrence) ⟨occurrence, present, rfl⟩
  · intro model
    constructor
    · intro liftedEdge member first last present runs
      obtain ⟨originalEdge, originalMember, rfl⟩ := List.mem_map.mp member
      obtain ⟨before, originalPresent, rfl⟩ := present
      obtain ⟨after, originalRun, same⟩ := action_reflect originalEdge.action before last runs
      exact ⟨after, model.1 originalEdge originalMember before after originalPresent originalRun, same⟩
    · rintro sink member occurrence ⟨originalOccurrence, present, _⟩
      exact model.2 sink member originalOccurrence present

def scheme (original : CommonSignedGraphSolver.Scheme n) : CommonSignedGraphSolver.Scheme n :=
  ⟨graph original.graph, original.heads.map (fun head => (head.1, liftOccurrence head.2))⟩

theorem scheme_models_exact (original : CommonSignedGraphSolver.Scheme n) (rows : Fin n → Row) :
    CommonSignedGraphSolver.Models (scheme original) (fun index => liftRow (rows index)) ↔ CommonSignedGraphSolver.Models original rows := by
  change (_ ∧ _) ↔ (_ ∧ _)
  rw [models_exact]
  apply and_congr_right
  intro _
  simp only [scheme, List.forall_mem_map]
  constructor
  · intro included head member
    obtain ⟨source, present, same⟩ := included head member
    exact lift_injective same ▸ present
  · intro included head member
    exact ⟨head.2, included head member, rfl⟩

theorem heads_check (original : CommonSignedGraphSolver.Scheme n) :
    CommonSignedGraphSolver.checkHeads (scheme original) = CommonSignedGraphSolver.checkHeads original := by
  simp only [CommonSignedGraphSolver.checkHeads, scheme, List.all_map, Function.comp_def, safety_check]

theorem solve_lift (original : CommonSignedGraphSolver.Scheme n) :
    CommonSignedGraphSolver.solve (scheme original) = (CommonSignedGraphSolver.solve original).map scheme := by
  simp only [CommonSignedGraphSolver.solve, heads_check]
  cases CommonSignedGraphSolver.checkHeads original <;> rfl

end Yulang.CommonSignedFreshGraph
