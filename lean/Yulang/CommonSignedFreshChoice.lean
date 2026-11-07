import Yulang.CommonSignedFreshGraph
import Yulang.CommonSignedChoiceSolver

/-! Fresh-coordinate extension of finite disjunctive signed row clauses and
their actual parameter-tested routing scheme. The original parameter rows
remain unrestricted; their explicit images are used in the new scope. -/
namespace Yulang.CommonSignedFreshChoice
open Common (Occurrence Row)
open CommonEffectFreshRows (liftOccurrence liftRow lift_injective)
open CommonSignedChoicePreparation (Clause Graph Models Supported)
open CommonSignedChoiceSolver (Problem Reach desired chosen)
open CommonSignedFreshGraph (action action_run action_reflect)

def clause (original : Clause n) : Clause n := ⟨original.source, action original.action, original.targets⟩
def graph (original : Graph n) : Graph n := original.map clause
def image (rows : Fin n → Row) : Fin n → Row := fun index => liftRow (rows index)
def pullback (rows : Fin n → Row) : Fin n → Row := fun index occurrence => rows index (liftOccurrence occurrence)

theorem lift_member (row : Row) (occurrence : Occurrence) : liftRow row (liftOccurrence occurrence) ↔ row occurrence := by
  constructor
  · rintro ⟨source, present, same⟩
    exact lift_injective same ▸ present
  · intro present
    exact ⟨occurrence, present, rfl⟩

theorem pullback_image (rows : Fin n → Row) : pullback (image rows) = rows := by
  funext slot occurrence
  exact propext (lift_member (rows slot) occurrence)

theorem models_pullback (original : Graph n) (rows : Fin n → Row) (model : Models (graph original) rows) :
    Models original (pullback rows) := by
  intro originalClause member source target present runs
  exact model (clause originalClause) (List.mem_map.mpr ⟨originalClause, member, rfl⟩)
    (liftOccurrence source) (liftOccurrence target) present
    (by simp only [clause, action_run, runs, Option.map_some])

theorem models_image (original : Graph n) (rows : Fin n → Row) (model : Models original rows) :
    Models (graph original) (image rows) := by
  intro newClause member source target present runs
  obtain ⟨oldClause, oldMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨before, oldPresent, rfl⟩ := present
  obtain ⟨after, oldRun, same⟩ := action_reflect oldClause.action before target runs
  obtain ⟨slot, listed, accepted⟩ := model oldClause oldMember before after oldPresent oldRun
  exact ⟨slot, listed, after, accepted, same⟩

theorem supported_exact (original : Graph n) (slot : Fin n) (occurrence : Occurrence) :
    Supported (graph original) slot (liftOccurrence occurrence) ↔ Supported original slot occurrence := by
  constructor
  · rintro ⟨rows, model, present⟩
    exact ⟨pullback rows, models_pullback original rows model, present⟩
  · rintro ⟨rows, model, present⟩
    exact ⟨image rows, models_image original rows model, occurrence, present, rfl⟩

theorem safety_check (original : Graph n) (slot : Fin n) (occurrence : Occurrence) :
    CommonSignedChoiceDecision.check (graph original) slot (liftOccurrence occurrence) = CommonSignedChoiceDecision.check original slot occurrence := by
  apply Bool.eq_iff_iff.mpr
  rw [CommonSignedChoiceDecision.check_exact, CommonSignedChoiceDecision.check_exact, supported_exact]

theorem desired_exact (original : Graph n) (parameters : Fin n → Row) (oldClause : Clause n) (occurrence : Occurrence) :
    desired (graph original) (image parameters) (clause oldClause) (liftOccurrence occurrence) ↔ desired original parameters oldClause occurrence := by
  simp only [desired, clause, safety_check, image, lift_member]

theorem chosen_exact (original : Graph n) (parameters : Fin n → Row) (oldClause : Clause n) (slot : Fin n) (occurrence : Occurrence) :
    chosen (graph original) (image parameters) (clause oldClause) slot (liftOccurrence occurrence) ↔ chosen original parameters oldClause slot occurrence := by
  simp only [chosen, desired_exact]
  simp only [clause, safety_check, image, lift_member]

theorem reach_lift {original : Graph n} {parameters : Fin n → Row} {source target : Fin n} {first last : Occurrence}
    (path : Reach original parameters source first target last) :
    Reach (graph original) (image parameters) source (liftOccurrence first) target (liftOccurrence last) := by
  induction path with
  | refl => exact .refl _ _
  | @next middle target first before after oldClause path member same runs selected ih =>
    exact .next (clause := clause oldClause) ih (List.mem_map.mpr ⟨oldClause, member, rfl⟩) same
      (by simp only [clause, action_run, runs, Option.map_some]) ((chosen_exact original parameters oldClause target after).mpr selected)

theorem reach_reflect {original : Graph n} {parameters : Fin n → Row} {source target : Fin n} {first last : Occurrence}
    (path : Reach (graph original) (image parameters) source first target last) :
    ∀ before, first = liftOccurrence before → ∃ after, last = liftOccurrence after ∧ Reach original parameters source before target after := by
  induction path with
  | refl => intro before same; exact ⟨before, same, .refl _ _⟩
  | @next middle target first moved output newClause path member same runs selected ih =>
    intro before firstSame
    obtain ⟨oldClause, oldMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨oldMiddle, middleSame, oldPath⟩ := ih before firstSame
    rw [middleSame] at runs
    obtain ⟨oldOutput, oldRun, outputSame⟩ := action_reflect oldClause.action oldMiddle output runs
    rw [← outputSame] at selected
    exact ⟨oldOutput, outputSame.symm, .next (clause := oldClause) oldPath oldMember same oldRun
      ((chosen_exact original parameters oldClause target oldOutput).mp selected)⟩

def problem (original : Problem n) : Problem n :=
  ⟨graph original.clauses, original.heads.map (fun head => (head.1, liftOccurrence head.2))⟩

theorem problem_models_pullback (original : Problem n) (rows : Fin n → Row) (model : (problem original).Models rows) :
    original.Models (pullback rows) := by
  refine ⟨models_pullback original.clauses rows model.1, ?_⟩
  intro head member
  exact model.2 (head.1, liftOccurrence head.2) (List.mem_map.mpr ⟨head, member, rfl⟩)

theorem problem_models_exact (original : Problem n) (rows : Fin n → Row) :
    (problem original).Models (image rows) ↔ original.Models rows := by
  constructor
  · intro model
    simpa only [pullback_image] using problem_models_pullback original (image rows) model
  · intro model
    refine ⟨models_image original.clauses rows model.1, ?_⟩
    intro head member
    obtain ⟨oldHead, oldMember, rfl⟩ := List.mem_map.mp member
    exact (lift_member (rows oldHead.1) oldHead.2).mpr (model.2 oldHead oldMember)

theorem heads_check (original : Problem n) :
    CommonSignedChoiceSolver.checkHeads (problem original) = CommonSignedChoiceSolver.checkHeads original := by
  simp only [CommonSignedChoiceSolver.checkHeads, problem, List.all_map, Function.comp_def, safety_check]

theorem solve_lift (original : Problem n) :
    CommonSignedChoiceSolver.solve (problem original) = (CommonSignedChoiceSolver.solve original).map problem := by
  simp only [CommonSignedChoiceSolver.solve, heads_check]
  cases CommonSignedChoiceSolver.checkHeads original <;> rfl

theorem seed_lift (original : Problem n) (parameters : Fin n → Row) (slot : Fin n) (occurrence : Occurrence) :
    (image parameters slot occurrence ∨ (slot, occurrence) ∈ (problem original).heads) ↔
      ∃ before, liftOccurrence before = occurrence ∧ (parameters slot before ∨ (slot, before) ∈ original.heads) := by
  constructor
  · rintro (⟨before, member, same⟩ | member)
    · exact ⟨before, same, Or.inl member⟩
    · obtain ⟨head, member, same⟩ := List.mem_map.mp member
      have oldPair : (slot, head.2) = head := Prod.ext (congrArg Prod.fst same).symm rfl
      exact ⟨head.2, congrArg Prod.snd same, Or.inr (oldPair ▸ member)⟩
  · rintro ⟨before, same, (member | member)⟩
    · exact Or.inl ⟨before, member, same⟩
    · exact Or.inr (List.mem_map.mpr ⟨(slot, before), member, Prod.ext rfl same⟩)

theorem instantiate_lift (original : Problem n) (parameters : Fin n → Row) :
    CommonSignedChoiceSolver.instantiateRows (problem original) (image parameters) =
      image (CommonSignedChoiceSolver.instantiateRows original parameters) := by
  funext slot occurrence
  apply propext
  constructor
  · rintro ⟨start, first, safe, seed, path⟩
    obtain ⟨before, firstSame, oldSeed⟩ := (seed_lift original parameters start first).mp seed
    rw [← firstSame] at safe path
    obtain ⟨after, same, oldPath⟩ := reach_reflect path before rfl
    exact ⟨after, ⟨start, before, (safety_check original.clauses start before) ▸ safe, oldSeed, oldPath⟩, same.symm⟩
  · rintro ⟨after, ⟨start, first, safe, seed, path⟩, rfl⟩
    exact ⟨start, liftOccurrence first, (safety_check original.clauses start first).symm ▸ safe,
      (seed_lift original parameters start (liftOccurrence first)).mpr ⟨first, rfl, seed⟩, reach_lift path⟩

theorem instantiate_pullback (original : Problem n) (parameters : Fin n → Row) :
    pullback (CommonSignedChoiceSolver.instantiateRows (problem original) (image parameters)) =
      CommonSignedChoiceSolver.instantiateRows original parameters := by
  rw [instantiate_lift, pullback_image]

end Yulang.CommonSignedFreshChoice
