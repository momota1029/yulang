import Yulang.CommonNominalCarrierConstraints
import Yulang.CastGraph

/-!
# Unrestricted solved parameters for invariant nominal slot equalities

Nominal graph arguments refer to shared value/row slots. The finite solver
computes connected components separately for the two sorts. Parameters are the
ordinary unrestricted product of all new regular values and all Common rows;
there is no residual condition, proof field, support bound or fuel.

This is the nominal equality stage. It does not solve arbitrary mixed
constructor bounds or claim source construction generation.
-/

namespace Yulang.CommonNominalSlotSolver

open CommonNominalCarrier
open Core.PresenceGeneration (Comp)

abbrev Edge (size : Nat) := Fin size × Fin size

def symmetricEdges (edges : List (Edge size)) : List (Edge size) :=
  edges ++ edges.map Prod.swap

private theorem reverse_edge (edges : List (Edge size)) (first last : Fin size) :
    (first, last) ∈ symmetricEdges edges ↔ (last, first) ∈ symmetricEdges edges := by
  simp only [symmetricEdges, List.mem_append, List.mem_map]
  constructor
  · rintro (direct | ⟨⟨a, b⟩, present, equal⟩)
    · exact Or.inr ⟨(first, last), direct, rfl⟩
    · have equal' : b = first ∧ a = last := by simpa using equal
      rcases equal' with ⟨rfl, rfl⟩
      exact Or.inl present
  · rintro (direct | ⟨⟨a, b⟩, present, equal⟩)
    · exact Or.inr ⟨(last, first), direct, rfl⟩
    · have equal' : b = last ∧ a = first := by simpa using equal
      rcases equal' with ⟨rfl, rfl⟩
      exact Or.inl present

abbrev Related (edges : List (Edge size)) (first last : Fin size) : Prop :=
  CastGraph.Path (symmetricEdges edges) first last

private theorem related_refl (edges : List (Edge size)) (index : Fin size) : Related edges index index :=
  .seed (by simp)

private theorem related_trans {edges : List (Edge size)} {first middle last : Fin size}
    (before : Related edges first middle) (after : Related edges middle last) : Related edges first last :=
  FiniteReachability.Reach.append before after

private theorem related_symm {edges : List (Edge size)} {first last : Fin size}
    (path : Related edges first last) : Related edges last first := by
  induction path with
  | seed present =>
      have same := List.mem_singleton.mp present
      subst same
      exact related_refl _ _
  | step _ edge ih =>
      have backwards := (reverse_edge edges _ _).mp (CastGraph.mem_adjacency _ _ _ |>.mp edge)
      exact related_trans (.step (related_refl _ _) ((CastGraph.mem_adjacency _ _ _).mpr backwards)) ih

private theorem related_edge (edges : List (Edge size)) (edge : Edge size) (present : edge ∈ edges) :
    Related edges edge.1 edge.2 :=
  .step (related_refl _ _) ((CastGraph.mem_adjacency _ _ _).mpr
    (List.mem_append.mpr (Or.inl present)))

def representative (edges : List (Edge size)) (index : Fin size) : Fin size :=
  ((List.finRange size).find? fun target => CastGraph.reachable (symmetricEdges edges) index target).getD index

private theorem representative_found (edges : List (Edge size)) (index : Fin size) :
    ∃ target, (List.finRange size).find?
      (fun target => CastGraph.reachable (symmetricEdges edges) index target) = some target := by
  cases found : (List.finRange size).find?
      (fun target => CastGraph.reachable (symmetricEdges edges) index target) with
  | some target => exact ⟨target, rfl⟩
  | none =>
      have absent := List.find?_eq_none.mp found index (List.mem_finRange index)
      have present := (CastGraph.reachable_exact _ index index).mpr (related_refl edges index)
      simp [present] at absent

private theorem representative_related (edges : List (Edge size)) (index : Fin size) :
    Related edges index (representative edges index) := by
  obtain ⟨target, found⟩ := representative_found edges index
  have reached := List.find?_some found
  simpa only [representative, found, Option.getD_some] using
    (CastGraph.reachable_exact _ index target).mp reached

private theorem representative_same {edges : List (Edge size)} {first last : Fin size}
    (related : Related edges first last) : representative edges first = representative edges last := by
  have tests : (fun target => CastGraph.reachable (symmetricEdges edges) first target) =
      (fun target => CastGraph.reachable (symmetricEdges edges) last target) := by
    funext target
    have same : CastGraph.reachable (symmetricEdges edges) first target = true ↔
        CastGraph.reachable (symmetricEdges edges) last target = true := by
      rw [CastGraph.reachable_exact, CastGraph.reachable_exact]
      exact ⟨related_trans (related_symm related), related_trans related⟩
    cases before : CastGraph.reachable (symmetricEdges edges) first target <;>
      cases after : CastGraph.reachable (symmetricEdges edges) last target <;> simp_all
  obtain ⟨target, found⟩ := representative_found edges first
  simp only [representative, ← tests, found, Option.getD_some]

private theorem related_property {A : Type} (relation : A → A → Prop)
    (refl : ∀ value, relation value value)
    (symm : ∀ {a b}, relation a b → relation b a)
    (trans : ∀ {a b c}, relation a b → relation b c → relation a c)
    (edges : List (Edge size)) (values : Fin size → A)
    (models : ∀ edge ∈ edges, relation (values edge.1) (values edge.2))
    {first last : Fin size} (path : Related edges first last) : relation (values first) (values last) := by
  induction path with
  | seed present =>
      have same := List.mem_singleton.mp present
      subst same
      exact refl _
  | @step origin target _ edge ih =>
      have present := (CastGraph.mem_adjacency _ _ _).mp edge
      rcases List.mem_append.mp present with direct | backwards
      · exact trans ih (models _ direct)
      · obtain ⟨⟨a, b⟩, direct, same⟩ := List.mem_map.mp backwards
        have same' : b = origin ∧ a = target := by simpa using same
        rcases same' with ⟨rfl, rfl⟩
        exact trans ih (symm (models _ direct))

structure Problem (size : Nat) where
  valueEdges : List (Edge size)
  rowEdges : List (Edge size)

def Problem.Models (problem : Problem size) (assignment : Fin size → Comp model) : Prop :=
  (∀ edge ∈ problem.valueEdges, Equivalent (assignment edge.1).1 (assignment edge.2).1) ∧
    ∀ edge ∈ problem.rowEdges, (assignment edge.1).2 = (assignment edge.2).2

abbrev Parameters (size : Nat) := (Fin size → Ty) × (Fin size → Row)

def Problem.instantiate (problem : Problem size) (parameters : Parameters size)
    (index : Fin size) : Comp model :=
  (parameters.1 (representative problem.valueEdges index),
    parameters.2 (representative problem.rowEdges index))

/-- Every parameter product, with no hidden satisfaction condition. -/
theorem all_parameter_sound (problem : Problem size) (parameters : Parameters size) :
    problem.Models (problem.instantiate parameters) := by
  constructor
  · intro edge present
    have same := representative_same (related_edge problem.valueEdges edge present)
    change Equivalent (parameters.1 _) (parameters.1 _)
    rw [same]
    exact ⟨subtype_refl _, subtype_refl _⟩
  · intro edge present
    have same := representative_same (related_edge problem.rowEdges edge present)
    change parameters.2 _ = parameters.2 _
    rw [same]

/-- Every original value and row model is recovered at every original slot;
values are demand-equivalent and rows are literally equal. -/
theorem all_models_recovered (problem : Problem size) (assignment : Fin size → Comp model)
    (models : problem.Models assignment) :
    ∃ parameters : Parameters size, ∀ index,
      Equivalent (problem.instantiate parameters index).1 (assignment index).1 ∧
        (problem.instantiate parameters index).2 = (assignment index).2 := by
  refine ⟨⟨fun index => (assignment index).1, fun index => (assignment index).2⟩, ?_⟩
  intro index
  have types := related_property Equivalent (fun _ => ⟨subtype_refl _, subtype_refl _⟩)
    (fun same => ⟨same.2, same.1⟩)
    (fun before after => ⟨subtype_trans before.1 after.1, subtype_trans after.2 before.2⟩)
    problem.valueEdges (fun index => (assignment index).1) models.1
    (representative_related problem.valueEdges index)
  have rows := related_property Eq (fun _ => rfl) Eq.symm Eq.trans
    problem.rowEdges (fun index => (assignment index).2) models.2
    (representative_related problem.rowEdges index)
  exact ⟨⟨types.2, types.1⟩, rows.symm⟩

end Yulang.CommonNominalSlotSolver

namespace Yulang.CommonNominalSlotSolver

open CommonNominalCarrier
open Core.PresenceGeneration (Comp)

private theorem equivalent_symm {first last : Ty} (same : Equivalent first last) : Equivalent last first :=
  ⟨same.2, same.1⟩

private theorem equivalent_trans {first middle last : Ty}
    (before : Equivalent first middle) (after : Equivalent middle last) : Equivalent first last :=
  ⟨subtype_trans before.1 after.1, subtype_trans after.2 before.2⟩

theorem models_of_recovered (problem : Problem size)
    (parameters : Parameters size) (assignment : Fin size → Comp model)
    (recovered : ∀ index, Equivalent (problem.instantiate parameters index).1 (assignment index).1 ∧
      (problem.instantiate parameters index).2 = (assignment index).2) : problem.Models assignment := by
  have sound := all_parameter_sound problem parameters
  constructor
  · intro edge present
    exact equivalent_trans (equivalent_symm (recovered edge.1).1)
      (equivalent_trans (sound.1 edge present) (recovered edge.2).1)
  · intro edge present
    exact (recovered edge.1).2.symm.trans ((sound.2 edge present).trans (recovered edge.2).2)

theorem all_models_exact (problem : Problem size) (assignment : Fin size → Comp model) :
    problem.Models assignment ↔ ∃ parameters : Parameters size, ∀ index,
      Equivalent (problem.instantiate parameters index).1 (assignment index).1 ∧
        (problem.instantiate parameters index).2 = (assignment index).2 :=
  ⟨all_models_recovered problem assignment,
    fun ⟨parameters, recovered⟩ => models_of_recovered problem parameters assignment recovered⟩

abbrev SlotArgument (size : Nat) := Fin size ⊕ Fin size

structure Head (size : Nat) where
  name : Nat
  arguments : List (SlotArgument size)

def argumentMeaning (assignment : Fin size → Comp model) : SlotArgument size → Argument
  | .inl index => .inl (assignment index).1
  | .inr index => .inr (assignment index).2

def Head.meaning (assignment : Fin size → Comp model) (head : Head size) : Ty :=
  nominal head.name (head.arguments.map (argumentMeaning assignment))

def merge (first last : Problem size) : Problem size :=
  ⟨first.valueEdges ++ last.valueEdges, first.rowEdges ++ last.rowEdges⟩

private theorem merge_models (first last : Problem size) (assignment : Fin size → Comp model) :
    (merge first last).Models assignment ↔ first.Models assignment ∧ last.Models assignment := by
  simp only [Problem.Models, merge, List.mem_append, or_imp, forall_and]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩; exact ⟨⟨a, c⟩, ⟨b, d⟩⟩
  · rintro ⟨⟨a, c⟩, ⟨b, d⟩⟩; exact ⟨⟨a, b⟩, ⟨c, d⟩⟩

def compileArgument : SlotArgument size → SlotArgument size → Option (Problem size)
  | .inl first, .inl last => some ⟨[(first, last)], []⟩
  | .inr first, .inr last => some ⟨[], [(first, last)]⟩
  | _, _ => none

def compileArguments : List (SlotArgument size) → List (SlotArgument size) → Option (Problem size)
  | [], [] => some ⟨[], []⟩
  | first :: rest, last :: tail => do
      return merge (← compileArgument first last) (← compileArguments rest tail)
  | _, _ => none

def compile (first last : Head size) : Option (Problem size) :=
  if first.name = last.name then compileArguments first.arguments last.arguments else none

private def Satisfied (assignment : Fin size → Comp model) (compiled : Option (Problem size)) : Prop :=
  ∃ problem, compiled = some problem ∧ problem.Models assignment

private theorem argument_exact (first last : SlotArgument size) (assignment : Fin size → Comp model) :
    Satisfied assignment (compileArgument first last) ↔
      ArgumentEquivalent (argumentMeaning assignment first) (argumentMeaning assignment last) := by
  cases first <;> cases last <;>
    simp [Satisfied, compileArgument, Problem.Models, argumentMeaning, ArgumentEquivalent]
  all_goals rfl

private def Aligned : List Argument → List Argument → Prop
  | [], [] => True
  | first :: rest, last :: tail => ArgumentEquivalent first last ∧ Aligned rest tail
  | _, _ => False

private theorem aligned_exact (first last : List Argument) :
    Aligned first last ↔ first.length = last.length ∧ ArgumentsEquivalent first last := by
  induction first generalizing last with
  | nil => cases last <;> simp [Aligned, ArgumentsEquivalent]
  | cons head tail ih =>
      cases last with
      | nil => simp [Aligned]
      | cons head' tail' =>
          simp only [Aligned, ih, List.length_cons, Nat.add_right_cancel_iff]
          constructor
          · rintro ⟨same, size, rest⟩
            refine ⟨size, ?_⟩
            intro index a b left right
            cases index with
            | zero =>
                simp only [List.getElem?_cons_zero, Option.some.injEq] at left right
                subst a; subst b
                exact same
            | succ index => exact rest index a b left right
          · rintro ⟨size, same⟩
            exact ⟨same 0 head head' rfl rfl, size,
              fun index a b left right => same (index + 1) a b left right⟩

private theorem arguments_exact (first last : List (SlotArgument size))
    (assignment : Fin size → Comp model) :
    Satisfied assignment (compileArguments first last) ↔
      Aligned (first.map (argumentMeaning assignment)) (last.map (argumentMeaning assignment)) := by
  induction first generalizing last with
  | nil => cases last <;> simp [compileArguments, Satisfied, Problem.Models, Aligned]
  | cons head tail ih =>
      cases last with
      | nil => simp [compileArguments, Satisfied, Aligned]
      | cons head' tail' =>
          have mergeExact (first last : Option (Problem size)) :
              Satisfied assignment (do return merge (← first) (← last)) ↔
                Satisfied assignment first ∧ Satisfied assignment last := by
            cases first <;> cases last <;> simp [Satisfied, merge_models]
          simp only [compileArguments, mergeExact, argument_exact, ih, List.map_cons, Aligned]

/-- Every nominal ID, arity and kind-correct shared slot vector, under every
assignment of arbitrary new regular types and arbitrary rows. -/
theorem compile_exact (first last : Head size) (assignment : Fin size → Comp model) :
    (∃ problem, compile first last = some problem ∧ problem.Models assignment) ↔
      CommonNominalCarrier.Subtype (first.meaning assignment) (last.meaning assignment) := by
  change Satisfied assignment (compile first last) ↔ _
  rw [Head.meaning, Head.meaning, nominal_regular_invariant_exact]
  by_cases identity : first.name = last.name
  · simp only [compile, identity, ↓reduceIte, arguments_exact, aligned_exact,
      List.length_map, true_and]
  · simp [compile, identity, Satisfied]

def solve : Option (Problem size) → List (Problem size)
  | none => []
  | some problem => [problem]

theorem solve_nominal_comparison_all_parameters (first last : Head size)
    (scheme : Problem size) (returned : scheme ∈ solve (compile first last))
    (parameters : Parameters size) :
    CommonNominalCarrier.Subtype (first.meaning (scheme.instantiate parameters))
      (last.meaning (scheme.instantiate parameters)) := by
  have compiled : compile first last = some scheme := by
    cases found : compile first last with
    | none => simp [solve, found] at returned
    | some actual =>
        have same : scheme = actual := by simpa [solve, found] using returned
        subst scheme
        rfl
  exact (compile_exact first last _).mp ⟨scheme, compiled, all_parameter_sound scheme parameters⟩

/-- Every original model is recovered at every original shared slot. Neither
rows nor value parameters have residual conditions. -/
theorem solve_nominal_comparison_all_instances_exact (first last : Head size)
    (assignment : Fin size → Comp model) :
    CommonNominalCarrier.Subtype (first.meaning assignment) (last.meaning assignment) ↔
      ∃ scheme ∈ solve (compile first last), ∃ parameters : Parameters size, ∀ index,
        Equivalent (scheme.instantiate parameters index).1 (assignment index).1 ∧
          (scheme.instantiate parameters index).2 = (assignment index).2 := by
  constructor
  · intro below
    obtain ⟨scheme, compiled, models⟩ := (compile_exact first last assignment).mpr below
    obtain ⟨parameters, recovered⟩ := all_models_recovered scheme assignment models
    exact ⟨scheme, by simp [solve, compiled], parameters, recovered⟩
  · rintro ⟨scheme, returned, parameters, recovered⟩
    have compiled : compile first last = some scheme := by
      cases found : compile first last with
      | none => simp [solve, found] at returned
      | some actual =>
          have same : scheme = actual := by simpa [solve, found] using returned
          subst scheme
          rfl
    exact (compile_exact first last assignment).mp
      ⟨scheme, compiled, models_of_recovered scheme parameters assignment recovered⟩

end Yulang.CommonNominalSlotSolver

namespace Yulang.CommonNominalSlotSolver

open CommonNominalCarrier
open Core.PresenceGeneration (Comp)

def compileAll : List (Head size × Head size) → Option (Problem size)
  | [] => some ⟨[], []⟩
  | (first, last) :: rest => do
      return merge (← compile first last) (← compileAll rest)

/-- Any finite set of comparisons sharing the same original value/row IDs. -/
theorem compile_all_exact (comparisons : List (Head size × Head size))
    (assignment : Fin size → Comp model) :
    (∃ problem, compileAll comparisons = some problem ∧ problem.Models assignment) ↔
      ∀ pair ∈ comparisons, CommonNominalCarrier.Subtype
        (pair.1.meaning assignment) (pair.2.meaning assignment) := by
  change Satisfied assignment (compileAll comparisons) ↔ _
  induction comparisons with
  | nil => simp [compileAll, Satisfied, Problem.Models]
  | cons pair rest ih =>
      have mergeExact (first last : Option (Problem size)) :
          Satisfied assignment (do return merge (← first) (← last)) ↔
            Satisfied assignment first ∧ Satisfied assignment last := by
        cases first <;> cases last <;> simp [Satisfied, merge_models]
      cases pair with
      | mk first last =>
          simp only [compileAll, mergeExact, ih]
          rw [show Satisfied assignment (compile first last) ↔ _ from compile_exact first last assignment]
          simp

private theorem returned_compiled (compiled : Option (Problem size)) (scheme : Problem size)
    (returned : scheme ∈ solve compiled) : compiled = some scheme := by
  cases compiled with
  | none => simp [solve] at returned
  | some actual =>
      have same : scheme = actual := by simpa [solve] using returned
      subst scheme
      rfl

theorem solve_nominal_family_all_parameters (comparisons : List (Head size × Head size))
    (scheme : Problem size) (returned : scheme ∈ solve (compileAll comparisons))
    (parameters : Parameters size) :
    ∀ pair ∈ comparisons, CommonNominalCarrier.Subtype
      (pair.1.meaning (scheme.instantiate parameters)) (pair.2.meaning (scheme.instantiate parameters)) :=
  (compile_all_exact comparisons _).mp
    ⟨scheme, returned_compiled _ _ returned, all_parameter_sound scheme parameters⟩

/-- All original models of all finite nominal comparisons are recovered
simultaneously. Shared value IDs remain shared, and all original row IDs are
recovered with literal equality. No condition on parameters remains. -/
theorem solve_nominal_family_all_instances_exact (comparisons : List (Head size × Head size))
    (assignment : Fin size → Comp model) :
    (∀ pair ∈ comparisons, CommonNominalCarrier.Subtype
      (pair.1.meaning assignment) (pair.2.meaning assignment)) ↔
    ∃ scheme ∈ solve (compileAll comparisons), ∃ parameters : Parameters size, ∀ index,
      Equivalent (scheme.instantiate parameters index).1 (assignment index).1 ∧
        (scheme.instantiate parameters index).2 = (assignment index).2 := by
  constructor
  · intro models
    obtain ⟨scheme, compiled, models⟩ := (compile_all_exact comparisons assignment).mpr models
    obtain ⟨parameters, recovered⟩ := all_models_recovered scheme assignment models
    exact ⟨scheme, by simp [solve, compiled], parameters, recovered⟩
  · rintro ⟨scheme, returned, parameters, recovered⟩
    exact (compile_all_exact comparisons assignment).mp
      ⟨scheme, returned_compiled _ _ returned, models_of_recovered scheme parameters assignment recovered⟩

end Yulang.CommonNominalSlotSolver
