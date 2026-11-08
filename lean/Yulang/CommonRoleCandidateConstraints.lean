import Yulang.CommonRoleGraphInspection
import Yulang.CommonRoleIntervalGeneration
import Yulang.CommonDeclaredNominalSourceFamily
import Yulang.CommonRoleRepeatedCaptureChecks

/-!
# Ordinary interval obligations from inspected head captures

The graph inspector returns the original graph-node identities captured by
each plain head variable. `slotBounds` is the finite source table associating
each such node with its original lower and upper ordinary type slots. The
generated constraints retain every same-name self/cross comparison, using
the existing interval generator. There is no point substitution search.

This is not yet candidate applicability: unresolved and cycle observations
must be retained, multiple lower contributions reconciled, and the generated
constraints propagated before the whole resolver can classify a demand.
-/
namespace Yulang.CommonRoleCandidateConstraints

open CommonRoleGraphInspection (Observation)
open Core.PresenceGeneration (TyTerm Comp)
open PresenceNormalForm (Atom All)
open CommonDeclaredNominalSlots (SlotAtom AllSlots)

abbrev Bindings (slots : Nat) := List (Nat × (Fin slots × Fin slots))

def fromObservations (slotBounds : Fin nodes → Fin slots × Fin slots) :
    List (Observation nodes) → Bindings slots :=
  List.flatMap fun observation => match observation with
    | .matched captured => captured.map fun (name, node) => (name, slotBounds node)
    | .mismatch | .unresolved | .cycle _ => []

theorem from_observations_exact (slotBounds : Fin nodes → Fin slots × Fin slots)
    (observations : List (Observation nodes)) (name : Nat) (pair : Fin slots × Fin slots) :
    (name, pair) ∈ fromObservations slotBounds observations ↔
      ∃ captured, .matched captured ∈ observations ∧
        ∃ node, (name, node) ∈ captured ∧ slotBounds node = pair := by
  simp only [fromObservations, List.mem_flatMap]
  constructor
  · rintro ⟨observation, member, found⟩
    cases observation with
    | matched captured =>
        obtain ⟨⟨actual, node⟩, present, equal⟩ := List.mem_map.mp found
        obtain ⟨rfl, same⟩ := Prod.mk.inj equal
        exact ⟨captured, member, node, present, same⟩
    | mismatch | unresolved | cycle => cases found
  · rintro ⟨captured, member, node, present, same⟩
    refine ⟨.matched captured, member, List.mem_map.mpr ?_⟩
    exact ⟨(name, node), present, by simp [same]⟩

def names (bindings : Bindings slots) : List Nat := (bindings.map Prod.fst).eraseDups

def bounds (bindings : Bindings slots) (name : Nat) : List (Fin slots × Fin slots) :=
  bindings.filterMap fun (key, pair) => if key = name then some pair else none

def arguments (bindings : Bindings slots) (name : Nat) :
    List (CommonRoleIntervalGeneration.Argument (Fin slots)) :=
  (bounds bindings name).map fun pair => (.var pair.1, .var pair.2)

def generate (bindings : Bindings slots) : List (Atom (Fin slots)) :=
  (names bindings).flatMap fun name => CommonRoleIntervalGeneration.generate (arguments bindings name)

def Compatible (bindings : Bindings slots) (assignment : Fin slots → Comp Common.model) : Prop :=
  ∀ name ∈ names bindings, ∀ first ∈ bounds bindings name, ∀ last ∈ bounds bindings name,
    Common.Subtype (assignment first.1).1 (assignment last.2).1

theorem generate_for_exact (bindings : Bindings slots) (name : Nat)
    (assignment : Fin slots → Comp Common.model) :
    All Common.model assignment (CommonRoleIntervalGeneration.generate (arguments bindings name)) ↔
      ∀ first ∈ bounds bindings name, ∀ last ∈ bounds bindings name,
        Common.Subtype (assignment first.1).1 (assignment last.2).1 := by
  rw [CommonRoleIntervalGeneration.generate_exact]
  simp only [CommonRoleIntervalGeneration.meaning, CommonRoleIntervals.valid_coalesce,
    arguments, List.map_map, List.forall_mem_map, CommonRoleIntervals.evaluate,
    CommonRoleIntervalGeneration.eval, TyTerm.eval, Function.comp_def]

/-- Every original occurrence is checked against every other occurrence of
the same captured name, including both directions and each self-check. -/
theorem generate_exact (bindings : Bindings slots) (assignment : Fin slots → Comp Common.model) :
    All Common.model assignment (generate bindings) ↔ Compatible bindings assignment := by
  simp only [All, generate, List.mem_flatMap, forall_exists_index, and_imp]
  unfold Compatible
  constructor
  · intro all name named
    apply (generate_for_exact bindings name assignment).mp
    intro atom member
    exact all atom name named member
  · intro compatible atom name named member
    exact (generate_for_exact bindings name assignment).mpr (compatible name named) atom member

/-- The existing repeated-capture component represents these same source
slots as `Form.var` nodes with their original natural-number identities. -/
def formBindings (bindings : Bindings slots) : CommonRoleIntervalCapture.Bindings :=
  bindings.map fun (name, pair) => (name, (.var pair.1.val, .var pair.2.val))

theorem form_names (bindings : Bindings slots) :
    CommonRoleRepeatedCaptureChecks.names (formBindings bindings) = names bindings := by
  simp [CommonRoleRepeatedCaptureChecks.names, formBindings, names, List.map_map, Function.comp_def]

theorem form_intervals (bindings : Bindings slots) (name : Nat) :
    CommonRoleRepeatedCaptureChecks.intervals (formBindings bindings) name =
      (bounds bindings name).map fun pair => (TyTerm.var pair.1.val, TyTerm.var pair.2.val) := by
  induction bindings with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨key, lower, upper⟩
      by_cases same : key = name <;>
        simpa [formBindings, CommonRoleRepeatedCaptureChecks.intervals, bounds,
          CommonRoleRepeatedCaptureChecks.term, same] using ih

/-- For any corresponding source assignments, the new finite-slot checks
have exactly the same meaning as the existing repeated-capture checks. -/
theorem repeated_checks_agree (bindings : Bindings slots)
    (assignment : Fin slots → Comp Common.model) (naturalAssignment : Nat → Comp Common.model)
    (agree : ∀ index : Fin slots, naturalAssignment index.val = assignment index) :
    All Common.model assignment (generate bindings) ↔
      All Common.model naturalAssignment (CommonRoleRepeatedCaptureChecks.generate (formBindings bindings)) := by
  rw [generate_exact, CommonRoleRepeatedCaptureChecks.generate_exact, form_names]
  unfold Compatible
  constructor
  · intro compatible name named first firstMember last lastMember
    rw [form_intervals] at firstMember lastMember
    obtain ⟨before, present, rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨after, included, rfl⟩ := List.mem_map.mp lastMember
    simpa only [TyTerm.eval, agree] using compatible name named before present after included
  · intro compatible name named first firstMember last lastMember
    have before : (TyTerm.var first.1.val, TyTerm.var first.2.val) ∈
        CommonRoleRepeatedCaptureChecks.intervals (formBindings bindings) name := by
      rw [form_intervals]
      exact List.mem_map.mpr ⟨first, firstMember, rfl⟩
    have after : (TyTerm.var last.1.val, TyTerm.var last.2.val) ∈
        CommonRoleRepeatedCaptureChecks.intervals (formBindings bindings) name := by
      rw [form_intervals]
      exact List.mem_map.mpr ⟨last, lastMember, rfl⟩
    simpa only [TyTerm.eval, agree] using compatible name named _ before _ after

theorem generated_slots (bindings : Bindings slots) : AllSlots (generate bindings) := by
  intro atom member
  obtain ⟨name, _, member⟩ := List.mem_flatMap.mp member
  obtain ⟨constraint, included, rfl⟩ := List.mem_map.mp member
  obtain ⟨first, firstMember, last, lastMember, rfl⟩ :=
    (CommonRoleIntervals.mem_checks _ _).mp included
  obtain ⟨first, _, rfl⟩ := List.mem_map.mp firstMember
  obtain ⟨last, _, rfl⟩ := List.mem_map.mp lastMember
  exact SlotAtom.value first.1 last.2

theorem generated_grammar (bindings : Bindings slots) :
    PresenceGeneratedChildGrammar.GoodAtoms (generate bindings) ∧
      PresenceGeneratedWidth.WidthAtoms (generate bindings) ∧
        PresenceSourceConstraintSupport.GoodAtoms (generate bindings) := by
  have allSlots := generated_slots bindings
  refine ⟨?_, ?_, ?_⟩
  · intro atom member
    cases allSlots atom member <;> trivial
  · intro source target member tail required
    cases allSlots (.tyLe source target) member
    cases required
  · intro atom member
    cases allSlots atom member <;> trivial

/-- The actual candidate-constraint pass, including the original ordinary
atoms, is handed to the existing unrestricted family solver. -/
def solve (original : List (Atom (Fin slots))) (bindings : Bindings slots) :
    List (CommonDeclaredNominalSourceFamily.Scheme slots) :=
  CommonDeclaredNominalSourceFamily.solve [] (original ++ generate bindings) []

/-- Every parameter of every returned scheme satisfies the original atoms
and every generated repeated-capture comparison. -/
theorem solve_sound (original : List (Atom (Fin slots))) (bindings : Bindings slots)
    (scheme : CommonDeclaredNominalSourceFamily.Scheme slots) (returned : scheme ∈ solve original bindings)
    (rows : Fin slots → Common.Row) (parameters : scheme.Parameters) :
    All Common.model (scheme.instantiate rows parameters) original ∧
      All Common.model (scheme.instantiate rows parameters) (generate bindings) := by
  have model := CommonDeclaredNominalSourceFamily.all_parameters_models []
    (original ++ generate bindings) [] scheme returned rows parameters
  exact (PresenceNormalForm.all_append _ _ _ _).mp model.1

/-- Exact recovery through the actual ordinary solver. The three grammar
premises concern the supplied original atom list; the newly generated
capture atoms establish those grammar properties internally. -/
theorem solve_all_instances_exact (original : List (Atom (Fin slots))) (bindings : Bindings slots)
    (child : PresenceGeneratedChildGrammar.GoodAtoms original)
    (width : PresenceGeneratedWidth.WidthAtoms original)
    (rows : PresenceSourceConstraintSupport.GoodAtoms original)
    (assignment : Fin slots → Comp Common.model) :
    (All Common.model assignment original ∧ Compatible bindings assignment) ↔
      ∃ scheme ∈ solve original bindings, ∃ rowParameters : Fin slots → Common.Row,
        ∃ parameters : scheme.Parameters,
          CommonDeclaredNominalSourceFamily.AssignmentEquivalent
            (scheme.instantiate rowParameters parameters) assignment := by
  obtain ⟨addedChild, addedWidth, addedRows⟩ := generated_grammar bindings
  have exactSolver := CommonDeclaredNominalSourceFamily.solve_all_instances_exact []
    (original ++ generate bindings) [] (child.append addedChild) (width.append addedWidth)
    (rows.append addedRows) assignment
  simpa [solve, CommonDeclaredNominalSourceFamily.Models, CommonDeclaredNominalSlots.Models,
    PresenceNormalForm.all_append, generate_exact] using exactSolver

/-- Failure of this ordinary constraint pass is exactly ordinary
inconsistency, for an original clause in the existing solver grammar. This
does not assert that a nonempty family is a selected role candidate. -/
theorem solve_empty_exact (original : List (Atom (Fin slots))) (bindings : Bindings slots)
    (child : PresenceGeneratedChildGrammar.GoodAtoms original)
    (width : PresenceGeneratedWidth.WidthAtoms original)
    (rows : PresenceSourceConstraintSupport.GoodAtoms original) :
    solve original bindings = [] ↔
      ¬ ∃ assignment, All Common.model assignment original ∧ Compatible bindings assignment := by
  constructor
  · intro empty ⟨assignment, model⟩
    obtain ⟨scheme, member, _, _, _⟩ :=
      (solve_all_instances_exact original bindings child width rows assignment).mp model
    simp [empty] at member
  · intro impossible
    cases result : solve original bindings with
    | nil => rfl
    | cons scheme rest =>
        have member : scheme ∈ solve original bindings := by rw [result]; exact List.mem_cons_self
        let rowParameters : Fin slots → Common.Row := fun _ => Common.rowEmpty
        let parameters : scheme.Parameters := (fun _ => .bottom, fun _ => .bottom)
        have model := solve_sound original bindings scheme member rowParameters parameters
        exact False.elim (impossible ⟨_, model.1, (generate_exact bindings _).mp model.2⟩)

/-- Read the actual head observations, keep them unchanged, and solve the
ordinary candidate constraints generated from every captured source slot. -/
structure Prepared (nodes slots : Nat) where
  observations : List (Observation nodes)
  bindings : Bindings slots
  schemes : List (CommonDeclaredNominalSourceFamily.Scheme slots)

def prepare (original : List (Atom (Fin slots))) (slotBounds : Fin nodes → Fin slots × Fin slots)
    (graph : CommonRoleRegularGraph.Graph nodes) (pattern : CommonRoleGraphInspection.Pattern)
    (head : Fin nodes) : Prepared nodes slots :=
  let observations := CommonRoleGraphInspection.inspectAll graph pattern head
  let bindings := fromObservations slotBounds observations
  ⟨observations, bindings, solve original bindings⟩

theorem prepare_observations (original : List (Atom (Fin slots)))
    (slotBounds : Fin nodes → Fin slots × Fin slots) (graph : CommonRoleRegularGraph.Graph nodes)
    (pattern : CommonRoleGraphInspection.Pattern) (head : Fin nodes) :
    (prepare original slotBounds graph pattern head).observations =
      CommonRoleGraphInspection.inspectAll graph pattern head := rfl

theorem prepare_all_instances_exact (original : List (Atom (Fin slots)))
    (slotBounds : Fin nodes → Fin slots × Fin slots) (graph : CommonRoleRegularGraph.Graph nodes)
    (pattern : CommonRoleGraphInspection.Pattern) (head : Fin nodes)
    (child : PresenceGeneratedChildGrammar.GoodAtoms original)
    (width : PresenceGeneratedWidth.WidthAtoms original)
    (rows : PresenceSourceConstraintSupport.GoodAtoms original)
    (assignment : Fin slots → Comp Common.model) :
    (All Common.model assignment original ∧
      Compatible (prepare original slotBounds graph pattern head).bindings assignment) ↔
      ∃ scheme ∈ (prepare original slotBounds graph pattern head).schemes,
        ∃ rowParameters : Fin slots → Common.Row, ∃ parameters : scheme.Parameters,
          CommonDeclaredNominalSourceFamily.AssignmentEquivalent
            (scheme.instantiate rowParameters parameters) assignment :=
  solve_all_instances_exact original _ child width rows assignment

/-- The source generator itself supplies the grammar facts for every clause
it emits. `slotBounds` still has to be connected to source graph allocation. -/
theorem generated_prepare_all_instances_exact (expression : Inference.Expr)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (generated : clause ∈ PresenceNormalForm.normalise (Core.PresenceGeneration.principal
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (slotBounds : Fin nodes → Fin (clause.locals + 1) × Fin (clause.locals + 1))
    (graph : CommonRoleRegularGraph.Graph nodes) (pattern : CommonRoleGraphInspection.Pattern)
    (head : Fin nodes) (assignment : Fin (clause.locals + 1) → Comp Common.model) :
    (All Common.model assignment clause.pack ∧
      Compatible (prepare clause.pack slotBounds graph pattern head).bindings assignment) ↔
      ∃ scheme ∈ (prepare clause.pack slotBounds graph pattern head).schemes,
        ∃ rowParameters : Fin (clause.locals + 1) → Common.Row, ∃ parameters : scheme.Parameters,
          CommonDeclaredNominalSourceFamily.AssignmentEquivalent
            (scheme.instantiate rowParameters parameters) assignment :=
  prepare_all_instances_exact clause.pack slotBounds graph pattern head
    (PresenceGeneratedChildGrammar.generated_child_grammar expression clause generated)
    (PresenceGeneratedWidth.generated_width_atoms expression clause generated)
    (PresenceSourceConstraintSupport.generated_row_shapes expression clause generated) assignment

end Yulang.CommonRoleCandidateConstraints
