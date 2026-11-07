import Yulang.CommonRoleLinearDictionaries
import Yulang.CommonRoleLinearRepresentation

/-!
# Common evidence interpreted directly from actual role declarations

The interpretation is fixed by the constructor grammar: 0 is Int, 1 is pair,
and n+2 is variant n. No solver, arbitrary theory, or external decoder is a
parameter. The two-argument fragment suffices for the regular-goal reduction.
Every where goal is read from the selected declaration and every child uses
the identical visible declaration list.
-/

namespace Yulang.CommonRoleActualEvidence

open CommonRoleLinearClock
open CommonRoleLinearRepresentation

/-- Interpret the actual first-order term in the fixed Common constructor grammar. -/
def interpretTerm (term : Roles.Term) (assignment : Nat → Common.Ty) : Option Common.Ty :=
  (decodePattern term).map (fun pattern => pattern.eval assignment)

def interpretGoal (requirement : Roles.Goal) (assignment : Nat → Common.Ty) :
    Option SemanticGoal := do
  let [clock, value] := requirement.args | none
  return ⟨requirement.role, ← interpretTerm clock assignment, ← interpretTerm value assignment⟩

def Matches (implementation : Roles.Impl) (goal : SemanticGoal)
    (assignment : Nat → Common.Ty) : Prop :=
  ∃ head, interpretGoal ⟨implementation.role, implementation.head⟩ assignment = some head ∧
    GoalEquivalent head goal

def Unique (visible : List Roles.Impl) (implementation : Roles.Impl) (goal : SemanticGoal) : Prop :=
  ∀ other ∈ visible, (∃ assignment, Matches other goal assignment) → other = implementation

mutual
  inductive Derives (visible : List Roles.Impl) : SemanticGoal → Prop where
    | impl {goal : SemanticGoal} (implementation : Roles.Impl) (assignment : Nat → Common.Ty)
        (member : implementation ∈ visible) (matched : Matches implementation goal assignment)
        (children : DerivesChildren visible assignment implementation.constraints) :
        Derives visible goal

  inductive DerivesChildren (visible : List Roles.Impl) :
      (Nat → Common.Ty) → List Roles.Goal → Prop where
    | nil {assignment : Nat → Common.Ty} : DerivesChildren visible assignment []
    | cons {assignment : Nat → Common.Ty} (requirement : Roles.Goal)
        (child : SemanticGoal) (rest : List Roles.Goal)
        (interpreted : interpretGoal requirement assignment = some child)
        (derivation : Derives visible child)
        (children : DerivesChildren visible assignment rest) :
        DerivesChildren visible assignment (requirement :: rest)
end

mutual
  inductive Dictionary (visible : List Roles.Impl) : SemanticGoal → Type where
    | impl {goal : SemanticGoal} (implementation : Roles.Impl) (assignment : Nat → Common.Ty)
        (member : implementation ∈ visible) (matched : Matches implementation goal assignment)
        (unique : Unique visible implementation goal)
        (children : Children visible assignment implementation.constraints) : Dictionary visible goal

  inductive Children (visible : List Roles.Impl) :
      (Nat → Common.Ty) → List Roles.Goal → Type where
    | nil {assignment : Nat → Common.Ty} : Children visible assignment []
    | cons {assignment : Nat → Common.Ty} (requirement : Roles.Goal) (child : SemanticGoal) (rest : List Roles.Goal)
        (interpreted : interpretGoal requirement assignment = some child)
        (dictionary : Dictionary visible child) (children : Children visible assignment rest) :
        Children visible assignment (requirement :: rest)
end

mutual
  def Dictionary.erase {visible : List Roles.Impl} {goal : SemanticGoal} :
      Dictionary visible goal → RoleDictionaries.Plan
    | .impl implementation _ _ _ _ children => .node implementation children.erase

  def Children.erase {visible : List Roles.Impl} {assignment : Nat → Common.Ty}
      {requirements : List Roles.Goal} : Children visible assignment requirements → List RoleDictionaries.Plan
    | .nil => []
    | .cons _ _ _ _ dictionary children => dictionary.erase :: children.erase
end

@[simp] theorem interpretTerm_encode (pattern : Pattern) (assignment : Nat → Common.Ty) :
    interpretTerm pattern.encode assignment = some (pattern.eval assignment) := by
  simp [interpretTerm, decodePattern_encode]

@[simp] theorem interpret_compile_head (key : Nat) (rule : Rule) (assignment : Nat → Common.Ty) :
    interpretGoal ⟨(compile key rule).role, (compile key rule).head⟩ assignment =
      some (headGoal rule assignment) := by
  simp [interpretGoal, compile, headGoal]

@[simp] theorem interpret_compile_child (rule : Rule) (assignment : Nat → Common.Ty) :
    interpretGoal ⟨rule.target, [Roles.Term.var rule.fresh, rule.right.encode]⟩ assignment =
      some (childGoal rule assignment) := by
  simp [interpretGoal, interpretTerm, decodePattern, decodePattern_encode, Pattern.eval, childGoal]

@[simp] theorem matches_compile (key : Nat) (rule : Rule) (goal : SemanticGoal)
    (assignment : Nat → Common.Ty) :
    Matches (compile key rule) goal assignment ↔ HeadMatches rule goal assignment := by
  simp [Matches, HeadMatches]

@[simp] theorem interpret_terminal_head (key terminal : Nat) (assignment : Nat → Common.Ty) :
    interpretGoal ⟨(terminalImpl key terminal).role, (terminalImpl key terminal).head⟩ assignment =
      some ⟨terminal, assignment 0, assignment 1⟩ := rfl

@[simp] theorem matches_terminal (key terminal : Nat) (goal : SemanticGoal) :
    (∃ assignment, Matches (terminalImpl key terminal) goal assignment) ↔ goal.role = terminal := by
  constructor
  · rintro ⟨assignment, head, interpreted, matched⟩
    simp only [interpret_terminal_head, Option.some.injEq] at interpreted
    subst head
    exact matched.1.symm
  · intro finished
    let assignment := fun name => if name = 0 then goal.clock else goal.value
    refine ⟨assignment, ⟨terminal, goal.clock, goal.value⟩, ?_, ?_⟩
    · simp [assignment]
    · exact ⟨finished.symm, Common.equivalent_refl _, Common.equivalent_refl _⟩


@[simp] theorem unique_compile (registry : CommonRoleLinearEvidence.Registry) (terminal : Nat) (entry : Nat × Rule)
    (goal : SemanticGoal) :
    Unique (CommonRoleLinearEvidence.visible registry terminal) (compile (entry.1 + 1) entry.2) goal ↔
      CommonRoleLinearEvidence.UniqueHead registry terminal entry goal := by
  constructor
  · intro unique
    constructor
    · intro finished
      have impossible := unique (terminalImpl 0 terminal) (List.mem_cons_self ..)
        ((matches_terminal _ _ _).mpr finished)
      exact terminal_ne_compile _ _ _ _ impossible
    · intro other member matched
      apply (compile_entry_eq_iff other entry).mp
      exact unique _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨other, member, rfl⟩))
        (by simpa using matched)
  · rintro ⟨notTerminal, unique⟩ other member matched
    rcases List.mem_cons.mp member with rfl | member
    · exact False.elim (notTerminal ((matches_terminal _ _ _).mp matched))
    · obtain ⟨otherEntry, entryMember, rfl⟩ := List.mem_map.mp member
      have same := unique otherEntry entryMember (by simpa using matched)
      cases same
      rfl

@[simp] theorem unique_terminal (registry : CommonRoleLinearEvidence.Registry) (terminal : Nat) (goal : SemanticGoal) :
    Unique (CommonRoleLinearEvidence.visible registry terminal) (terminalImpl 0 terminal) goal ↔
      ∀ entry ∈ registry, ∀ assignment, ¬ HeadMatches entry.2 goal assignment := by
  constructor
  · intro unique entry member assignment matched
    have impossible := unique (compile (entry.1 + 1) entry.2)
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨entry, member, rfl⟩))
      ⟨assignment, (matches_compile _ _ _ _).mpr matched⟩
    exact compile_ne_terminal _ _ _ _ impossible
  · intro noRule other member matched
    rcases List.mem_cons.mp member with rfl | member
    · rfl
    · obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp member
      obtain ⟨assignment, matched⟩ := matched
      exact False.elim (noRule entry entryMember assignment ((matches_compile _ _ _ _).mp matched))

def terminalAssignment (goal : SemanticGoal) : Nat → Common.Ty :=
  fun name => if name = 0 then goal.clock else goal.value

theorem terminalAssignment_matches (terminal : Nat) (goal : SemanticGoal)
    (finished : goal.role = terminal) :
    Matches (terminalImpl 0 terminal) goal (terminalAssignment goal) := by
  refine ⟨⟨terminal, goal.clock, goal.value⟩, ?_, ?_⟩
  · simp [terminalAssignment]
  · exact ⟨finished.symm, Common.equivalent_refl _, Common.equivalent_refl _⟩

/-- Converts the specialized compiler proof to a dictionary whose constructors
inspect actual `Impl.head` and `Impl.constraints`. -/
def ofSpecial {registry : CommonRoleLinearEvidence.Registry} {terminal : Nat} {goal : SemanticGoal} :
    CommonRoleLinearEvidence.Dictionary registry terminal goal → Dictionary (CommonRoleLinearEvidence.visible registry terminal) goal
  | .done finished noRule =>
      .impl (terminalImpl 0 terminal) (terminalAssignment goal) (List.mem_cons_self ..)
        (terminalAssignment_matches terminal goal finished)
        ((unique_terminal registry terminal goal).mpr noRule) .nil
  | .step entry assignment member matched unique child =>
      .impl (compile (entry.1 + 1) entry.2) assignment
        (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨entry, member, rfl⟩))
        ((matches_compile _ _ _ _).mpr matched)
        ((unique_compile registry terminal entry goal).mpr unique)
        (.cons _ (childGoal entry.2 assignment) [] (interpret_compile_child entry.2 assignment)
          (ofSpecial child) .nil)

theorem ofSpecial_erase {registry : CommonRoleLinearEvidence.Registry} {terminal : Nat} {goal : SemanticGoal}
    (dictionary : CommonRoleLinearEvidence.Dictionary registry terminal goal) :
    (ofSpecial dictionary).erase = dictionary.erase := by
  induction dictionary with
  | done => rfl
  | step entry assignment member matched unique child ih =>
      simp only [ofSpecial, Dictionary.erase, Children.erase, CommonRoleLinearEvidence.Dictionary.erase, ih]

/-- Reflection reads the selected actual declaration, then its actual where
list. The finite compiler representation supplies no extra semantic premise. -/
theorem toSpecial {registry : CommonRoleLinearEvidence.Registry} {terminal : Nat} {goal : SemanticGoal}
    (dictionary : Dictionary (CommonRoleLinearEvidence.visible registry terminal) goal) :
    Nonempty (CommonRoleLinearEvidence.Dictionary registry terminal goal) := by
  induction dictionary using Dictionary.rec (motive_2 := fun assignment requirements _ =>
    ∀ requirement ∈ requirements, ∃ child, interpretGoal requirement assignment = some child ∧
      Nonempty (CommonRoleLinearEvidence.Dictionary registry terminal child)) with
  | @impl goal implementation assignment member matched unique children ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨.done ((matches_terminal _ _ _).mp ⟨assignment, matched⟩)
          ((unique_terminal registry terminal goal).mp unique)⟩
      · obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp member
        subst implementation
        obtain ⟨child, interpreted, ⟨childDictionary⟩⟩ := ih _ (List.mem_singleton_self _)
        have childSame : childGoal entry.2 assignment = child := by
          simpa only [interpret_compile_child, Option.some.injEq] using interpreted
        cases childSame
        exact ⟨.step entry assignment entryMember ((matches_compile _ _ _ _).mp matched)
          ((unique_compile registry terminal entry goal).mp unique) childDictionary⟩
  | nil => contradiction
  | cons requirement child rest interpreted dictionary children ihChild ihRest =>
      rename_i wanted member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨child, interpreted, ihChild⟩
      · exact ihRest wanted member

/-- Both directions retain the full dictionary, including every where child. -/
theorem dictionary_iff_special (registry : CommonRoleLinearEvidence.Registry) (terminal : Nat) (goal : SemanticGoal) :
    Nonempty (Dictionary (CommonRoleLinearEvidence.visible registry terminal) goal) ↔
      Nonempty (CommonRoleLinearEvidence.Dictionary registry terminal goal) :=
  ⟨fun ⟨dictionary⟩ => toSpecial dictionary, fun ⟨dictionary⟩ => ⟨ofSpecial dictionary⟩⟩

theorem Dictionary.derives {visible : List Roles.Impl} {goal : SemanticGoal}
    (dictionary : Dictionary visible goal) : Derives visible goal := by
  induction dictionary using Dictionary.rec (motive_2 := fun assignment requirements _ =>
    DerivesChildren visible assignment requirements) with
  | impl implementation assignment member matched unique children ih =>
      exact .impl implementation assignment member matched ih
  | nil => exact .nil
  | cons requirement child rest interpreted dictionary children ihChild ihRest =>
      exact .cons requirement child rest interpreted ihChild ihRest

theorem derives_to_special {registry : CommonRoleLinearEvidence.Registry} {terminal : Nat}
    {goal : SemanticGoal} (derivation : Derives (CommonRoleLinearEvidence.visible registry terminal) goal) :
    CommonRoleLinearEvidence.Derives registry terminal goal := by
  induction derivation using Derives.rec (motive_2 := fun assignment requirements _ =>
    ∀ requirement ∈ requirements, ∃ child, interpretGoal requirement assignment = some child ∧
      CommonRoleLinearEvidence.Derives registry terminal child) with
  | @impl goal implementation assignment member matched children ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact .done ((matches_terminal _ _ _).mp ⟨assignment, matched⟩)
      · obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp member
        subst implementation
        obtain ⟨child, interpreted, childDerivation⟩ := ih _ (List.mem_singleton_self _)
        have childSame : childGoal entry.2 assignment = child := by
          simpa only [interpret_compile_child, Option.some.injEq] using interpreted
        cases childSame
        exact .step entry assignment entryMember ((matches_compile _ _ _ _).mp matched) childDerivation
  | nil => contradiction
  | cons requirement child rest interpreted derivation children ihChild ihRest =>
      rename_i wanted member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨child, interpreted, ihChild⟩
      · exact ihRest wanted member

theorem derives_of_special {registry : CommonRoleLinearEvidence.Registry} {terminal : Nat}
    {goal : SemanticGoal} (derivation : CommonRoleLinearEvidence.Derives registry terminal goal) :
    Derives (CommonRoleLinearEvidence.visible registry terminal) goal := by
  induction derivation with
  | @done goal finished =>
      exact .impl (terminalImpl 0 terminal) (terminalAssignment goal) (List.mem_cons_self ..)
        (terminalAssignment_matches terminal goal finished) .nil
  | step entry assignment member matched child ih =>
      exact .impl (compile (entry.1 + 1) entry.2) assignment
        (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨entry, member, rfl⟩))
        ((matches_compile _ _ _ _).mpr matched)
        (.cons _ (childGoal entry.2 assignment) [] (interpret_compile_child entry.2 assignment) ih .nil)

theorem derives_iff_special (registry : CommonRoleLinearEvidence.Registry) (terminal : Nat)
    (goal : SemanticGoal) :
    Derives (CommonRoleLinearEvidence.visible registry terminal) goal ↔
      CommonRoleLinearEvidence.Derives registry terminal goal :=
  ⟨derives_to_special, derives_of_special⟩

theorem Dictionary.all_visible {visible : List Roles.Impl} {goal : SemanticGoal}
    (dictionary : Dictionary visible goal) :
    ∀ implementation ∈ dictionary.erase.declarations, implementation ∈ visible := by
  induction dictionary using Dictionary.rec (motive_2 := fun _ _ children =>
    ∀ implementation ∈ children.erase.flatMap RoleDictionaries.Plan.declarations,
      implementation ∈ visible) with
  | impl implementation assignment member matched unique children ih =>
      intro wanted present
      simp only [Dictionary.erase, RoleDictionaries.Plan.declarations, List.mem_cons] at present
      rcases present with rfl | present
      · exact member
      · exact ih wanted present
  | nil => contradiction
  | cons requirement child rest interpreted dictionary children ihChild ihRest =>
      rename_i wanted present
      simp only [Children.erase, List.flatMap_cons, List.mem_append] at present
      rcases present with present | present
      · exact ihChild wanted present
      · exact ihRest wanted present

/-- Associated constant bodies keep their equation for every semantic assignment,
including assignments containing regular recursive types and arbitrary rows. -/
theorem associated_int_equation (assignment : Nat → Common.Ty) :
    interpretTerm Pattern.int.encode assignment = some (.base .int) := rfl

end Yulang.CommonRoleActualEvidence
