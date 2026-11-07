import Yulang.CommonRoleLinearEvidence

/-!
# Unique-head regular dictionaries along finite machine reachability

The generic safety premise in this module is a property of reachable finite
machine configurations, independent of a resolver. It must be established by
the interpreter compiler, not assumed at the final B4 boundary. The existence
theorems below retain the exact finite `RoleDictionaries.Plan` payload and use
the same compiled visible registry for every where child.
-/

namespace Yulang.CommonRoleLinearEvidence

open CommonRoleLinearClock

inductive Reachable (registry : Registry) (start : Configuration) : Configuration → Prop where
  | refl : Reachable registry start start
  | step {source target : Configuration} (before : Reachable registry start source)
      (entry : Nat × Rule) (member : entry ∈ registry) (transition : entry.2.Step source target) :
      Reachable registry start target

theorem Reachable.trans {registry : Registry} {first middle last : Configuration}
    (before : Reachable registry first middle) (after : Reachable registry middle last) :
    Reachable registry first last := by
  induction after with
  | refl => exact before
  | step _ entry member transition ih => exact .step ih entry member transition

def NoOverlapAt (registry : Registry) (terminal : Nat) (configuration : Configuration) : Prop :=
  (configuration.role = terminal → ∀ entry ∈ registry, ∀ target, ¬ entry.2.Step configuration target) ∧
  (∀ first ∈ registry, ∀ last ∈ registry, ∀ a b,
    first.2.Step configuration a → last.2.Step configuration b → first = last)

def SafeFrom (registry : Registry) (terminal : Nat) (start : Configuration) : Prop :=
  ∀ configuration, Reachable registry start configuration → NoOverlapAt registry terminal configuration

theorem safe_child {registry : Registry} {terminal : Nat} {source target : Configuration}
    (safe : SafeFrom registry terminal source) (entry : Nat × Rule) (member : entry ∈ registry)
    (transition : entry.2.Step source target) : SafeFrom registry terminal target := by
  intro later reached
  exact safe later ((Reachable.step .refl entry member transition).trans reached)

theorem no_semantic_head_overlap {registry : Registry} {terminal : Nat}
    (linear : LinearRegistry registry) {configuration : Configuration}
    (safe : NoOverlapAt registry terminal configuration) {goal : SemanticGoal}
    (same : GoalEquivalent goal (goalOf configuration)) : ¬ HeadOverlap registry terminal goal := by
  rintro (⟨finished, entry, member, assignment, matched⟩ |
    ⟨first, firstMember, last, lastMember, different, ⟨firstAssignment, firstMatch⟩,
      ⟨lastAssignment, lastMatch⟩⟩)
  · obtain ⟨target, transition, _⟩ := matched_child_finite entry.2 (linear entry member)
      configuration assignment (GoalEquivalent.trans matched same)
    exact safe.1 (same.1.symm.trans finished) entry member target transition
  · obtain ⟨a, firstStep, _⟩ := matched_child_finite first.2 (linear first firstMember)
      configuration firstAssignment (GoalEquivalent.trans firstMatch same)
    obtain ⟨b, lastStep, _⟩ := matched_child_finite last.2 (linear last lastMember)
      configuration lastAssignment (GoalEquivalent.trans lastMatch same)
    exact different (safe.2 first firstMember last lastMember a b firstStep lastStep)

theorem no_reachable_overlap {registry : Registry} {terminal : Nat}
    (linear : LinearRegistry registry) {start : Configuration}
    (safe : SafeFrom registry terminal start) :
    ¬ ReachesOverlap registry terminal (goalOf start) := by
  intro overlap
  have refute {goal : SemanticGoal} (reached : ReachesOverlap registry terminal goal) :
      ∀ configuration, Reachable registry start configuration →
        GoalEquivalent goal (goalOf configuration) → False := by
    induction reached with
    | here overlap =>
        intro configuration reachable same
        exact no_semantic_head_overlap linear (safe configuration reachable) same overlap
    | descend entry assignment member matched _ child ih =>
        intro source reachable same
        obtain ⟨target, transition, sameChild⟩ := matched_child_finite entry.2
          (linear entry member) source assignment (GoalEquivalent.trans matched same)
        exact ih target (.step reachable entry member transition) sameChild
  exact refute overlap start .refl (GoalEquivalent.refl _)

theorem resolves_iff_machine_halts (registry : Registry) (terminal : Nat)
    (linear : LinearRegistry registry) (start : Configuration) (safe : SafeFrom registry terminal start) :
    Resolves registry terminal (goalOf start) ↔ MachineHalts registry terminal start := by
  constructor
  · intro resolved
    exact (derives_iff_machine_halts registry terminal linear start).mp resolved.1
  · intro halts
    exact ⟨machine_to_derives halts, no_reachable_overlap linear safe⟩

inductive Dictionary (registry : Registry) (terminal : Nat) : SemanticGoal → Type where
  | done {goal : SemanticGoal} (finished : goal.role = terminal)
      (noRule : ∀ entry ∈ registry, ∀ assignment, ¬ HeadMatches entry.2 goal assignment) :
      Dictionary registry terminal goal
  | step {goal : SemanticGoal} (entry : Nat × Rule) (assignment : Nat → Common.Ty)
      (member : entry ∈ registry) (matched : HeadMatches entry.2 goal assignment)
      (unique : UniqueHead registry terminal entry goal)
      (child : Dictionary registry terminal (childGoal entry.2 assignment)) :
      Dictionary registry terminal goal

def Dictionary.erase {registry : Registry} {terminal : Nat} {goal : SemanticGoal} :
    Dictionary registry terminal goal → RoleDictionaries.Plan
  | .done _ _ => .node (terminalImpl 0 terminal) []
  | .step entry _ _ _ _ child => .node (compile (entry.1 + 1) entry.2) [child.erase]

theorem Dictionary.derives {registry : Registry} {terminal : Nat} {goal : SemanticGoal}
    (dictionary : Dictionary registry terminal goal) : Derives registry terminal goal := by
  induction dictionary with
  | done finished _ => exact .done finished
  | step entry assignment member matched _ _ ih => exact .step entry assignment member matched ih

def Dictionary.transport {registry : Registry} {terminal : Nat} {first last : SemanticGoal}
    (same : GoalEquivalent first last) (dictionary : Dictionary registry terminal first) :
    Dictionary registry terminal last := by
  cases dictionary with
  | done finished noRule =>
      exact .done (same.1.symm.trans finished) (fun entry member assignment matched =>
        noRule entry member assignment (GoalEquivalent.trans matched (GoalEquivalent.symm same)))
  | step entry assignment member matched unique child =>
      refine .step entry assignment member (GoalEquivalent.trans matched same) ⟨?_, ?_⟩ child
      · intro finished
        exact unique.1 (same.1.trans finished)
      · intro other otherMember otherMatch
        obtain ⟨otherAssignment, otherMatched⟩ := otherMatch
        exact unique.2 other otherMember ⟨otherAssignment,
          GoalEquivalent.trans otherMatched (GoalEquivalent.symm same)⟩

theorem machine_to_dictionary {registry : Registry} {terminal : Nat}
    (linear : LinearRegistry registry) {start : Configuration}
    (run : MachineHalts registry terminal start) (safe : SafeFrom registry terminal start) :
    Nonempty (Dictionary registry terminal (goalOf start)) := by
  induction run with
  | @done configuration finished =>
      refine ⟨.done finished ?_⟩
      intro entry member assignment matched
      obtain ⟨target, transition, _⟩ := matched_child_finite entry.2 (linear entry member)
        configuration assignment matched
      exact (safe configuration .refl).1 finished entry member target transition
  | @step source target entry member transition rest ih =>
      obtain ⟨child⟩ := ih (safe_child safe entry member transition)
      obtain ⟨assignment, matched, sameChild⟩ := finite_step_instance entry.2 source target transition
      refine ⟨.step entry assignment member matched ⟨?_, ?_⟩
        (Dictionary.transport (GoalEquivalent.symm sameChild) child)⟩
      · intro finished
        exact (safe source .refl).1 finished entry member target transition
      · intro other otherMember otherMatched
        obtain ⟨otherAssignment, otherMatch⟩ := otherMatched
        obtain ⟨otherTarget, otherStep, _⟩ := matched_child_finite other.2
          (linear other otherMember) source otherAssignment otherMatch
        exact (safe source .refl).2 other otherMember entry member otherTarget target otherStep transition

theorem dictionary_iff_machine_halts (registry : Registry) (terminal : Nat)
    (linear : LinearRegistry registry) (start : Configuration) (safe : SafeFrom registry terminal start) :
    Nonempty (Dictionary registry terminal (goalOf start)) ↔ MachineHalts registry terminal start := by
  constructor
  · rintro ⟨dictionary⟩
    exact (derives_iff_machine_halts registry terminal linear start).mp dictionary.derives
  · intro halts
    exact machine_to_dictionary linear halts safe

theorem Dictionary.all_visible {registry : Registry} {terminal : Nat} {goal : SemanticGoal}
    (dictionary : Dictionary registry terminal goal) :
    ∀ implementation ∈ dictionary.erase.declarations, implementation ∈ visible registry terminal := by
  induction dictionary with
  | done => simp [Dictionary.erase, RoleDictionaries.Plan.declarations, visible]
  | step entry assignment member matched unique child ih =>
      intro implementation present
      simp only [Dictionary.erase, RoleDictionaries.Plan.declarations, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, List.mem_cons] at present
      rcases present with rfl | present
      · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨entry, member, rfl⟩)
      · exact ih implementation present

end Yulang.CommonRoleLinearEvidence
