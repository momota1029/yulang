import Yulang.CommonRoleMergedObstruction

/-! The generated canonical matcher agrees with Common head meaning on
finite rigid payloads. Even the larger arbitrary-Common evidence semantics
has exactly the same success set. This is a comparison, not a return to
arbitrary record-tail assignments. -/
namespace Yulang.CommonRoleMergedSemantic

open CommonRoleLinearClock (Pattern Ground Rule Configuration)
open CommonRoleMergedPayload
open CommonRoleMergedRegistry (compile terminalImpl visible)
open CommonRoleRegularRegistry (registry registry_linear)
open CommonRoleLinearEvidence (MachineHalts)

theorem generated_match_exact (copies : Nat) (pattern : Pattern) (value : Ground) :
    (∃ assignment : Nat → Ground, pattern.instantiate assignment = value) ↔
      ∃ assignment : Nat → Common.Ty, ∃ type,
        interpret (headTerm copies pattern) assignment = some type ∧
        Common.Equivalent type (Common.variant 0 value.eval) := by
  constructor
  · rintro ⟨assignment, matched⟩
    refine ⟨fun name => (assignment name).eval, _, interpret_head .., ?_⟩
    have same := head_meaning copies pattern (fun name => (assignment name).eval)
    rw [← CommonRoleLinearClock.instantiate_eval, matched] at same
    simpa only [← CommonRoleLinearClock.instantiate_eval, matched] using same
  · rintro ⟨assignment, type, interpreted, matched⟩
    have same := Option.some.inj ((interpret_head copies pattern assignment).symm.trans interpreted)
    subst type
    have headMatch : Common.Equivalent (pattern.eval assignment) value.eval := by
      apply (CommonCanonicalShapes.variant_equivalent_iff 0 _ _).mp
      exact Common.equivalent_trans (Common.equivalent_symm (head_meaning copies pattern assignment)) matched
    exact ⟨CommonRoleLinearClock.matchingAssignment pattern value,
      CommonRoleLinearClock.matchingAssignment_head pattern value assignment headMatch⟩

theorem requirements_determined_common (rule : Rule) (linear : CommonRoleLinearClock.Linear rule)
    (value : Ground) (σ τ : Nat → Common.Ty)
    (first : Common.Equivalent (rule.left.eval σ) value.eval)
    (last : Common.Equivalent (rule.left.eval τ) value.eval) :
    Common.Equivalent (rule.right.eval σ) (rule.right.eval τ) := by
  obtain ⟨_, a⟩ := CommonRoleLinearClock.finite_match_reflection rule linear value σ first
  obtain ⟨_, b⟩ := CommonRoleLinearClock.finite_match_reflection rule linear value τ last
  exact Common.equivalent_trans a (Common.equivalent_symm b)

theorem pattern_determines_used (pattern : Pattern) (σ τ : Nat → Common.Ty)
    (same : Common.Equivalent (pattern.eval σ) (pattern.eval τ)) (name : Nat)
    (used : 0 < pattern.encode.occurrences name) : Common.Equivalent (σ name) (τ name) := by
  induction pattern with
  | var variableName =>
      have equal : variableName = name := by
        by_cases equal : variableName = name
        · exact equal
        · simp [CommonRoleLinearClock.Pattern.encode, Roles.Term.occurrences, Ne.symm equal] at used
      subst variableName
      exact same
  | int => simp [CommonRoleLinearClock.Pattern.encode, Roles.Term.occurrences, Roles.argsOccurrences] at used
  | pair first last ihFirst ihLast =>
      obtain ⟨firstSame, lastSame⟩ := (CommonCanonicalShapes.pair_equivalent_iff _ _ _ _).mp same
      have occurs : 0 < first.encode.occurrences name + last.encode.occurrences name := by
        simpa [CommonRoleLinearClock.Pattern.encode, Roles.Term.occurrences, Roles.argsOccurrences] using used
      by_cases firstUsed : 0 < first.encode.occurrences name
      · exact ihFirst firstSame firstUsed
      · exact ihLast lastSame (by omega)
  | variant tag payload ih =>
      exact ih ((CommonCanonicalShapes.variant_equivalent_iff tag _ _).mp same)
        (by simpa [CommonRoleLinearClock.Pattern.encode, Roles.Term.occurrences, Roles.argsOccurrences] using used)

theorem requirements_determined_all_common (rule : Rule) (linear : CommonRoleLinearClock.Linear rule)
    (σ τ : Nat → Common.Ty) (same : Common.Equivalent (rule.left.eval σ) (rule.left.eval τ)) :
    Common.Equivalent (rule.right.eval σ) (rule.right.eval τ) := by
  apply CommonRoleLinearClock.Pattern.eval_congr
  intro name used
  have covered := linear name
  exact pattern_determines_used rule.left σ τ same name (by omega)

structure Goal where
  role : Nat
  argument : Common.Ty

def interpretGoal (requirement : Roles.Goal) (assignment : Nat → Common.Ty) : Option Goal := do
  let [term] := requirement.args | none
  return ⟨requirement.role, ← interpret term assignment⟩

def Matches (implementation : Roles.Impl) (goal : Goal) (assignment : Nat → Common.Ty) : Prop :=
  implementation.role = goal.role ∧ ∃ term type, implementation.head = [term] ∧
    interpret term assignment = some type ∧ Common.Equivalent type goal.argument

def meaning (goal : CommonRoleCanonicalMergedEvidence.Goal) : Goal :=
  ⟨goal.role, Common.variant 0 goal.value.eval⟩

theorem generated_candidate_exact (role key copies : Nat) (pattern : Pattern) (children : List Roles.Goal)
    (goal : CommonRoleCanonicalMergedEvidence.Goal) :
    (∃ assignment, CommonRoleCanonicalMergedEvidence.Matches
      ⟨role, [headTerm copies pattern], children, key⟩ goal assignment) ↔
    ∃ assignment, Matches ⟨role, [headTerm copies pattern], children, key⟩ (meaning goal) assignment := by
  constructor
  · rintro ⟨assignment, sameRole, decoded, read, matched⟩
    have samePattern := Option.some.inj ((decode_head copies pattern).symm.trans read)
    subst decoded
    obtain ⟨semantic, type, interpreted, same⟩ := (generated_match_exact copies pattern goal.value).mp ⟨assignment, matched⟩
    exact ⟨semantic, sameRole, headTerm copies pattern, type, rfl, interpreted, same⟩
  · rintro ⟨semantic, sameRole, term, type, head, interpreted, same⟩
    have sameTerm : term = headTerm copies pattern := (List.cons.inj head).1.symm
    subst term
    obtain ⟨assignment, matched⟩ := (generated_match_exact copies pattern goal.value).mpr
      ⟨semantic, type, interpreted, same⟩
    exact ⟨assignment, sameRole, pattern, decode_head copies pattern, matched⟩

theorem visible_candidate_exact (code : CommonRoleComputation.Code) (implementation : Roles.Impl)
    (member : implementation ∈ visible code) (goal : CommonRoleCanonicalMergedEvidence.Goal) :
    (∃ assignment, CommonRoleCanonicalMergedEvidence.Matches implementation goal assignment) ↔
      ∃ assignment, Matches implementation (meaning goal) assignment := by
  rcases List.mem_cons.mp member with rfl | member
  · exact generated_candidate_exact 0 0 0 (.var 0) [] goal
  · obtain ⟨entry, _, rfl⟩ := List.mem_map.mp member
    exact generated_candidate_exact entry.2.source (entry.1 + 1) entry.2.padding entry.2.left _ goal

theorem unique_common (code : CommonRoleComputation.Code) (implementation : Roles.Impl)
    (goal : CommonRoleCanonicalMergedEvidence.Goal)
    (unique : CommonRoleCanonicalMergedEvidence.Unique (visible code) implementation goal) :
    ∀ other ∈ visible code, (∃ assignment, Matches other (meaning goal) assignment) → other = implementation := by
  intro other member matched
  exact unique other member ((visible_candidate_exact code other member goal).mpr matched)

mutual
  inductive Derives (visible : List Roles.Impl) : Goal → Prop where
    | impl {goal} (implementation : Roles.Impl) (assignment : Nat → Common.Ty)
        (member : implementation ∈ visible) (matched : Matches implementation goal assignment)
        (children : Children visible assignment implementation.constraints) : Derives visible goal
  inductive Children (visible : List Roles.Impl) : (Nat → Common.Ty) → List Roles.Goal → Prop where
    | nil {assignment} : Children visible assignment []
    | cons {assignment} (requirement : Roles.Goal) (child : Goal) (rest : List Roles.Goal)
        (interpreted : interpretGoal requirement assignment = some child)
        (derivation : Derives visible child) (children : Children visible assignment rest) :
        Children visible assignment (requirement :: rest)
end

def goalOf (configuration : Configuration) : Goal := ⟨configuration.role, Common.variant 0 configuration.value.eval⟩

@[simp] theorem child_interpreted (rule : Rule) (assignment : Nat → Common.Ty) :
    interpretGoal ⟨rule.target, [plainTerm rule.right]⟩ assignment =
      some ⟨rule.target, Common.variant 0 (rule.right.eval assignment)⟩ := by
  simp [interpretGoal, plainTerm, paddedType]

def HeadDeterminesRequirements (declarations : List Roles.Impl) : Prop :=
  ∀ implementation ∈ declarations, ∀ σ τ : Nat → Common.Ty,
    (∀ term ∈ implementation.head, ∃ first last,
      interpret term σ = some first ∧ interpret term τ = some last ∧ Common.Equivalent first last) →
    ∀ child ∈ implementation.constraints, ∃ first last,
      interpretGoal child σ = some first ∧ interpretGoal child τ = some last ∧
      first.role = last.role ∧ Common.Equivalent first.argument last.argument

theorem head_determines_requirements (code : CommonRoleComputation.Code) : HeadDeterminesRequirements (visible code) := by
  intro implementation member σ τ heads child required
  rcases List.mem_cons.mp member with rfl | member
  · cases required
  · obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
    have childEqual : child = ⟨entry.2.target, [plainTerm entry.2.right]⟩ := by simpa [compile] using required
    subst child
    obtain ⟨first, last, firstRead, lastRead, same⟩ := heads _ (List.mem_singleton_self _)
    have firstEqual := Option.some.inj ((interpret_head entry.2.padding entry.2.left σ).symm.trans firstRead)
    have lastEqual := Option.some.inj ((interpret_head entry.2.padding entry.2.left τ).symm.trans lastRead)
    subst first
    subst last
    have dataSame : Common.Equivalent (entry.2.left.eval σ) (entry.2.left.eval τ) := by
      apply (CommonCanonicalShapes.variant_equivalent_iff 0 _ _).mp
      exact Common.equivalent_trans (Common.equivalent_symm (head_meaning entry.2.padding entry.2.left σ))
        (Common.equivalent_trans same (head_meaning entry.2.padding entry.2.left τ))
    exact ⟨_, _, child_interpreted entry.2 σ, child_interpreted entry.2 τ, rfl,
      (CommonCanonicalShapes.variant_equivalent_iff 0 _ _).mpr
        (requirements_determined_all_common entry.2 (registry_linear code entry present) σ τ dataSame)⟩

theorem reflect (code : CommonRoleComputation.Code) {goal : Goal} (derivation : Derives (visible code) goal) :
    ∀ source, goal.role = source.role → Common.Equivalent goal.argument (Common.variant 0 source.value.eval) →
      MachineHalts (registry code) 0 source := by
  induction derivation using Derives.rec (motive_2 := fun assignment requirements _ =>
    ∀ requirement ∈ requirements, ∃ child, interpretGoal requirement assignment = some child ∧
      ∀ source, child.role = source.role → Common.Equivalent child.argument (Common.variant 0 source.value.eval) →
        MachineHalts (registry code) 0 source) with
  | @impl goal implementation assignment member matched children ih =>
      intro source role data
      rcases List.mem_cons.mp member with rfl | member
      · exact .done (role.symm.trans matched.1.symm)
      · obtain ⟨entry, present, rfl⟩ := List.mem_map.mp member
        obtain ⟨sourceRole, term, type, head, interpreted, matched⟩ := matched
        have termEqual : term = headTerm entry.2.padding entry.2.left := (List.cons.inj head).1.symm
        subst term
        have typeEqual := Option.some.inj ((interpret_head entry.2.padding entry.2.left assignment).symm.trans interpreted)
        subst type
        have dataMatch : Common.Equivalent (entry.2.left.eval assignment) source.value.eval := by
          apply (CommonCanonicalShapes.variant_equivalent_iff 0 _ _).mp
          exact Common.equivalent_trans (Common.equivalent_symm (head_meaning entry.2.padding entry.2.left assignment))
            (Common.equivalent_trans matched data)
        obtain ⟨target, transition, sameChild⟩ := CommonRoleFiniteShadowHalting.matched_step entry.2
          (registry_linear code entry present) source assignment (sourceRole.trans role) dataMatch
        obtain ⟨child, read, reflected⟩ := ih _ (List.mem_singleton_self _)
        have childEqual := Option.some.inj ((child_interpreted entry.2 assignment).symm.trans read)
        subst child
        have targetRole : entry.2.target = target.role := by
          obtain ⟨_, _, same, _, _⟩ := transition
          exact same.symm
        exact .step entry present transition (reflected target targetRole
          ((CommonCanonicalShapes.variant_equivalent_iff 0 _ _).mpr sameChild))
  | nil => contradiction
  | cons requirement child rest interpreted derivation children ihChild ihRest =>
      rename_i wanted member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨child, interpreted, ihChild⟩
      · exact ihRest wanted member

theorem of_machine (code : CommonRoleComputation.Code) {source : Configuration}
    (run : MachineHalts (registry code) 0 source) : Derives (visible code) (goalOf source) := by
  induction run with
  | @done source finished =>
      let assignment : Nat → Common.Ty := fun _ => source.value.eval
      exact .impl terminalImpl assignment (List.mem_cons_self ..)
        ⟨finished.symm, _, _, rfl, interpret_head 0 (.var 0) assignment, Common.equivalent_refl _⟩ .nil
  | @step source target entry present transition rest ih =>
      obtain ⟨assignment, sourceRole, targetRole, sourceData, targetData⟩ := transition
      let semantic : Nat → Common.Ty := fun name => (assignment name).eval
      have sourceEval : entry.2.left.eval semantic = source.value.eval := by
        simpa only [CommonRoleLinearClock.instantiate_eval] using congrArg Ground.eval sourceData
      have targetEval : entry.2.right.eval semantic = target.value.eval := by
        simpa only [CommonRoleLinearClock.instantiate_eval] using congrArg Ground.eval targetData
      refine .impl (compile (entry.1 + 1) entry.2) semantic
        (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨entry, present, rfl⟩)) ?_
        (.cons _ (goalOf target) [] ?_ ih .nil)
      · refine ⟨sourceRole.symm, _, _, rfl, interpret_head entry.2.padding entry.2.left semantic, ?_⟩
        have same := head_meaning entry.2.padding entry.2.left semantic
        rw [sourceEval] at same
        simpa only [sourceEval, goalOf] using same
      · rw [child_interpreted, targetEval]
        simp [goalOf, targetRole]

theorem arbitrary_common_exact (code : CommonRoleComputation.Code) (input : CommonRoleComputation.Tree) :
    Derives (visible code) (goalOf (CommonRoleRegularHalting.start code input)) ↔ CommonRoleComputation.Halts code input := by
  constructor
  · intro derivation
    exact (CommonRoleRegularHalting.machine_halts_exact code input).mp
      (reflect code derivation _ rfl (Common.equivalent_refl _))
  · intro halting
    exact of_machine code ((CommonRoleRegularHalting.machine_halts_exact code input).mpr halting)

theorem canonical_iff_arbitrary_common (code : CommonRoleComputation.Code) (input : CommonRoleComputation.Tree) :
    Nonempty (CommonRoleCanonicalMergedEvidence.Dictionary (visible code) (CommonRoleMergedHalting.startGoal code input)) ↔
      Derives (visible code) (goalOf (CommonRoleRegularHalting.start code input)) :=
  (CommonRoleMergedHalting.dictionary_exact code input).trans (arbitrary_common_exact code input).symm

end Yulang.CommonRoleMergedSemantic
