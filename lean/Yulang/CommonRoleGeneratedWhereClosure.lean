import Yulang.CommonRoleSourceRoleObligations
import Yulang.CheckedRoles

/-!
# Actual recursive where-goal closure

The finite first-order declaration tree is computed without fuel or a supplied
visit list. Failed and overlapping nodes remain present; every sibling is
expanded. This is not interval stabilization or a parser adequacy theorem.
-/
namespace Yulang.CommonRoleGeneratedWhereClosure
open Roles

/-- Uniqueness is a declarative property of matching registry declarations. -/
def Unique (impls : List Impl) (g : Goal) (i : Impl) : Prop :=
  i ∈ impls ∧ Matches i g ∧ ∀ j ∈ impls, Matches j g → j = i

theorem unique_exact (impls : List Impl) (g : Goal) (i : Impl) :
    candidates impls g = [i] ↔ Unique impls g i := by
  constructor
  · intro h
    have hi := mem_candidates.mp (h ▸ List.mem_singleton_self i)
    exact ⟨hi.1, hi.2, fun j hj hm => by
      have member := mem_candidates.mpr ⟨hj, hm⟩
      simpa only [h, List.mem_singleton] using member⟩
  · rintro ⟨member, matched, only⟩
    have present := mem_candidates.mpr ⟨member, matched⟩
    have nodup := candidates_nodup impls g
    cases h : candidates impls g with
    | nil => simp [h] at present
    | cons j rest =>
      have first := mem_candidates.mp (h ▸ List.mem_cons_self)
      have same := only j first.1 first.2
      subst j
      cases rest with
      | nil => rfl
      | cons j rest =>
        have next := mem_candidates.mp (h ▸ List.mem_cons_of_mem i List.mem_cons_self)
        have same := only j next.1 next.2
        subst j
        simp [h] at nodup

def children (impls : List Impl) (g : Goal) : List Goal :=
  match candidates impls g with
  | [i] => i.constraints.map fun c => c.subst (matchingSubst i.head g.args)
  | _ => []

/-- Arbitrary matching substitutions, not the executable extraction function. -/
inductive Edge (impls : List Impl) : Goal → Goal → Prop
  | child (i : Impl) (σ : Subst) (c : Goal) : Unique impls g i →
      substArgs σ i.head = g.args → c ∈ i.constraints →
      Edge impls g (c.subst σ)

theorem children_exact (impls : List Impl) (wf : WellFormed impls) (g q : Goal) :
    q ∈ children impls g ↔ Edge impls g q := by
  constructor
  · intro member
    unfold children at member
    split at member
    · rename_i i selected
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp member
      have unique := (unique_exact impls g i).mp selected
      exact .child i _ c unique (matched_head unique.2.1) hc
    · simp at member
  · intro edge
    cases edge with
    | child i σ c unique head member =>
      rw [children, (unique_exact impls g i).mpr unique]
      exact List.mem_map.mpr ⟨c, member, matched_constraint (wf i unique.1) σ head member⟩

theorem edge_decreases (impls : List Impl) (wf : WellFormed impls)
    (edge : Edge impls g q) : argsSize q.args < argsSize g.args := by
  cases edge with
  | child i σ c unique head member =>
    simpa only [Goal.subst, head] using size_decreases (wf i unique.1) member σ

def closure (impls : List Impl) (wf : WellFormed impls) (g : Goal) : List Goal :=
  g :: (children impls g).attach.flatMap fun child => closure impls wf child.val
termination_by argsSize g.args
decreasing_by exact edge_decreases impls wf ((children_exact impls wf g child.val).mp child.property)

inductive Reach (impls : List Impl) : Goal → Goal → Prop
  | refl : Reach impls g g
  | step : Edge impls g child → Reach impls child q → Reach impls g q

theorem closure_complete (impls : List Impl) (wf : WellFormed impls)
    (reachable : Reach impls g q) : q ∈ closure impls wf g := by
  induction reachable with
  | refl => rw [closure]; exact List.mem_cons_self
  | @step g child q edge _ ih =>
      rw [closure]
      apply List.mem_cons_of_mem
      have member := (children_exact impls wf g child).mpr edge
      exact List.mem_flatMap.mpr ⟨⟨child, member⟩, List.mem_attach _ _, ih⟩

theorem closure_sound (impls : List Impl) (wf : WellFormed impls) (g q : Goal)
    (member : q ∈ closure impls wf g) : Reach impls g q := by
  rw [closure] at member
  rcases List.mem_cons.mp member with same | below
  · subst q; exact .refl
  · obtain ⟨child, _, member⟩ := List.mem_flatMap.mp below
    exact .step ((children_exact impls wf g child.val).mp child.property)
      (closure_sound impls wf child.val q member)
termination_by argsSize g.args
decreasing_by exact edge_decreases impls wf ((children_exact impls wf g child.val).mp child.property)

theorem closure_exact (impls : List Impl) (wf : WellFormed impls) (g q : Goal) :
    q ∈ closure impls wf g ↔ Reach impls g q :=
  ⟨closure_sound impls wf g q, closure_complete impls wf⟩

theorem reach_trans (first : Reach impls g q) (last : Reach impls q r) :
    Reach impls g r := by
  induction first with
  | refl => exact last
  | step edge _ ih => exact .step edge (ih last)

/-- Every actual generated child has a computed place, including failing goals. -/
theorem generated_closed (impls : List Impl) (wf : WellFormed impls) (g q r : Goal)
    (present : q ∈ closure impls wf g) (edge : Edge impls q r) :
    r ∈ closure impls wf g :=
  closure_complete impls wf (reach_trans (closure_sound impls wf g q present) (.step edge .refl))

theorem edge_resolves (impls : List Impl) (wf : WellFormed impls)
    (edge : Edge impls g q) (resolved : RoleConstraints.Resolves impls g) :
    RoleConstraints.Resolves impls q := by
  cases edge with
  | child i σ c unique head member =>
      have root := (RoleConstraints.resolve_exact impls wf g).mpr resolved
      obtain ⟨j, selected, each⟩ := (resolve_resolved_iff impls wf g).mp root
      have same : j = i := List.singleton_inj.mp
        (selected.symm.trans ((unique_exact impls g i).mpr unique))
      subst j
      rw [← matched_constraint (wf i unique.1) σ head member]
      exact (RoleConstraints.resolve_exact impls wf _).mp (each c member)

theorem reach_resolves (impls : List Impl) (wf : WellFormed impls)
    (reachable : Reach impls g q) (resolved : RoleConstraints.Resolves impls g) :
    RoleConstraints.Resolves impls q := by
  induction reachable with
  | refl => exact resolved
  | step edge _ ih => exact ih (edge_resolves impls wf edge resolved)

/-- Checking all generated obligations preserves exactly the original success. -/
theorem closure_resolves (impls : List Impl) (wf : WellFormed impls) (g : Goal) :
    (∀ q ∈ closure impls wf g, RoleConstraints.Resolves impls q) ↔
      RoleConstraints.Resolves impls g := by
  constructor
  · intro all; exact all g (closure_complete impls wf .refl)
  · intro root q member
    exact reach_resolves impls wf (closure_sound impls wf g q member) root

/-- Exact declarative closure condition: every generated head has one match. -/
theorem resolve_unique_closure (impls : List Impl) (wf : WellFormed impls) (g : Goal) :
    resolve impls wf g = .resolved ↔
      ∀ q ∈ closure impls wf g, ∃ i, Unique impls q i := by
  constructor
  · intro root q member
    have resolved := reach_resolves impls wf (closure_sound impls wf g q member)
      ((RoleConstraints.resolve_exact impls wf g).mp root)
    obtain ⟨i, selected, _⟩ := (resolve_resolved_iff impls wf q).mp
      ((RoleConstraints.resolve_exact impls wf q).mpr resolved)
    exact ⟨i, (unique_exact impls q i).mp selected⟩
  · intro all
    obtain ⟨i, unique⟩ := all g (closure_complete impls wf .refl)
    apply (resolve_resolved_iff impls wf g).mpr
    refine ⟨i, (unique_exact impls g i).mpr unique, ?_⟩
    intro c member
    apply (resolve_unique_closure impls wf _).mpr
    intro q included
    exact all q (closure_complete impls wf
      (.step (.child i _ c unique (matched_head unique.2.1) member)
        (closure_sound impls wf _ q included)))
termination_by argsSize g.args
decreasing_by
  simpa only [Goal.subst, matched_head unique.2.1] using
    size_decreases (wf i unique.1) member (matchingSubst i.head g.args)

/-- A missing head is stated without consulting an executable resolver. -/
def Missing (impls : List Impl) (g : Goal) : Prop :=
  ∀ i ∈ impls, ¬ Matches i g

theorem missing_exact (impls : List Impl) (g : Goal) :
    candidates impls g = [] ↔ Missing impls g := by
  constructor
  · intro empty i member matched
    have found := mem_candidates.mpr ⟨member, matched⟩
    simp [empty] at found
  · intro missing
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro i member
    have found := mem_candidates.mp member
    exact missing i found.1 found.2

/-- No path through an overlapping head is expanded, matching existing policy. -/
theorem overlap_reach (impls : List Impl) (wf : WellFormed impls) (g : Goal) :
    ReachesOverlap impls g ↔ ∃ q, Reach impls g q ∧ HeadOverlap impls q := by
  constructor
  · intro overlap
    induction overlap with
    | here h => exact ⟨_, .refl, h⟩
    | @descend g i c selected member _ ih =>
        obtain ⟨q, reachable, overlap⟩ := ih
        have unique := (unique_exact impls g i).mp selected
        exact ⟨q, .step (.child i _ c unique (matched_head unique.2.1) member) reachable, overlap⟩
  · rintro ⟨q, reachable, overlap⟩
    induction reachable with
    | refl => exact .here overlap
    | step edge _ ih =>
        cases edge with
        | child i σ c unique head member =>
            apply ReachesOverlap.descend ((unique_exact impls _ i).mpr unique) member
            rw [matched_constraint (wf i unique.1) σ head member]
            exact ih overlap

theorem ambiguous_exact (impls : List Impl) (wf : WellFormed impls) (g : Goal) :
    resolve impls wf g = .ambiguous ↔
      ∃ q ∈ closure impls wf g, ∃ i ∈ impls, ∃ j ∈ impls,
        i ≠ j ∧ Matches i q ∧ Matches j q := by
  rw [resolve_ambiguous_iff, overlap_reach impls wf]
  simp only [← closure_exact impls wf, head_overlap_iff]

/-- Missing children are retained even if another sibling is overlapping.
Ambiguity wins only in the final classification, not by dropping that child. -/
theorem noImpl_exact (impls : List Impl) (wf : WellFormed impls) (g : Goal) :
    resolve impls wf g = .noImpl ↔
      (∀ q ∈ closure impls wf g, ¬ HeadOverlap impls q) ∧
      ∃ q ∈ closure impls wf g, Missing impls q := by
  have ambiguous : resolve impls wf g = .ambiguous ↔
      ∃ q ∈ closure impls wf g, HeadOverlap impls q := by
    rw [resolve_ambiguous_iff, overlap_reach impls wf]
    simp only [← closure_exact impls wf]
  constructor
  · intro failed
    have noOverlap : ∀ q ∈ closure impls wf g, ¬ HeadOverlap impls q := by
      intro q member overlap
      have bad := ambiguous.mpr ⟨q, member, overlap⟩
      rw [failed] at bad
      contradiction
    refine ⟨noOverlap, ?_⟩
    apply Classical.byContradiction
    intro absent
    have all : ∀ q ∈ closure impls wf g, ∃ i, Unique impls q i := by
      intro q member
      cases selected : candidates impls q with
      | nil => exact False.elim (absent ⟨q, member, (missing_exact impls q).mp selected⟩)
      | cons i rest =>
          cases rest with
          | nil => exact ⟨i, (unique_exact impls q i).mp selected⟩
          | cons j rest => exact False.elim (noOverlap q member (by simp [HeadOverlap, selected]))
    have success := (resolve_unique_closure impls wf g).mpr all
    rw [failed] at success
    contradiction
  · rintro ⟨noOverlap, q, member, missing⟩
    cases result : resolve impls wf g with
    | noImpl => rfl
    | ambiguous =>
        obtain ⟨q, member, overlap⟩ := ambiguous.mp result
        exact False.elim (noOverlap q member overlap)
    | resolved =>
        obtain ⟨i, unique⟩ := (resolve_unique_closure impls wf g).mp result q member
        exact False.elim (missing i unique.1 unique.2.1)

/-- Classification inspects the complete computed finite closure. -/
def classify (impls : List Impl) (wf : WellFormed impls) (g : Goal) : Result :=
  if (closure impls wf g).any (fun q => decide (2 ≤ (candidates impls q).length)) then .ambiguous
  else if (closure impls wf g).any (fun q => (candidates impls q).isEmpty) then .noImpl
  else .resolved

/-- No missing child or ambiguous sibling is lost by finite source registration. -/
theorem classify_eq_resolve (impls : List Impl) (wf : WellFormed impls) (g : Goal) :
    classify impls wf g = resolve impls wf g := by
  have overlap : (closure impls wf g).any
      (fun q => decide (2 ≤ (candidates impls q).length)) = true ↔
      resolve impls wf g = .ambiguous := by
    rw [resolve_ambiguous_iff, overlap_reach impls wf]
    simp only [List.any_eq_true, decide_eq_true_eq, ← closure_exact impls wf, HeadOverlap]
  have missing : (closure impls wf g).any (fun q => (candidates impls q).isEmpty) = true ↔
      ∃ q ∈ closure impls wf g, Missing impls q := by
    simp only [List.any_eq_true, List.isEmpty_iff, missing_exact]
  unfold classify
  split
  · rename_i found; exact (overlap.mp found).symm
  · rename_i absent
    split
    · rename_i found
      apply Eq.symm
      apply (noImpl_exact impls wf g).mpr
      refine ⟨?_, missing.mp found⟩
      intro q member over
      apply absent
      apply overlap.mpr
      exact (resolve_ambiguous_iff impls wf g).mpr
        ((overlap_reach impls wf g).mpr ⟨q, closure_sound impls wf g q member, over⟩)
    · rename_i noMissing
      cases result : resolve impls wf g with
      | resolved => rfl
      | ambiguous => exact False.elim (absent (overlap.mpr result))
      | noImpl => exact False.elim (noMissing (missing.mpr ((noImpl_exact impls wf g).mp result).2))

open CommonRoleSourceRoleObligations (Obligation Package)
open CommonRoleStructuralAssociatedTemplates (generate)

/-- The source receiver is retained while the actual where tree is registered. -/
def registerOne (impls : List Impl) (wf : WellFormed impls)
    (heads : Nat → Inference.Base) (o : Obligation) : List (Nat × Goal) :=
  (closure impls wf (generate o.template (heads o.receiver))).map fun g => (o.receiver, g)

/-- Each registered goal has exactly a root source owner and a declaration path. -/
theorem registered_exact (impls : List Impl) (wf : WellFormed impls)
    (heads : Nat → Inference.Base) (o : Obligation) (owner : Nat) (g : Goal) :
    (owner, g) ∈ registerOne impls wf heads o ↔
      owner = o.receiver ∧ Reach impls (generate o.template (heads o.receiver)) g := by
  simp only [registerOne, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨q, member, receiver, rfl⟩
    exact ⟨receiver.symm, closure_sound impls wf _ _ member⟩
  · rintro ⟨rfl, reachable⟩
    exact ⟨g, closure_complete impls wf reachable, rfl, rfl⟩

def runOne (impls : List Impl) (wf : WellFormed impls)
    (heads : Nat → Inference.Base) (o : Obligation) : Bool :=
  decide (argsBound (generate o.template (heads o.receiver)).args = 0) &&
    decide (classify impls wf (generate o.template (heads o.receiver)) = .resolved)

theorem run_one_agrees (impls : List Impl) (wf : WellFormed impls)
    (heads : Nat → Inference.Base) (o : Obligation) :
    runOne impls wf heads o = CommonRoleSourceRoleObligations.runOne impls wf heads o := by
  simp only [runOne, CommonRoleSourceRoleObligations.runOne, classify_eq_resolve]

/-- Every registered descendant of a successfully discharged source obligation
has independent resolution evidence, including every source-ordered sibling. -/
theorem registered_resolves (impls : List Impl) (wf : WellFormed impls)
    (heads : Nat → Inference.Base) (o : Obligation)
    (success : runOne impls wf heads o = true) (owner : Nat) (g : Goal)
    (member : (owner, g) ∈ registerOne impls wf heads o) :
    RoleConstraints.Resolves impls g := by
  have selected := (Bool.and_eq_true_iff.mp success).2
  have resolved := of_decide_eq_true selected
  rw [classify_eq_resolve] at resolved
  exact reach_resolves impls wf ((registered_exact impls wf heads o owner g).mp member).2
    ((RoleConstraints.resolve_exact impls wf _).mp resolved)

def runSource (impls : List Impl) (wf : WellFormed impls) (roles : RoleDecls)
    (src : CommonRoleAssociatedClauseExtraction.Source) (heads : Nat → Inference.Base) : Bool :=
  match CommonRoleSourceRoleObligations.check roles src with
  | none => false
  | some p => p.obligations.all (runOne impls wf heads)

/-- The real checked source entry now has a computed recursive where closure.
External source inference and general interval refinement remain outside. -/
theorem run_source_agrees (impls : List Impl) (wf : WellFormed impls) (roles : RoleDecls)
    (src : CommonRoleAssociatedClauseExtraction.Source) (heads : Nat → Inference.Base) :
    runSource impls wf roles src heads =
      CommonRoleSourceRoleObligations.runSource impls wf roles src heads := by
  have same : runOne impls wf heads = CommonRoleSourceRoleObligations.runOne impls wf heads :=
    funext (run_one_agrees impls wf heads)
  cases checked : CommonRoleSourceRoleObligations.check roles src <;>
    simp [runSource, CommonRoleSourceRoleObligations.runSource,
      CommonRoleSourceRoleObligations.runRoles, checked, same]

theorem run_source_exact (impls : List Impl) (wf : WellFormed impls) (roles : RoleDecls)
    (src : CommonRoleAssociatedClauseExtraction.Source) (heads : Nat → Inference.Base) :
    runSource impls wf roles src heads = true ↔
      CommonRoleSourceRoleObligations.ValidSource roles src ∧
      ∀ c ∈ src, CommonRoleSourceRoleObligations.Discharges impls heads c := by
  rw [run_source_agrees, CommonRoleSourceRoleObligations.run_source_exact]

/-- Declaration validation constructs the termination certificate internally. -/
def checkedClassify (impls : List Impl) (g : Goal) : CheckedRoles.Result :=
  if accepted : CheckedRoles.checkDatabase impls = true then
    .answer (classify impls ((CheckedRoles.checkDatabase_exact impls).mp accepted) g)
  else .invalidDeclarations

theorem checked_agrees (impls : List Impl) (g : Goal) :
    checkedClassify impls g = CheckedRoles.resolve impls g := by
  simp only [checkedClassify, CheckedRoles.resolve, classify_eq_resolve]

theorem checked_exact (impls : List Impl) (g : Goal) :
    checkedClassify impls g = .answer .resolved ↔
      WellFormed impls ∧ RoleConstraints.Resolves impls g := by
  rw [checked_agrees, CheckedRoles.resolve_exact]

end Yulang.CommonRoleGeneratedWhereClosure
