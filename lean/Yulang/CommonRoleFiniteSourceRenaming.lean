import Yulang.CommonRoleNamedSourceRenaming

/-!
# Checked renaming on the computed finite source support

Names outside source and input need not have distinct images. Input names are
included even when absent from source, to prevent capture of unrelated seeds.
The checker is a sufficient representation-safety condition, not a language
rejection criterion or a necessary condition for equal readiness results.
-/
namespace Yulang.CommonRoleFiniteSourceRenaming
open Roles
open CommonRoleAssociatedClauseExtraction (Clause Source Equation Step)
open CommonRoleSourceRoleObligations (ValidSource Discharges)
open CommonRoleNamedSourceEntry (Assumptions Derives Models names runSource)
open CommonRoleNamedSourceRenaming

def support (src : Source) (input : Assumptions) : List Nat :=
  names src ++ input.map Prod.fst

def CollisionFree (f : Nat → Nat) (src : Source) (input : Assumptions) : Prop :=
  ∀ a ∈ support src input, ∀ b ∈ support src input, f a = f b → a = b

instance (f : Nat → Nat) (src : Source) (input : Assumptions) :
    Decidable (CollisionFree f src input) :=
  inferInstanceAs (Decidable (∀ a ∈ support src input, ∀ b ∈ support src input,
    f a = f b → a = b))

def check (f : Nat → Nat) (src : Source) (input : Assumptions) : Bool :=
  decide (CollisionFree f src input)

theorem check_exact (f : Nat → Nat) (src : Source) (input : Assumptions) :
    check f src input = true ↔ CollisionFree f src input := by simp [check]

theorem check_fails (f : Nat → Nat) (src : Source) (input : Assumptions) :
    check f src input = false ↔
      ∃ a ∈ support src input, ∃ b ∈ support src input, f a = f b ∧ a ≠ b := by
  rw [check, decide_eq_false_iff_not]
  classical
  simp [CollisionFree]

/-- Every independent fact has a finite source or initial-assumption origin. -/
theorem derives_supported (env : AssocEnv) (roles : RoleDecls)
    (src : Source) (input : Assumptions) (name : Nat) (head : Inference.Base)
    (derived : Derives env roles src input name head) : name ∈ support src input := by
  cases derived with
  | initial member => exact List.mem_append_right _ (List.mem_map.mpr ⟨_, member, rfl⟩)
  | equation c e hc he _ _ =>
    exact List.mem_append_left _ ((CommonRoleNamedSourceEntry.names_member src _).mpr
      ⟨c, hc, Or.inr ⟨e, he, rfl⟩⟩)

/-- Reflection needs distinct images only for names that the finite input can use. -/
theorem derives_original (f : Nat → Nat) (safe : CollisionFree f src input)
    (env : AssocEnv) (roles : RoleDecls) (name : Nat) (head : Inference.Base)
    (derived : Derives env roles (renameSource f src) (renameInput f input) name head) :
    ∃ old, f old = name ∧ Derives env roles src input old head := by
  induction derived with
  | @initial n h mem =>
    obtain ⟨⟨old, base⟩, member, same⟩ := List.mem_map.mp mem
    have pair : f old = n ∧ base = h := Prod.mk.inj same
    rcases pair with ⟨h, rfl⟩
    exact ⟨old, h, .initial member⟩
  | equation c e hc he _ step ih =>
    obtain ⟨original, member, rfl⟩ := List.mem_map.mp hc
    obtain ⟨equation, equationMember, rfl⟩ := List.mem_map.mp he
    obtain ⟨old, same, previous⟩ := ih
    have receiverMem : original.receiver ∈ support src input :=
      List.mem_append_left _ ((CommonRoleNamedSourceEntry.names_member src _).mpr
        ⟨original, member, Or.inl rfl⟩)
    have oldEq : old = original.receiver :=
      safe old (derives_supported env roles src input old _ previous) _ receiverMem same
    subst old
    exact ⟨equation.output, rfl, .equation original equation member equationMember previous
      ((step_rename f env roles original equation _ _).mp step)⟩

/-- Exact evidence at every supported name, without global injectivity. -/
theorem derives_exact (f : Nat → Nat) (safe : CollisionFree f src input)
    (env : AssocEnv) (roles : RoleDecls) (name : Nat)
    (member : name ∈ support src input) (head : Inference.Base) :
    Derives env roles (renameSource f src) (renameInput f input) (f name) head ↔
      Derives env roles src input name head := by
  constructor
  · intro derived
    obtain ⟨old, same, previous⟩ := derives_original f safe env roles _ _ derived
    exact safe old (derives_supported env roles src input old head previous) name member same ▸ previous
  · exact derives_rename f env roles src input name head

private noncomputable def originalName (f : Nat → Nat) (domain : List Nat) (name : Nat) : Nat := by
  classical
  exact if h : ∃ old ∈ domain, f old = name then Classical.choose h else 0

private theorem original_image (f : Nat → Nat) (safe : CollisionFree f src input)
    (name : Nat) (member : name ∈ support src input) :
    originalName f (support src input) (f name) = name := by
  unfold originalName
  split
  · rename_i h
    exact safe _ (Classical.choose_spec h).1 name member (Classical.choose_spec h).2
  · rename_i h
    exact False.elim (h ⟨name, member, rfl⟩)

/-- No caller valuation or global inverse is needed to preserve model existence. -/
theorem models_exact (f : Nat → Nat) (safe : CollisionFree f src input)
    (env : AssocEnv) (roles : RoleDecls) :
    Models env roles (renameSource f src) (renameInput f input) ↔ Models env roles src input := by
  constructor
  · rintro ⟨values, holds⟩
    refine ⟨fun name => values (f name), ?_⟩
    intro name member head derived
    exact holds (f name) ((names_rename f src _).mpr ⟨name, member, rfl⟩) head
      (derives_rename f env roles src input name head derived)
  · rintro ⟨values, holds⟩
    refine ⟨fun name => values (originalName f (support src input) name), ?_⟩
    intro name member head derived
    obtain ⟨old, oldMember, rfl⟩ := (names_rename f src name).mp member
    have supported : old ∈ support src input := List.mem_append_left _ oldMember
    change Common.Equivalent (values (originalName f (support src input) (f old))) (.base head)
    rw [original_image f safe old supported]
    exact holds old oldMember head ((derives_exact f safe env roles old supported head).mp derived)

/-- Both entries recheck, reallocate and resaturate; only finite collision freedom
and the inherited core/associated well-formedness assumptions are required. -/
theorem run_source_exact (f : Nat → Nat) (safe : CollisionFree f src input)
    (env : AssocEnv) (roles : RoleDecls) (wf : WellFormed env.cores)
    (awf : AssocWellFormed env roles) :
    runSource env roles wf (renameSource f src) (renameInput f input) =
      runSource env roles wf src input := by
  have obligations :
      (∀ c ∈ renameSource f src, ∃ head,
        Derives env roles (renameSource f src) (renameInput f input) c.receiver head ∧
          Discharges env.cores (fun _ => head) c) ↔
      (∀ c ∈ src, ∃ head, Derives env roles src input c.receiver head ∧
        Discharges env.cores (fun _ => head) c) := by
    constructor
    · intro h c member
      obtain ⟨head, derived, discharged⟩ := h (renameClause f c)
        (List.mem_map.mpr ⟨c, member, rfl⟩)
      have supported : c.receiver ∈ support src input :=
        List.mem_append_left _ ((CommonRoleNamedSourceEntry.names_member src _).mpr
          ⟨c, member, Or.inl rfl⟩)
      exact ⟨head, (derives_exact f safe env roles c.receiver supported head).mp derived,
        (discharge_rename f env.cores c head).mp discharged⟩
    · intro h c member
      obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
      obtain ⟨head, derived, discharged⟩ := h original originalMember
      exact ⟨head, derives_rename f env roles src input original.receiver head derived,
        (discharge_rename f env.cores original head).mpr discharged⟩
  have exactness :
      runSource env roles wf (renameSource f src) (renameInput f input) = true ↔
      runSource env roles wf src input = true := by
    rw [CommonRoleNamedSourceEntry.run_source_exact env roles wf awf,
      CommonRoleNamedSourceEntry.run_source_exact env roles wf awf,
      valid_source_rename, models_exact f safe, obligations]
  cases a : runSource env roles wf (renameSource f src) (renameInput f input) <;>
    cases b : runSource env roles wf src input <;> simp_all

/-- Rejection here means an unsafe encoding request, not a role diagnostic. -/
def renameChecked (f : Nat → Nat) (src : Source) (input : Assumptions) :
    Option (Source × Assumptions) :=
  if check f src input then some (renameSource f src, renameInput f input) else none

theorem rename_checked_exact (f : Nat → Nat) (src other : Source)
    (input more : Assumptions) :
    renameChecked f src input = some (other, more) ↔
      CollisionFree f src input ∧ other = renameSource f src ∧ more = renameInput f input := by
  cases h : check f src input with
  | false =>
    have collision : ¬ CollisionFree f src input := by
      intro safe
      have good := (check_exact f src input).mpr safe
      simp [h] at good
    simp [renameChecked, h, collision]
  | true =>
    have safe := (check_exact f src input).mp h
    simp [renameChecked, h, safe, eq_comm]

/-- A computed successful rename preserves the entire finite readiness result.
No injectivity proof is supplied externally, and no solver-success premise occurs. -/
theorem checked_readiness (f : Nat → Nat) (src other : Source)
    (input more : Assumptions) (checked : renameChecked f src input = some (other, more))
    (env : AssocEnv) (roles : RoleDecls) (wf : WellFormed env.cores)
    (awf : AssocWellFormed env roles) :
    runSource env roles wf other more = runSource env roles wf src input := by
  obtain ⟨safe, rfl, rfl⟩ := (rename_checked_exact f src other input more).mp checked
  exact run_source_exact f safe env roles wf awf

end Yulang.CommonRoleFiniteSourceRenaming
