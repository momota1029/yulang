import Yulang.CommonRoleNamedSourceEntry

/-!
# Capture-avoiding renaming of original source identities

This preserves receiver/output identities, not role IDs, associated member IDs
or structural Goal binders. Injectivity is a hypothesis for reflection, never
an assumed language decision about which invocations must share a name.
-/
namespace Yulang.CommonRoleNamedSourceRenaming
open Roles
open CommonRoleAssociatedClauseExtraction (Clause Source Equation Step)
open CommonRoleSourceRoleObligations (ValidClause ValidSource Discharges)
open CommonRoleNamedSourceEntry (Assumptions Derives Models names runSource)

def renameEquation (f : Nat → Nat) (e : Equation) : Equation := ⟨e.name, f e.output⟩
def renameClause (f : Nat → Nat) (c : Clause) : Clause :=
  ⟨f c.receiver, c.goal, c.equations.map (renameEquation f)⟩
def renameSource (f : Nat → Nat) (src : Source) : Source := src.map (renameClause f)
def renameInput (f : Nat → Nat) (input : Assumptions) : Assumptions :=
  input.map fun entry => (f entry.1, entry.2)

/-- The independent equation judgment does not inspect the source name encoding. -/
theorem step_rename (f : Nat → Nat) (env : AssocEnv) (roles : RoleDecls)
    (c : Clause) (e : Equation) (head result : Inference.Base) :
    Step env roles (renameClause f c) (renameEquation f e) head result ↔
      Step env roles c e head result := Iff.rfl

theorem valid_clause_rename (f : Nat → Nat) (roles : RoleDecls) (c : Clause) :
    ValidClause roles (renameClause f c) ↔ ValidClause roles c := by
  simp [ValidClause, renameClause, renameEquation]

theorem valid_source_rename (f : Nat → Nat) (roles : RoleDecls) (src : Source) :
    ValidSource roles (renameSource f src) ↔ ValidSource roles src := by
  simp [ValidSource, renameSource, valid_clause_rename]

/-- Original name-domain membership is transported exactly, even for collisions. -/
theorem names_rename (f : Nat → Nat) (src : Source) (name : Nat) :
    name ∈ names (renameSource f src) ↔ ∃ old ∈ names src, f old = name := by
  simp only [CommonRoleNamedSourceEntry.names_member, renameSource, List.mem_map]
  constructor
  · rintro ⟨_, ⟨c, hc, rfl⟩, same | ⟨e, he, same⟩⟩
    · exact ⟨c.receiver, ⟨c, hc, Or.inl rfl⟩, same⟩
    · obtain ⟨original, member, rfl⟩ := List.mem_map.mp he
      exact ⟨original.output, ⟨c, hc, Or.inr ⟨original, member, rfl⟩⟩, same⟩
  · rintro ⟨old, ⟨c, hc, same | ⟨e, he, same⟩⟩, image⟩
    · exact ⟨renameClause f c, ⟨c, hc, rfl⟩, Or.inl (congrArg f same |>.trans image)⟩
    · exact ⟨renameClause f c, ⟨c, hc, rfl⟩, Or.inr
        ⟨renameEquation f e, List.mem_map.mpr ⟨e, he, rfl⟩, congrArg f same |>.trans image⟩⟩

/-- Forward transport allows arbitrary name maps; it does not assert reflection. -/
theorem derives_rename (f : Nat → Nat) (env : AssocEnv) (roles : RoleDecls)
    (src : Source) (input : Assumptions) (name : Nat) (head : Inference.Base)
    (derived : Derives env roles src input name head) :
    Derives env roles (renameSource f src) (renameInput f input) (f name) head := by
  induction derived with
  | initial mem => exact .initial (List.mem_map.mpr ⟨_, mem, rfl⟩)
  | equation c e hc he _ step ih =>
    exact .equation (renameClause f c) (renameEquation f e)
      (List.mem_map.mpr ⟨c, hc, rfl⟩) (List.mem_map.mpr ⟨e, he, rfl⟩) ih
      ((step_rename f env roles c e _ _).mpr step)

/-- Every renamed derivation has an original witness when names do not collide. -/
theorem derives_original (f : Nat → Nat) (injective : Function.Injective f)
    (env : AssocEnv) (roles : RoleDecls) (src : Source) (input : Assumptions)
    (name : Nat) (head : Inference.Base)
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
    have oldEq : old = original.receiver := injective same
    subst old
    exact ⟨equation.output, rfl, .equation original equation member equationMember previous
      ((step_rename f env roles original equation _ _).mp step)⟩

/-- Exact source-name evidence, without any caller allocation or state map. -/
theorem derives_rename_exact (f : Nat → Nat) (injective : Function.Injective f)
    (env : AssocEnv) (roles : RoleDecls) (src : Source) (input : Assumptions)
    (name : Nat) (head : Inference.Base) :
    Derives env roles (renameSource f src) (renameInput f input) (f name) head ↔
      Derives env roles src input name head := by
  constructor
  · intro derived
    obtain ⟨old, same, previous⟩ := derives_original f injective env roles src input _ _ derived
    exact injective same ▸ previous
  · exact derives_rename f env roles src input name head

private noncomputable def originalName (f : Nat → Nat) (name : Nat) : Nat := by
  classical
  exact if h : ∃ old, f old = name then Classical.choose h else 0

private theorem original_image (f : Nat → Nat) (injective : Function.Injective f) (name : Nat) :
    originalName f (f name) = name := by
  unfold originalName
  split
  · rename_i h
    exact injective (Classical.choose_spec h)
  · rename_i h
    exact False.elim (h ⟨name, rfl⟩)

/-- Models are transported both ways; no chosen valuation is a caller premise. -/
theorem models_rename_exact (f : Nat → Nat) (injective : Function.Injective f)
    (env : AssocEnv) (roles : RoleDecls) (src : Source) (input : Assumptions) :
    Models env roles (renameSource f src) (renameInput f input) ↔ Models env roles src input := by
  constructor
  · rintro ⟨values, holds⟩
    refine ⟨fun name => values (f name), ?_⟩
    intro name member head derived
    exact holds (f name) ((names_rename f src _).mpr ⟨name, member, rfl⟩) head
      (derives_rename f env roles src input name head derived)
  · rintro ⟨values, holds⟩
    refine ⟨fun name => values (originalName f name), ?_⟩
    intro name member head derived
    obtain ⟨old, oldMember, rfl⟩ := (names_rename f src name).mp member
    change Common.Equivalent (values (originalName f (f old))) (.base head)
    rw [original_image f injective old]
    exact holds old oldMember head
      ((derives_rename_exact f injective env roles src input old head).mp derived)

/-- Renaming only source identities leaves a fixed scalar discharge unchanged. -/
theorem discharge_rename (f : Nat → Nat) (impls : List Impl) (c : Clause)
    (head : Inference.Base) :
    Discharges impls (fun _ => head) (renameClause f c) ↔
      Discharges impls (fun _ => head) c := Iff.rfl

/-- Reallocation and resaturation after any injective source-name renaming have
exactly the same finite readiness. No success, model, package or fuel premise. -/
theorem run_source_rename (f : Nat → Nat) (injective : Function.Injective f)
    (env : AssocEnv) (roles : RoleDecls) (wf : WellFormed env.cores)
    (awf : AssocWellFormed env roles) (src : Source) (input : Assumptions) :
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
      exact ⟨head, (derives_rename_exact f injective env roles src input c.receiver head).mp derived,
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
      valid_source_rename, models_rename_exact f injective, obligations]
  cases a : runSource env roles wf (renameSource f src) (renameInput f input) <;>
    cases b : runSource env roles wf src input <;> simp_all

end Yulang.CommonRoleNamedSourceRenaming
