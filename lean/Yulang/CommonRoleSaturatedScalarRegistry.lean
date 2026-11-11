import Yulang.CommonRoleScalarRegistry
import Yulang.CommonRoleNamedOrdinaryInputs

/-!
# Named associated closure to scalar registry classification

A root source name is allocated internally after the existing mixed closure
computes its shared state. Independent source derivations characterize all four
scalar-adapter outcomes. Actual dictionaries hold in every named source model.
Existing associated-environment checks remain inputs. General structural
materialization, final where children and the full B4 source instance are not
claimed. Missing source names and inconsistent states are unavailable.
-/
namespace Yulang.CommonRoleSaturatedScalarRegistry
set_option maxHeartbeats 400000
open CommonRoleScalarDictionaryModels (Scalar)
open CommonRoleScalarRegistry (Entry Ready Outcome Implements)
open CommonRoleStructuralAssociatedTemplates (Program)
open CommonRoleNamedOrdinaryInputs (Input table name Derives OrdinaryModels)
open Core.PresenceGeneration (Comp)
open RoleDictionaries (Answer Plan)

/-- Choose an occurrence of the original name from the computed finite domain. -/
def lookup (names : List Nat) (root : Nat) : Option (Fin names.length) :=
  (List.finRange names.length).find? fun i => names[i] == root

theorem lookup_sound (names : List Nat) (root : Nat) (slot : Fin names.length)
    (found : lookup names root = some slot) : names[slot] = root := by
  have yes := List.find?_some (p := fun i : Fin names.length => names[i] == root) found
  exact beq_iff_eq.mp yes

theorem lookup_exists (names : List Nat) (root : Nat) :
    (∃ slot, lookup names root = some slot) ↔ root ∈ names := by
  constructor
  · rintro ⟨slot, found⟩
    rw [← lookup_sound names root slot found]
    exact List.getElem_mem _
  · intro member
    obtain ⟨index, bound, equal⟩ := List.getElem_of_mem member
    cases found : lookup names root with
    | some slot => exact ⟨slot, rfl⟩
    | none =>
      have absent := List.find?_eq_none.mp found
      exact False.elim (absent ⟨index, bound⟩ (by simp) (by simpa using equal))

/-- Scalar evidence is derived in original names; it is not read from the
materializer or from a chosen ordinary assignment. -/
def Known (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (program : Program)
    (input : Input) (root : Nat) (term : Roles.Term) : Prop :=
  ∃ scalar : Scalar, Derives env roles program input root scalar.base ∧ term = scalar.term

inductive Classify (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (program : Program)
    (input : Input) (entries : List Entry) (role root : Nat) : Outcome → Prop where
  | pending : (∀ term, ¬ Known env roles program input root term) →
      Classify env roles program input entries role root .pending
  | ready : Known env roles program input root term → Ready entries role term answer →
      Classify env roles program input entries role root (.ready answer)

theorem known_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (program : Program) (input : Input) (slot : Fin (table program input).length) (term : Roles.Term) :
    CommonRoleScalarRegistry.Known (CommonRoleNamedOrdinaryInputs.run env roles wf program input) slot term ↔
      Known env roles program input (name program input slot) term := by
  simp only [CommonRoleScalarRegistry.Known, Known,
    CommonRoleNamedOrdinaryInputs.run_evidence_exact env roles wf awf]

theorem classify_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (program : Program) (input : Input) (entries : List Entry) (role : Nat)
    (slot : Fin (table program input).length) (out : Outcome) :
    CommonRoleScalarRegistry.Classify entries role slot
      (CommonRoleNamedOrdinaryInputs.run env roles wf program input) out ↔
      Classify env roles program input entries role (name program input slot) out := by
  constructor
  · intro classified
    cases classified with
    | pending absent => exact .pending (fun term known => absent term ((known_exact env roles wf awf program input slot _).mpr known))
    | ready known ready => exact .ready ((known_exact env roles wf awf program input slot _).mp known) ready
  · intro classified
    cases classified with
    | pending absent => exact .pending (fun term known => absent term ((known_exact env roles wf awf program input slot _).mp known))
    | ready known ready => exact .ready ((known_exact env roles wf awf program input slot _).mpr known) ready

def run (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (wf : Roles.WellFormed env.cores)
    (program : Program) (input : Input) (entries : List Entry) (role root : Nat) : Option Outcome :=
  Option.bind (lookup (table program input) root) fun slot =>
    CommonRoleScalarRegistry.run entries role slot (CommonRoleNamedOrdinaryInputs.run env roles wf program input)

/-- Exact outer classification after computed source saturation. Every input
state and receiver slot is computed, and consistency is part of the iff. -/
theorem run_exact (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (program : Program) (input : Input) (entries : List Entry) (role root : Nat) (out : Outcome) :
    run env roles wf program input entries role root = some out ↔
      root ∈ table program input ∧ CommonRoleNamedOrdinaryInputs.Models env roles program input ∧
        Classify env roles program input entries role root out := by
  have models : (CommonRoleNamedOrdinaryInputs.run env roles wf program input).Models ↔
      CommonRoleNamedOrdinaryInputs.Models env roles program input :=
    (CommonRoleOpenPropagation.consistent_exact _).symm.trans
      (CommonRoleNamedOrdinaryInputs.solver_source_exact env roles wf awf program input)
  constructor
  · intro returned
    obtain ⟨slot, found, actual⟩ := Option.bind_eq_some_iff.mp returned
    have same : name program input slot = root := lookup_sound _ _ slot found
    obtain ⟨consistent, classified⟩ := (CommonRoleScalarRegistry.run_exact entries role slot _ out).mp actual
    refine ⟨(lookup_exists _ _).mp ⟨slot, found⟩, models.mp consistent, ?_⟩
    have source := (classify_exact env roles wf awf program input entries role slot out).mp classified
    simpa only [same] using source
  · rintro ⟨present, consistent, classified⟩
    obtain ⟨slot, found⟩ := (lookup_exists _ _).mpr present
    have same : name program input slot = root := lookup_sound _ _ slot found
    apply Option.bind_eq_some_iff.mpr
    refine ⟨slot, found, (CommonRoleScalarRegistry.run_exact entries role slot _ out).mpr ⟨models.mpr consistent, ?_⟩⟩
    apply (classify_exact env roles wf awf program input entries role slot out).mpr
    simpa only [same] using classified

/-- All ordinary and associated source facts hold in this original valuation. -/
def SourceModel (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (program : Program)
    (input : Input) (values : Nat → Common.Ty) : Prop :=
  OrdinaryModels input values ∧ ∀ root base,
    Derives env roles program input root base → Common.Equivalent (values root) (.base base)

/-- Selected dictionary evidence holds in every original source model after
associated saturation, with the actual declaration and every child retained. -/
theorem run_all_models (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (program : Program) (input : Input) (entries : List Entry) (role root : Nat) (dictionary : Plan)
    (returned : run env roles wf program input entries role root = some (.ready (.resolved dictionary)))
    (values : Nat → Common.Ty) (models : SourceModel env roles program input values) :
    Implements entries role (values root) dictionary := by
  have classified := ((run_exact env roles wf awf program input entries role root _).mp returned).2.2
  cases classified with
  | ready known ready =>
    cases ready with
    | selected unique =>
      obtain ⟨entry, member, rfl, sameRole, sameTerm⟩ := unique.1
      obtain ⟨scalar, derived, term⟩ := known
      have same : scalar = entry.scalar :=
        CommonRoleScalarRegistry.scalar_term_injective _ _ (term.symm.trans sameTerm)
      rw [same] at derived
      exact .leaf entry member sameRole (models.2 root entry.scalar.base derived)

/-- Visible-implementation order changes cannot affect the computed source
closure, classification or the literal selected dictionary. -/
theorem run_visible_set (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (program : Program) (input : Input)
    (first last : List Entry) (same : ∀ entry, entry ∈ first ↔ entry ∈ last) (role root : Nat) :
    run env roles wf program input first role root = run env roles wf program input last role root := by
  unfold run
  apply congrArg (fun f => Option.bind (lookup (table program input) root) f)
  funext slot
  exact CommonRoleScalarRegistry.run_visible_set first last same role slot
    (CommonRoleNamedOrdinaryInputs.run env roles wf program input)

/-- Reordering/duplicating original ordinary constraints preserves derived
knownness even if the concrete allocated slots change. -/
theorem known_input_congr (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (program : Program)
    (first last : Input) (same : ∀ q, q ∈ first ↔ q ∈ last) (root : Nat) (term : Roles.Term) :
    Known env roles program first root term ↔ Known env roles program last root term := by
  simp only [Known, CommonRoleNamedOrdinaryInputs.derives_congr env roles program first last same]

theorem classify_input_congr (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (program : Program)
    (first last : Input) (same : ∀ q, q ∈ first ↔ q ∈ last)
    (entries : List Entry) (role root : Nat) (out : Outcome) :
    Classify env roles program first entries role root out ↔
      Classify env roles program last entries role root out := by
  constructor
  · intro classified
    cases classified with
    | pending absent => exact .pending (fun term known => absent term ((known_input_congr env roles program first last same root term).mpr known))
    | ready known ready => exact .ready ((known_input_congr env roles program first last same root _).mp known) ready
  · intro classified
    cases classified with
    | pending absent => exact .pending (fun term known => absent term ((known_input_congr env roles program first last same root term).mp known))
    | ready known ready => exact .ready ((known_input_congr env roles program first last same root _).mpr known) ready

theorem domain_input_congr (program : Program) (first last : Input)
    (same : ∀ q, q ∈ first ↔ q ∈ last) (root : Nat) :
    root ∈ table program first ↔ root ∈ table program last := by
  have extra : root ∈ CommonRoleNamedOrdinaryInputs.extra first ↔
      root ∈ CommonRoleNamedOrdinaryInputs.extra last := by
    simp only [CommonRoleNamedOrdinaryInputs.extra, List.mem_eraseDups, List.mem_flatMap]
    constructor
    · rintro ⟨q, member, rootMember⟩; exact ⟨q, (same q).mp member, rootMember⟩
    · rintro ⟨q, member, rootMember⟩; exact ⟨q, (same q).mpr member, rootMember⟩
  simp only [table, CommonRoleAmbientMixedSource.table, List.mem_append, extra]

/-- Exact output and actual dictionary payload are invariant under ordinary
input reorder/duplication, despite reallocation of the source-name domain. -/
theorem run_input_congr (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
    (wf : Roles.WellFormed env.cores) (awf : Roles.AssocWellFormed env roles)
    (program : Program) (first last : Input) (same : ∀ q, q ∈ first ↔ q ∈ last)
    (entries : List Entry) (role root : Nat) :
    run env roles wf program first entries role root = run env roles wf program last entries role root := by
  have result (out : Outcome) : run env roles wf program first entries role root = some out ↔
      run env roles wf program last entries role root = some out := by
    rw [run_exact env roles wf awf, run_exact env roles wf awf,
      domain_input_congr program first last same,
      CommonRoleNamedOrdinaryInputs.models_congr env roles program first last same,
      classify_input_congr env roles program first last same]
  cases left : run env roles wf program first entries role root with
  | some out => exact ((result out).mp left).symm
  | none =>
    cases right : run env roles wf program last entries role root with
    | none => rfl
    | some out =>
      have impossible := (result out).mpr right
      rw [left] at impossible
      cases impossible

end Yulang.CommonRoleSaturatedScalarRegistry
