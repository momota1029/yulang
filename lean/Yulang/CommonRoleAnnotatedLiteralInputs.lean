import Yulang.CommonRoleComputedSourceAllocation

/-!
# Checked scalar annotations as finite source inputs

Only existing literal expressions with explicit matching scalar annotations are
supported. Nonliteral or unannotated expressions require a broader input layer;
failure of this check is not a language rejection. Scope-resolved source names
and grouped role clauses remain inputs. No dynamic children are generated.
-/
namespace Yulang.CommonRoleAnnotatedLiteralInputs
open Roles
open CommonRoleAssociatedClauseExtraction (Source Clause Equation Step)
open CommonRoleSourceRoleObligations (ValidSource Discharges)

structure Binding where
  name : Nat
  value : Inference.Expr
  annotation : Inference.Base
  deriving DecidableEq, Repr

abbrev Bindings := List Binding

def Valid (bindings : Bindings) : Prop :=
  ∀ b ∈ bindings, b.value = .lit b.annotation

instance (bindings : Bindings) : Decidable (Valid bindings) :=
  inferInstanceAs (Decidable (∀ b ∈ bindings, b.value = .lit b.annotation))

/-- An explicit scalar annotation, not a caller's ordinary equality atom. -/
def BindingMeaning (b : Binding) (value : Common.Ty) : Prop :=
  Core.PresenceGeneration.Typing Common.model [] b.value (Core.PresenceGeneration.Comp.pure Common.model value) ∧
    Common.Subtype value (.base b.annotation)

/-- In the checked fragment the lower bound from literal typing and the upper
bound from its annotation are exactly the paired scalar equality. -/
theorem binding_meaning_exact (b : Binding) (literal : b.value = .lit b.annotation)
    (value : Common.Ty) :
    BindingMeaning b value ↔ Common.Equivalent value (.base b.annotation) := by
  simp only [BindingMeaning, literal, Core.PresenceGeneration.Typing.lit_iff]
  change (Common.Subtype (.base b.annotation) value ∧
    Common.rowLe Common.rowEmpty Common.rowEmpty) ∧
    Common.Subtype value (.base b.annotation) ↔ _
  exact ⟨fun h => ⟨h.2, h.1.1⟩, fun h => ⟨⟨h.2, Common.rowLe_refl _⟩, h.1⟩⟩

/-- For arbitrary literal/annotation scalar pairs, the syntax check accepts
exactly when the existing declarative typing and annotation have a value model.
This is not an exact checker for nonliteral expressions. -/
theorem literal_check_exact (name : Nat) (literal annotation : Inference.Base) :
    Valid [⟨name, .lit literal, annotation⟩] ↔
      ∃ value, BindingMeaning ⟨name, .lit literal, annotation⟩ value := by
  constructor
  · intro valid
    have same : literal = annotation := by
      have h := valid ⟨name, .lit literal, annotation⟩ (by simp)
      simpa using h
    subst annotation
    exact ⟨.base literal, (binding_meaning_exact _ rfl _).mpr (Common.equivalent_refl _)⟩
  · rintro ⟨value, typed, upper⟩
    have lower := (Core.PresenceGeneration.Typing.lit_iff Common.model [] literal _).mp typed
    have same := (CommonRigidHeadInspection.base_iff literal annotation).mp
      (Common.subtype_trans lower.1 upper)
    subst annotation
    intro b member
    simpa using (List.mem_singleton.mp member ▸ (rfl :
      (Binding.mk name (.lit literal) literal).value = .lit literal))

/-- Literal typing alone leaves larger value types available. The annotation
upper bound cannot be manufactured from a literal's lower bound. -/
theorem literal_does_not_force_scalar :
    Core.PresenceGeneration.Typing Common.model [] (.lit .int)
      (Core.PresenceGeneration.Comp.pure Common.model (.union (.base .int) (.base .str))) ∧
    ¬ Common.Equivalent (.union (.base .int) (.base .str)) (.base .int) := by
  constructor
  · apply Core.PresenceGeneration.Typing.lit
    exact ⟨CommonBoundCoalescing.le_union_left _ _, Common.rowLe_refl _⟩
  · intro eq
    have included : Common.Subtype (.base .str) (.union (.base .int) (.base .str)) := by
      exact CommonBoundCoalescing.le_union_right _ _
    have impossible := Common.subtype_trans included eq.1
    have same := (CommonRigidHeadInspection.base_iff .str .int).mp impossible
    cases same

def lower (bindings : Bindings) : CommonRoleNamedSourceEntry.Assumptions :=
  bindings.map fun b => (b.name, b.annotation)

inductive Seed (bindings : Bindings) : Nat → Inference.Base → Prop
  | binding (b : Binding) : b ∈ bindings → b.value = .lit b.annotation →
      Seed bindings b.name b.annotation

theorem lower_exact (bindings : Bindings) (valid : Valid bindings)
    (name : Nat) (head : Inference.Base) :
    (name, head) ∈ lower bindings ↔ Seed bindings name head := by
  constructor
  · intro member
    obtain ⟨b, hb, same⟩ := List.mem_map.mp member
    cases same
    exact .binding b hb (valid b hb)
  · intro seed
    cases seed with
    | binding b hb _ => exact List.mem_map.mpr ⟨b, hb, rfl⟩

/-- Original bindings and grouped equations are the sole declarative inputs. -/
inductive Derives (env : AssocEnv) (roles : RoleDecls) (src : Source)
    (bindings : Bindings) : Nat → Inference.Base → Prop
  | initial {name head} : Seed bindings name head → Derives env roles src bindings name head
  | equation (c : Clause) (e : Equation) {head result} :
      c ∈ src → e ∈ c.equations → Derives env roles src bindings c.receiver head →
      Step env roles c e head result → Derives env roles src bindings e.output result

theorem derives_exact (env : AssocEnv) (roles : RoleDecls) (src : Source)
    (bindings : Bindings) (valid : Valid bindings) (name : Nat) (head : Inference.Base) :
    CommonRoleNamedSourceEntry.Derives env roles src (lower bindings) name head ↔
      Derives env roles src bindings name head := by
  constructor
  · intro derived
    induction derived with
    | initial member => exact .initial ((lower_exact bindings valid _ _).mp member)
    | equation c e hc he _ step ih => exact .equation c e hc he ih step
  · intro derived
    induction derived with
    | initial seed => exact .initial ((lower_exact bindings valid _ _).mpr seed)
    | equation c e hc he _ step ih => exact .equation c e hc he ih step

def Models (env : AssocEnv) (roles : RoleDecls) (src : Source) (bindings : Bindings) : Prop :=
  ∃ values : Nat → Common.Ty, ∀ name ∈ CommonRoleNamedSourceEntry.names src, ∀ head,
    Derives env roles src bindings name head → Common.Equivalent (values name) (.base head)

theorem models_exact (env : AssocEnv) (roles : RoleDecls) (src : Source)
    (bindings : Bindings) (valid : Valid bindings) :
    CommonRoleNamedSourceEntry.Models env roles src (lower bindings) ↔
      Models env roles src bindings := by
  simp only [CommonRoleNamedSourceEntry.Models, Models, derives_exact env roles src bindings valid]

/-- Every checked source binding in the source domain has its actual literal
and annotation meaning in each independent model, not just a chosen seed tag. -/
theorem models_bindings (env : AssocEnv) (roles : RoleDecls) (src : Source)
    (bindings : Bindings) (valid : Valid bindings) (values : Nat → Common.Ty)
    (facts : ∀ name ∈ CommonRoleNamedSourceEntry.names src, ∀ head,
      Derives env roles src bindings name head → Common.Equivalent (values name) (.base head))
    (b : Binding) (member : b ∈ bindings)
    (present : b.name ∈ CommonRoleNamedSourceEntry.names src) :
    BindingMeaning b (values b.name) :=
  (binding_meaning_exact b (valid b member) _).mpr
    (facts b.name present b.annotation (.initial (.binding b member (valid b member))))

/-- Computes validation, named inputs, canonical names and finite readiness.
No ordinary constraints or successful solving are provided by the caller. -/
def run (env : AssocEnv) (roles : RoleDecls) (wf : WellFormed env.cores)
    (src : Source) (bindings : Bindings) : Bool :=
  if Valid bindings then
    let allocated := CommonRoleComputedSourceAllocation.allocate src (lower bindings)
    CommonRoleNamedSourceEntry.runSource env roles wf allocated.1 allocated.2
  else false

/-- Soundness and completeness for this explicit literal-annotation fragment.
The independent side contains original bindings and source clauses, not the
computed assumptions, allocated slots or output of the solver. -/
theorem run_exact (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (src : Source) (bindings : Bindings) :
    run env roles wf src bindings = true ↔ Valid bindings ∧ ValidSource roles src ∧
      Models env roles src bindings ∧ ∀ c ∈ src, ∃ head,
        Derives env roles src bindings c.receiver head ∧ Discharges env.cores (fun _ => head) c := by
  by_cases valid : Valid bindings
  · simp only [run, ite_eq_left valid,
      CommonRoleComputedSourceAllocation.allocated_readiness env roles wf awf]
    rw [CommonRoleNamedSourceEntry.run_source_exact env roles wf awf]
    simp only [valid, true_and, models_exact env roles src bindings valid,
      derives_exact env roles src bindings valid]
  · simp [run, valid]

end Yulang.CommonRoleAnnotatedLiteralInputs
