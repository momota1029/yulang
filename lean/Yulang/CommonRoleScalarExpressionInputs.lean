import Yulang.CommonRoleAnnotatedLiteralInputs

/-!
# Checked annotated scalar expressions

Existing literal, variable and let expressions form a pure finite fragment.
The evaluator is connected to existing presence typing, including both let rules.
Unsupported syntax is a fragment boundary, not a language rejection.
-/
namespace Yulang.CommonRoleScalarExpressionInputs
open Inference (Expr Base)
open Core.PresenceGeneration (Typing BindingTyping Comp)

inductive Evaluates : List Base → Expr → Base → Prop
  | lit : Evaluates Γ (.lit head) head
  | var : Γ[n]? = some head → Evaluates Γ (.var n) head
  | letE : Evaluates Γ value a → Evaluates (a :: Γ) body b →
      Evaluates Γ (.letE value body) b

def infer (Γ : List Base) : Expr → Option Base
  | .lit head => some head
  | .var n => Γ[n]?
  | .letE value body => (infer Γ value).bind fun head => infer (head :: Γ) body
  | _ => none

theorem infer_exact (Γ : List Base) (e : Expr) (head : Base) :
    infer Γ e = some head ↔ Evaluates Γ e head := by
  constructor
  · intro h
    induction e generalizing Γ head with
    | lit b => simp only [infer, Option.some.injEq] at h; subst head; exact .lit
    | var n => exact .var h
    | letE value body ihv ihb =>
      simp only [infer, Option.bind_eq_some_iff] at h
      obtain ⟨a, hv, hb⟩ := h
      exact .letE (ihv Γ a hv) (ihb (a :: Γ) head hb)
    | _ => simp [infer] at h
  · intro h
    induction h with
    | lit => rfl
    | var h => exact h
    | letE _ _ ihv ihb => simp [infer, ihv, ihb]

abbrev Env := List (Core.PresenceGeneration.Binding Common.model)

def LowerEnv (heads : List Base) (Γ : Env) : Prop :=
  ∀ (n : Nat) (head : Base), heads[n]? = some head → ∀ binding, Γ[n]? = some binding →
    ∀ c, BindingTyping Common.model binding c → Common.Subtype (.base head) c.1

theorem lowerEnv_cons (heads : List Base) (Γ : Env) (head : Base)
    (binding : Core.PresenceGeneration.Binding Common.model)
    (tail : LowerEnv heads Γ)
    (first : ∀ c, BindingTyping Common.model binding c → Common.Subtype (.base head) c.1) :
    LowerEnv (head :: heads) (binding :: Γ) := by
  intro n b hb x hx c typed
  cases n with
  | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hb hx
            subst b; subst x; exact first c typed
  | succ n => exact tail n b hb x hx c typed

/-- Every existing typing of a scalar evaluation retains its scalar lower bound.
The environment condition also covers captured polymorphic let bindings. -/
theorem evaluates_lower (evaluated : Evaluates heads e head) :
    ∀ Γ, LowerEnv heads Γ → ∀ c, Typing Common.model Γ e c →
      Common.Subtype (.base head) c.1 := by
  induction evaluated with
  | lit => intro Γ env c typed; cases typed with | lit h => exact h.1
  | var lookup =>
      intro Γ env c typed
      cases typed with | var get bt => exact env _ _ lookup _ get c bt
  | letE ev eb ihv ihb =>
      intro Γ env c typed
      cases typed with
      | letValue _ _ body =>
          apply ihb _ (lowerEnv_cons _ _ _ _ env ?_) _ body
          intro d bt
          cases bt with
          | poly value _ => exact ihv Γ env (Comp.pure Common.model d.1) value
      | letComputed value body le =>
          have lower := ihv Γ env _ value
          have result := ihb _ (lowerEnv_cons _ _ _ _ env ?_) _ body
          · exact Common.subtype_trans result le.1
          · intro d bt
            cases bt with | mono bound => exact Common.subtype_trans lower bound.1

def canonicalEnv (heads : List Base) : Env :=
  heads.map fun head => .mono (Comp.pure Common.model (.base head))

/-- The scalar evaluator has an existing declarative typing at every supertype
of its result. It does not force a scalar upper bound without an annotation. -/
theorem evaluates_typed (evaluated : Evaluates heads e head) :
    ∀ value, Common.Subtype (.base head) value →
      Typing Common.model (canonicalEnv heads) e (Comp.pure Common.model value) := by
  induction evaluated with
  | lit => intro value lower; exact .lit ⟨lower, Common.rowLe_refl _⟩
  | @var Γ n head lookup =>
      intro value lower
      apply Typing.var (b := .mono (Comp.pure Common.model (.base head)))
      · simp [canonicalEnv, lookup]
      · exact .mono ⟨lower, Common.rowLe_refl _⟩
  | @letE Γ e a body b ev eb ihv ihb =>
      intro value lower
      apply Typing.letComputed (ihv (.base a) (Common.subtype_refl _)) (ihb value lower)
      exact ⟨Common.subtype_refl _, fun _ h => h.elim id id⟩

def Meaning (e : Expr) (annotation : Base) (value : Common.Ty) : Prop :=
  Typing Common.model [] e (Comp.pure Common.model value) ∧
    Common.Subtype value (.base annotation)

/-- Within the independently supported fragment, annotation checking is exact. -/
theorem annotation_exact (evaluated : Evaluates [] e head) (annotation : Base) :
    infer [] e = some annotation ↔ ∃ value, Meaning e annotation value := by
  constructor
  · intro checked
    have same : head = annotation := Option.some.inj
      (((infer_exact [] e head).mpr evaluated).symm.trans checked)
    subst annotation
    exact ⟨.base head, evaluates_typed evaluated _ (Common.subtype_refl _), Common.subtype_refl _⟩
  · rintro ⟨value, typed, upper⟩
    have lower := evaluates_lower evaluated [] (by intro n b h; simp at h) _ typed
    have same := (CommonRigidHeadInspection.base_iff head annotation).mp
      (Common.subtype_trans lower upper)
    simpa only [same] using (infer_exact [] e head).mpr evaluated

/-- Checked scalar annotations yield exactly the existing typing and upper bound. -/
theorem meaning_exact (evaluated : Evaluates [] e annotation) (value : Common.Ty) :
    Meaning e annotation value ↔ Common.Equivalent value (.base annotation) := by
  constructor
  · rintro ⟨typed, upper⟩
    exact ⟨upper, evaluates_lower evaluated [] (by intro n b h; simp at h) _ typed⟩
  · intro equivalent
    exact ⟨evaluates_typed evaluated value equivalent.2, equivalent.1⟩

open Roles
open CommonRoleAssociatedClauseExtraction (Source Clause Equation Step)
open CommonRoleSourceRoleObligations (ValidSource Discharges)
abbrev Binding := CommonRoleAnnotatedLiteralInputs.Binding
abbrev Bindings := List Binding

def Valid (bindings : Bindings) : Prop :=
  ∀ b ∈ bindings, infer [] b.value = some b.annotation

instance (bindings : Bindings) : Decidable (Valid bindings) :=
  inferInstanceAs (Decidable (∀ b ∈ bindings, infer [] b.value = some b.annotation))

/-- Whole-list validation is exactly the independent source expression judgment. -/
theorem valid_exact (bindings : Bindings) :
    Valid bindings ↔ ∀ b ∈ bindings, Evaluates [] b.value b.annotation := by
  simp only [Valid, infer_exact]

def lower (bindings : Bindings) : CommonRoleNamedSourceEntry.Assumptions :=
  bindings.map fun b => (b.name, b.annotation)

inductive Seed (bindings : Bindings) : Nat → Base → Prop
  | binding (b : Binding) : b ∈ bindings → Evaluates [] b.value b.annotation →
      Seed bindings b.name b.annotation

theorem lower_exact (bindings : Bindings) (valid : Valid bindings)
    (name : Nat) (head : Base) :
    (name, head) ∈ lower bindings ↔ Seed bindings name head := by
  constructor
  · intro member
    obtain ⟨b, hb, same⟩ := List.mem_map.mp member
    cases same
    exact .binding b hb ((infer_exact [] b.value b.annotation).mp (valid b hb))
  · intro seed
    cases seed with
    | binding b hb _ => exact List.mem_map.mpr ⟨b, hb, rfl⟩

inductive Derives (env : AssocEnv) (roles : RoleDecls) (src : Source)
    (bindings : Bindings) : Nat → Base → Prop
  | initial {name head} : Seed bindings name head → Derives env roles src bindings name head
  | equation (c : Clause) (e : Equation) {head result} :
      c ∈ src → e ∈ c.equations → Derives env roles src bindings c.receiver head →
      Step env roles c e head result → Derives env roles src bindings e.output result

theorem derives_exact (env : AssocEnv) (roles : RoleDecls) (src : Source)
    (bindings : Bindings) (valid : Valid bindings) (name : Nat) (head : Base) :
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

theorem models_bindings (env : AssocEnv) (roles : RoleDecls) (src : Source)
    (bindings : Bindings) (valid : Valid bindings) (values : Nat → Common.Ty)
    (facts : ∀ name ∈ CommonRoleNamedSourceEntry.names src, ∀ head,
      Derives env roles src bindings name head → Common.Equivalent (values name) (.base head))
    (b : Binding) (member : b ∈ bindings)
    (present : b.name ∈ CommonRoleNamedSourceEntry.names src) :
    Meaning b.value b.annotation (values b.name) := by
  have evaluated := (infer_exact [] b.value b.annotation).mp (valid b member)
  exact (meaning_exact evaluated _).mpr
    (facts b.name present b.annotation (.initial (.binding b member evaluated)))

def run (env : AssocEnv) (roles : RoleDecls) (wf : WellFormed env.cores)
    (src : Source) (bindings : Bindings) : Bool :=
  if Valid bindings then
    let allocated := CommonRoleComputedSourceAllocation.allocate src (lower bindings)
    CommonRoleNamedSourceEntry.runSource env roles wf allocated.1 allocated.2
  else false

/-- Arbitrary finite original expressions and source clauses, with independent
scalar-evaluation seeds. No solver success, equality atoms, model or fuel input. -/
theorem run_exact (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (src : Source) (bindings : Bindings) :
    run env roles wf src bindings = true ↔
      (∀ b ∈ bindings, Evaluates [] b.value b.annotation) ∧ ValidSource roles src ∧
      Models env roles src bindings ∧ ∀ c ∈ src, ∃ head,
        Derives env roles src bindings c.receiver head ∧ Discharges env.cores (fun _ => head) c := by
  rw [← valid_exact]
  by_cases valid : Valid bindings
  · simp only [run, ite_eq_left valid,
      CommonRoleComputedSourceAllocation.allocated_readiness env roles wf awf]
    rw [CommonRoleNamedSourceEntry.run_source_exact env roles wf awf]
    simp only [valid, true_and, models_exact env roles src bindings valid,
      derives_exact env roles src bindings valid]
  · simp [run, valid]

end Yulang.CommonRoleScalarExpressionInputs
