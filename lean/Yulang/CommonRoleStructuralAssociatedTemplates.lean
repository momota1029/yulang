import Yulang.CommonRoleNamedAssociatedSourceModels

/-!
# Structural generation of finite associated goal templates

Only placeholder zero is in scope. Existing int/str materialization is used;
unsupported scalar encodings are blocked, not given a new language meaning.
Finite occurrence selection, source scoping and registry construction remain
external. This does not establish general parser adequacy or dynamic where B4.
-/
namespace Yulang.CommonRoleStructuralAssociatedTemplates
open Roles
open CommonRoleOrdinaryKnownness (encode Evidence)
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

mutual
  inductive Fill (payload : Term) : Term → Term → Prop
    | hole : Fill payload (.var 0) payload
    | app {k ts us} : Fills payload ts us → Fill payload (.app k ts) (.app k us)
  inductive Fills (payload : Term) : List Term → List Term → Prop
    | nil : Fills payload [] []
    | cons {t u ts us} : Fill payload t u → Fills payload ts us →
        Fills payload (t :: ts) (u :: us)
end

mutual
  theorem fill_exact (payload t u : Term) (scope_ok : t.bound ≤ 1) :
      Fill payload t u ↔ t.subst (fun _ => payload) = u := by
    cases t with
    | var v =>
      have : v = 0 := by simp only [Term.bound] at scope_ok; omega
      subst v
      constructor
      · intro h; cases h; rfl
      · intro h; cases h; exact .hole
    | app k ts =>
      constructor
      · intro h; cases h with
        | app hs => exact congrArg (Term.app k) ((fills_exact payload ts _ scope_ok).mp hs)
      · intro h
        cases h
        exact .app ((fills_exact payload ts _ scope_ok).mpr rfl)
  theorem fills_exact (payload : Term) (ts us : List Term) (scope_ok : argsBound ts ≤ 1) :
      Fills payload ts us ↔ substArgs (fun _ => payload) ts = us := by
    cases ts with
    | nil =>
      constructor
      · intro h; cases h; rfl
      · intro h; cases h; exact .nil
    | cons t ts =>
      have bounds : t.bound ≤ 1 ∧ argsBound ts ≤ 1 := by
        simpa only [argsBound, Nat.max_le] using scope_ok
      constructor
      · intro h; cases h with
        | cons ht hs => simp only [substArgs,
            (fill_exact payload t _ bounds.1).mp ht,
            (fills_exact payload ts _ bounds.2).mp hs]
      · intro h; cases h
        exact .cons ((fill_exact payload t _ bounds.1).mpr rfl)
          ((fills_exact payload ts _ bounds.2).mpr rfl)
end

mutual
  theorem fill_ground (payload t : Term) (ground : payload.bound = 0) :
      (t.subst (fun _ => payload)).bound = 0 := by
    cases t with
    | var _ => exact ground
    | app _ ts => exact fills_ground payload ts ground
  theorem fills_ground (payload : Term) (ts : List Term) (ground : payload.bound = 0) :
      argsBound (substArgs (fun _ => payload) ts) = 0 := by
    cases ts with
    | nil => rfl
    | cons t ts => simp [substArgs, argsBound, fill_ground payload t ground,
        fills_ground payload ts ground]
end

structure Template where
  goal : Goal
  scope_ok : argsBound goal.args ≤ 1

/-- Scope checking constructs the proof instead of asking for a scope oracle. -/
def check (g : Goal) : Option Template :=
  if h : argsBound g.args ≤ 1 then some ⟨g, h⟩ else none

theorem check_accepts (g : Goal) :
    (check g).isSome = true ↔ argsBound g.args ≤ 1 := by
  simp [check]

theorem checked_goal (g : Goal) (t : Template) (checked : check g = some t) :
    t.goal = g := by
  unfold check at checked
  split at checked
  · cases Option.some.inj checked; rfl
  · contradiction

/-- Unsupported scalar codes use an unbound guard sentinel. -/
def generate (t : Template) (head : Inference.Base) : Goal :=
  match encode head with
  | some payload => t.goal.subst (fun _ => payload)
  | none => ⟨t.goal.role, [.var 0]⟩

/-- Independent structural materialization, preserving role and argument order. -/
def Materializes (t : Template) (head : Inference.Base) (g : Goal) : Prop :=
  ∃ payload, encode head = some payload ∧ g.role = t.goal.role ∧
    Fills payload t.goal.args g.args

theorem encode_ground (head : Inference.Base) (payload : Term)
    (encoded : encode head = some payload) : payload.bound = 0 := by
  cases head <;> simp [encode] at encoded <;> cases encoded <;> rfl

/-- Generated closed goals are exactly independent structural materializations. -/
theorem materializes_exact (t : Template) (head : Inference.Base) (g : Goal) :
    Materializes t head g ↔ argsBound (generate t head).args = 0 ∧ generate t head = g := by
  cases encoded : encode head with
  | none => simp [Materializes, generate, encoded, argsBound, Term.bound]
  | some payload =>
    have ground := fills_ground payload t.goal.args (encode_ground head payload encoded)
    constructor
    · rintro ⟨value, enc, role, filled⟩
      have same : payload = value := Option.some.inj (encoded.symm.trans enc)
      subst value
      refine ⟨by simpa only [generate, encoded, Goal.subst] using ground, ?_⟩
      simp only [generate, encoded]
      change t.goal.subst (fun _ => payload) = g
      cases g
      simp only [Goal.subst, Goal.mk.injEq]
      exact ⟨role.symm, (fills_exact payload t.goal.args _ t.scope_ok).mp filled⟩
    · rintro ⟨_, same⟩
      have eqg : t.goal.subst (fun _ => payload) = g := by
        simpa only [generate, encoded] using same
      rw [← eqg]
      exact ⟨payload, encoded, rfl,
        (fills_exact payload t.goal.args _ t.scope_ok).mpr rfl⟩

theorem materializes_shape (t : Template) (head : Inference.Base) (g : Goal)
    (materialized : Materializes t head g) :
    g.role = t.goal.role ∧ g.args.length = t.goal.args.length := by
  obtain ⟨payload, _, role, filled⟩ := materialized
  rw [← (fills_exact payload t.goal.args g.args t.scope_ok).mp filled]
  exact ⟨role, substArgs_length _ _⟩

/-- Every declared placeholder occurrence carries the actual encoded payload;
a used receiver cannot be replaced with an unrelated constant goal. -/
theorem materializes_payload (t : Template) (head : Inference.Base) (g : Goal)
    (used : 0 < argsOccurrences 0 t.goal.args) (materialized : Materializes t head g) :
    ∃ payload, encode head = some payload ∧ matchingSubst t.goal.args g.args 0 = payload := by
  obtain ⟨payload, encoded, _, filled⟩ := materialized
  refine ⟨payload, encoded, ?_⟩
  rw [← (fills_exact payload t.goal.args g.args t.scope_ok).mp filled]
  exact matchingSubst_agrees t.goal.args (fun _ => payload) 0 used

structure Occurrence where
  receiver : Nat
  output : Nat
  name : Nat
  template : Template

abbrev Program := List Occurrence

def Occurrence.compile (q : Occurrence) : CommonRoleNamedAssociatedGraph.NamedOccurrence :=
  ⟨q.receiver, q.output, q.name, generate q.template⟩

def compile (p : Program) : CommonRoleNamedAssociatedGraph.Program := p.map Occurrence.compile

/-- A declarative source step uses a structural goal and independent declarations. -/
def Step (env : AssocEnv) (roles : RoleDecls) (q : Occurrence)
    (head result : Inference.Base) : Prop :=
  ∃ g, Materializes q.template head g ∧ RoleConstraints.Resolves env.cores g ∧
    ∃ rhs, AssocDerives env roles g q.name rhs ∧
      CommonRoleAssociatedStateFlow.scalar rhs = some result

theorem step_exact (env : AssocEnv) (roles : RoleDecls) (q : Occurrence)
    (head result : Inference.Base) :
    CommonRoleNamedAssociatedSourceModels.Associated env roles q.compile head result ↔
      Step env roles q head result := by
  constructor
  · rintro ⟨closed, resolved, rhs, derived, scalar⟩
    exact ⟨generate q.template head,
      (materializes_exact q.template head _).mpr ⟨closed, rfl⟩,
      resolved, rhs, derived, scalar⟩
  · rintro ⟨g, materialized, resolved, rhs, derived, scalar⟩
    obtain ⟨closed, rfl⟩ := (materializes_exact q.template head g).mp materialized
    exact ⟨closed, resolved, rhs, derived, scalar⟩

abbrev table (p : Program) := CommonRoleNamedAssociatedGraph.table (compile p)

/-- Source derivations do not inspect generated templates or resolver outputs. -/
inductive Derives (env : AssocEnv) (roles : RoleDecls)
    (p : Program) (s : State (table p).length) : Nat → Inference.Base → Prop
  | initial {name head} : CommonRoleNamedAssociatedSourceModels.Seed (compile p) s name head →
      Derives env roles p s name head
  | associated (q : Occurrence) {head result} : q ∈ p →
      Derives env roles p s q.receiver head → Step env roles q head result →
      Derives env roles p s q.output result

/-- Exact compilation for every finite structural program and old state. -/
theorem derives_exact (env : AssocEnv) (roles : RoleDecls) (p : Program)
    (s : State (table p).length) (name : Nat) (head : Inference.Base) :
    CommonRoleNamedAssociatedSourceModels.NamedDerives env roles (compile p) s name head ↔
      Derives env roles p s name head := by
  constructor
  · intro h
    induction h with
    | initial seed => exact .initial seed
    | @associated i head result _ step ih =>
      have bound : i.val < p.length := by simpa [compile] using i.isLt
      have lookup_eq : (compile p)[i.val] = (p[i.val]'bound).compile := by simp [compile]
      rw [lookup_eq] at step ih ⊢
      exact .associated p[i.val] (by simp) ih ((step_exact env roles _ _ _).mp step)
  · intro h
    induction h with
    | initial seed => exact .initial seed
    | @associated q head result member _ step ih =>
      obtain ⟨i, bound, same⟩ := List.getElem_of_mem member
      let j : Fin (compile p).length := ⟨i, by simpa [compile] using bound⟩
      have lookup_eq : (compile p)[j.val] = q.compile := by simp [compile, j, same]
      have result := CommonRoleNamedAssociatedSourceModels.NamedDerives.associated
        (p := compile p) (s := s) j
        (by simpa only [lookup_eq, Occurrence.compile] using ih)
        (by simpa only [lookup_eq] using (step_exact env roles q head result).mpr step)
      simpa only [lookup_eq, Occurrence.compile] using result

def run (env : AssocEnv) (roles : RoleDecls) (wf : WellFormed env.cores)
    (p : Program) (s : State (table p).length) :=
  CommonRoleNamedAssociatedSourceModels.run env roles wf (compile p) s

theorem run_evidence_exact (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (p : Program) (s : State (table p).length) (slot : Fin (table p).length)
    (head : Inference.Base) :
    Evidence (run env roles wf p s).atoms slot head ↔
      Derives env roles p s (CommonRoleSourceIdentity.source (table p) slot) head :=
  (CommonRoleNamedAssociatedSourceModels.run_evidence_exact env roles wf awf
    (compile p) s slot head).trans (derives_exact env roles p s _ head)

theorem run_source_exact (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (p : Program) (s : State (table p).length) (v : Fin (table p).length → Comp Common.model) :
    All Common.model v (run env roles wf p s).atoms ↔
      All Common.model v s.atoms ∧ ∃ values, CommonRoleSourceDescent.Factors (table p) v values ∧
        ∀ name head, Derives env roles p s name head →
          Common.Equivalent (values name) (.base head) := by
  rw [run, CommonRoleNamedAssociatedSourceModels.run_source_exact env roles wf awf]
  simp only [derives_exact]

theorem solver_source_exact (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (p : Program) (s : State (table p).length) :
    CommonRoleOpenPropagation.consistent (run env roles wf p s) = true ↔
      ∃ v : Fin (table p).length → Comp Common.model,
        All Common.model v s.atoms ∧ ∃ values,
          CommonRoleSourceDescent.Factors (table p) v values ∧
            ∀ name head, Derives env roles p s name head →
              Common.Equivalent (values name) (.base head) := by
  rw [CommonRoleOpenPropagation.consistent_exact]
  exact exists_congr (run_source_exact env roles wf awf p s)

end Yulang.CommonRoleStructuralAssociatedTemplates
