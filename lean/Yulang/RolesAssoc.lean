import Yulang.Roles

/-!
# First-order associated types

Spec §6.1–6.3 (2026-11-05): bodies contain only constructors and head variables.
`Term` has no associated-type projection constructor, so instantiation cannot
recursively expand another associated type. Selection reuses `resolve` unchanged.
-/
namespace Yulang.Roles

/-- A signature is a finite-arity role with a partial map from names to defaults.
`some none` declares a required name; `none` means the name is undeclared.
Default variables are positional role parameters, not impl variables. -/
structure RoleDecl where
  arity : Nat
  assoc : Nat → Option (Option Term)
  defaultsScoped : ∀ name rhs, assoc name = some (some rhs) → rhs.bound ≤ arity

abbrev RoleDecls := Nat → RoleDecl

/-- Keep the original `Impl` and all its theorems unchanged. -/
structure AssocImpl where
  impl : Impl
  assoc : List (Nat × Term)
  /-- A dictionary representation; duplicate source declarations are not modeled. -/
  uniqueNames : (assoc.map Prod.fst).Nodup
  deriving DecidableEq, Repr

/-- Annotation coherence is a representation invariant: the same original impl
identity cannot carry two different bodies. This does not require nonoverlap. -/
structure AssocEnv where
  impls : List AssocImpl
  coherent : ∀ i ∈ impls, ∀ j ∈ impls, i.impl = j.impl → i.assoc = j.assoc

def AssocEnv.cores (env : AssocEnv) : List Impl := env.impls.map AssocImpl.impl

/-- Only variables occurring in the head may occur in explicit bodies. -/
def AssocHeadVars (i : AssocImpl) : Prop :=
  ∀ name rhs, (name, rhs) ∈ i.assoc → ∀ v,
    0 < rhs.occurrences v → 0 < argsOccurrences v i.impl.head

/-- Correct signature arity, and every declared name is supplied or defaulted. -/
def AssocComplete (roles : RoleDecls) (i : AssocImpl) : Prop :=
  i.impl.head.length = (roles i.impl.role).arity ∧
  ∀ name d, (roles i.impl.role).assoc name = some d →
    (∃ rhs, i.assoc.lookup name = some rhs) ∨ ∃ rhs, d = some rhs

/-- No body defines a name absent from the role declaration. -/
def AssocDeclared (roles : RoleDecls) (i : AssocImpl) : Prop :=
  ∀ name rhs, (name, rhs) ∈ i.assoc → ∃ d, (roles i.impl.role).assoc name = some d

def AssocWellFormed (env : AssocEnv) (roles : RoleDecls) : Prop :=
  ∀ i ∈ env.impls, AssocHeadVars i ∧ AssocComplete roles i ∧ AssocDeclared roles i

/-- Positional substitution for default bodies; out-of-range placeholders cannot
be observed by a scoped default at a goal of the declared arity. -/
def defaultSubst (args : List Term) : Subst :=
  fun v => (args[v]?).getD (.var v)

/-- Explicit bodies take precedence over defaults. No constraints are inspected. -/
def assocValue (i : AssocImpl) (role : RoleDecl) (g : Goal) (name : Nat) : Option Term :=
  match i.assoc.lookup name with
  | some rhs => some (rhs.subst (matchingSubst i.impl.head g.args))
  | none => ((role.assoc name).join).map (Term.subst (defaultSubst g.args))

/-- Reuse terminating role resolution, then instantiate the unique selected
impl's annotation. In a well-formed environment, undeclared names give `none`;
unresolved goals always give `none`. -/
def assocOf (env : AssocEnv) (roles : RoleDecls) (wf : WellFormed env.cores)
    (g : Goal) (name : Nat) : Option Term :=
  if resolve env.cores wf g = .resolved then
    match candidates env.cores g with
    | [i] => match env.impls.find? (fun j => j.impl == i) with
      | some j => assocValue j (roles g.role) g name
      | none => none
    | _ => none
  else none

/- Absence of a variable is preserved by a substitution whose relevant images
omit that variable. -/
mutual
  theorem Term.subst_absent (t : Term) (σ : Subst) (w : Nat)
      (h : ∀ v, 0 < t.occurrences v → (σ v).occurrences w = 0) :
      (t.subst σ).occurrences w = 0 := by
    cases t with
    | var v => exact h v (by simp [Term.occurrences])
    | app k ts => exact args_subst_absent ts σ w h
  theorem args_subst_absent (ts : List Term) (σ : Subst) (w : Nat)
      (h : ∀ v, 0 < argsOccurrences v ts → (σ v).occurrences w = 0) :
      argsOccurrences w (substArgs σ ts) = 0 := by
    cases ts with
    | nil => rfl
    | cons t ts =>
      simp only [substArgs, argsOccurrences]
      rw [t.subst_absent σ w (fun v hv => h v (by simp only [argsOccurrences]; omega)),
        args_subst_absent ts σ w (fun v hv => h v (by simp only [argsOccurrences]; omega))]
end

/- Each relevant substitution image is a subterm of the instantiated head. -/
mutual
  theorem Term.image_absent (t : Term) (σ : Subst) (v w : Nat)
      (hv : 0 < t.occurrences v) (hw : (t.subst σ).occurrences w = 0) :
      (σ v).occurrences w = 0 := by
    cases t with
    | var u =>
      have : v = u := by
        by_cases he : v = u
        · exact he
        · simp [Term.occurrences, he] at hv
      subst u
      exact hw
    | app k ts => exact args_image_absent ts σ v w hv hw
  theorem args_image_absent (ts : List Term) (σ : Subst) (v w : Nat)
      (hv : 0 < argsOccurrences v ts) (hw : argsOccurrences w (substArgs σ ts) = 0) :
      (σ v).occurrences w = 0 := by
    cases ts with
    | nil => simp [argsOccurrences] at hv
    | cons t ts =>
      simp only [substArgs, argsOccurrences, Nat.add_eq_zero_iff] at hw
      by_cases ht : 0 < t.occurrences v
      · exact t.image_absent σ v w ht hw.1
      · exact args_image_absent ts σ v w (by simp only [argsOccurrences] at hv; omega) hw.2
end

/-- Hygiene for any body scope by a matching head; goal variables stay rigid. -/
theorem assoc_rhs_closed {i : AssocImpl} (scope : AssocHeadVars i)
    {name : Nat} {rhs : Term} (body : (name, rhs) ∈ i.assoc)
    {g : Goal} (hm : Matches i.impl g) (w : Nat)
    (absent : argsOccurrences w g.args = 0) :
    (rhs.subst (matchingSubst i.impl.head g.args)).occurrences w = 0 := by
  apply rhs.subst_absent
  intro v hv
  apply args_image_absent i.impl.head _ v w (scope name rhs body v hv)
  rw [matched_head hm]
  exact absent

/-- A valid explicit body observes the matching substitution only on head vars. -/
theorem assoc_rhs_matching {i : AssocImpl} (scope : AssocHeadVars i)
    {name : Nat} {rhs : Term} (body : (name, rhs) ∈ i.assoc)
    (σ : Subst) {g : Goal} (head : substArgs σ i.impl.head = g.args) :
    rhs.subst (matchingSubst i.impl.head g.args) = rhs.subst σ := by
  rw [← head]
  exact rhs.subst_congr _ σ (fun v hv => matchingSubst_agrees _ σ v (scope name rhs body v hv))

theorem substArgs_length (σ : Subst) (ts : List Term) :
    (substArgs σ ts).length = ts.length := by
  induction ts <;> simp_all [substArgs]

theorem args_absent_member {ts : List Term} {t : Term} (ht : t ∈ ts) (w : Nat)
    (h : argsOccurrences w ts = 0) : t.occurrences w = 0 := by
  induction ts with
  | nil => simp at ht
  | cons u us ih =>
    simp only [argsOccurrences, Nat.add_eq_zero_iff] at h
    rcases List.mem_cons.mp ht with rfl | ht
    · exact h.1
    · exact ih ht h.2

mutual
  theorem Term.occurrences_above_bound (t : Term) (v : Nat) (h : t.bound ≤ v) :
      t.occurrences v = 0 := by
    cases t with
    | var u => simp only [Term.bound] at h; simp [Term.occurrences, show v ≠ u by omega]
    | app k ts => exact args_occurrences_above_bound ts v h
  theorem args_occurrences_above_bound (ts : List Term) (v : Nat) (h : argsBound ts ≤ v) :
      argsOccurrences v ts = 0 := by
    cases ts with
    | nil => rfl
    | cons t ts =>
      simp only [argsBound, Nat.max_le] at h
      simp [argsOccurrences, t.occurrences_above_bound v h.1,
        args_occurrences_above_bound ts v h.2]
end

theorem default_rhs_closed (rhs : Term) (args : List Term) (scope : rhs.bound ≤ args.length)
    (w : Nat) (absent : argsOccurrences w args = 0) :
    (rhs.subst (defaultSubst args)).occurrences w = 0 := by
  apply rhs.subst_absent
  intro v hv
  have lt : v < args.length := by
    by_cases hb : rhs.bound ≤ v
    · rw [rhs.occurrences_above_bound v hb] at hv; omega
    · omega
  cases he : args[v]? with
  | none => have := List.getElem?_eq_none_iff.mp he; omega
  | some t =>
    simpa [defaultSubst, he] using args_absent_member (List.mem_of_getElem? he) w absent

theorem assoc_lookup_mem {i : AssocImpl} {name : Nat} {rhs : Term}
    (h : i.assoc.lookup name = some rhs) : (name, rhs) ∈ i.assoc := by
  obtain ⟨l, r, he, _⟩ := List.lookup_eq_some_iff.mp h
  simp [he]

/-- The annotation selected by a core impl is independent of list search order. -/
theorem assoc_find {env : AssocEnv} {i : AssocImpl} (hi : i ∈ env.impls) :
    ∃ j, env.impls.find? (fun j => j.impl == i.impl) = some j ∧
      j.impl = i.impl ∧ j.assoc = i.assoc := by
  have hs : (env.impls.find? (fun j => j.impl == i.impl)).isSome = true :=
    List.find?_isSome.mpr ⟨i, hi, by simp⟩
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hs
  have core : j.impl = i.impl := by simpa using List.find?_some hj
  have member : j ∈ env.impls := List.mem_of_find?_eq_some hj
  exact ⟨j, hj, core, env.coherent j member i hi core⟩

/-- Once resolution succeeds, where derivations do not occur in the value.
The only remaining inputs are the selected impl, head match, and signature. -/
theorem assoc_independent_of_constraints (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (g : Goal) (name : Nat)
    (resolved : resolve env.cores wf g = .resolved)
    (i : AssocImpl) (member : i ∈ env.impls)
    (selected : candidates env.cores g = [i.impl]) :
    assocOf env roles wf g name = assocValue i (roles g.role) g name := by
  obtain ⟨j, hj, hc, ha⟩ := assoc_find member
  simp only [assocOf, resolved, ↓reduceIte, selected, hj]
  simp only [assocValue, hc, ha]

/-- Arbitrary matching substitutions give the same explicit associated value. -/
theorem assoc_explicit_eq (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (g : Goal) (name : Nat) (resolved : resolve env.cores wf g = .resolved)
    (i : AssocImpl) (member : i ∈ env.impls)
    (selected : candidates env.cores g = [i.impl])
    (σ : Subst) (head : substArgs σ i.impl.head = g.args)
    (rhs : Term) (body : i.assoc.lookup name = some rhs) :
    assocOf env roles wf g name = some (rhs.subst σ) := by
  rw [assoc_independent_of_constraints env roles wf g name resolved i member selected]
  simp only [assocValue, body]
  rw [assoc_rhs_matching (awf i member).1 (assoc_lookup_mem body) σ head]

/-- A successful resolver selects an annotated impl, without another search tree. -/
theorem assoc_selected_of_resolved (env : AssocEnv) (wf : WellFormed env.cores)
    (g : Goal) (resolved : resolve env.cores wf g = .resolved) :
    ∃ i ∈ env.impls, candidates env.cores g = [i.impl] ∧ Matches i.impl g := by
  obtain ⟨core, hs, _⟩ := (resolve_resolved_iff env.cores wf g).mp resolved
  have hm := mem_candidates.mp (hs ▸ List.mem_singleton_self core)
  obtain ⟨i, hi, he⟩ := List.mem_map.mp hm.1
  exact ⟨i, hi, he ▸ hs, he ▸ hm.2⟩

/-- Instantiation is total for declared names of a well-formed matching impl. -/
theorem assocValue_total_closed (roles : RoleDecls) (i : AssocImpl)
    (wf : AssocHeadVars i ∧ AssocComplete roles i ∧ AssocDeclared roles i)
    (g : Goal) (hm : Matches i.impl g) (name : Nat)
    (declared : ∃ d, (roles g.role).assoc name = some d) :
    ∃ value, assocValue i (roles g.role) g name = some value ∧
      ∀ w, argsOccurrences w g.args = 0 → value.occurrences w = 0 := by
  cases body : i.assoc.lookup name with
  | some rhs =>
    refine ⟨rhs.subst (matchingSubst i.impl.head g.args), ?_, ?_⟩
    · simp [assocValue, body]
    · exact assoc_rhs_closed wf.1 (assoc_lookup_mem body) hm
  | none =>
    obtain ⟨d, hd⟩ := declared
    have hd' : (roles i.impl.role).assoc name = some d := hm.1.symm ▸ hd
    have coverage := wf.2.1.2 name d hd'
    obtain ⟨rhs, hrhs⟩ : ∃ rhs, d = some rhs := by
      rcases coverage with ⟨rhs, h⟩ | h
      · simp [body] at h
      · exact h
    subst d
    have arity : g.args.length = (roles g.role).arity := by
      rw [← matched_head hm, substArgs_length, wf.2.1.1, hm.1]
    refine ⟨rhs.subst (defaultSubst g.args), ?_, ?_⟩
    · simp [assocValue, body, hd]
    · apply default_rhs_closed
      rw [arity]
      exact (roles g.role).defaultsScoped name rhs hd

/-- For every declared name, resolution success and the two well-formedness
conditions imply a value containing only variables occurring in the goal. -/
theorem assoc_total_closed (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (g : Goal) (name : Nat) (resolved : resolve env.cores wf g = .resolved)
    (declared : ∃ d, (roles g.role).assoc name = some d) :
    ∃ value, assocOf env roles wf g name = some value ∧
      ∀ v, 0 < value.occurrences v → 0 < argsOccurrences v g.args := by
  obtain ⟨i, hi, hs, hm⟩ := assoc_selected_of_resolved env wf g resolved
  obtain ⟨value, hv, closed⟩ := assocValue_total_closed roles i (awf i hi) g hm name declared
  refine ⟨value, ?_, ?_⟩
  · rw [assoc_independent_of_constraints env roles wf g name resolved i hi hs]
    exact hv
  · intro v hv
    have := closed v
    omega

/-- A successful goal has exactly one value for each declared associated name. -/
theorem assoc_unique (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (g : Goal) (name : Nat) (resolved : resolve env.cores wf g = .resolved)
    (declared : ∃ d, (roles g.role).assoc name = some d) :
    ∃ value, assocOf env roles wf g name = some value ∧
      ∀ other, assocOf env roles wf g name = some other → other = value := by
  obtain ⟨value, hv, _⟩ := assoc_total_closed env roles wf awf g name resolved declared
  exact ⟨value, hv, fun other ho => Option.some.inj (ho.symm.trans hv)⟩

/-- Independent associated-type derivations, using the existing declarative
where judgment. Neither constructor inspects `resolve` or `assocOf`. -/
inductive AssocDerives (env : AssocEnv) (roles : RoleDecls) : Goal → Nat → Term → Prop where
  | explicit {g : Goal} {name : Nat} (i : AssocImpl) (σ : Subst)
      (member : i ∈ env.impls) (role : i.impl.role = g.role)
      (head : substArgs σ i.impl.head = g.args)
      (children : ∀ c ∈ i.impl.constraints, Derives env.cores (c.subst σ))
      (rhs : Term) (body : i.assoc.lookup name = some rhs) :
      AssocDerives env roles g name (rhs.subst σ)
  | default {g : Goal} {name : Nat} (i : AssocImpl) (σ : Subst)
      (member : i ∈ env.impls) (role : i.impl.role = g.role)
      (head : substArgs σ i.impl.head = g.args)
      (children : ∀ c ∈ i.impl.constraints, Derives env.cores (c.subst σ))
      (rhs : Term) (omitted : i.assoc.lookup name = none)
      (body : (roles g.role).assoc name = some (some rhs)) :
      AssocDerives env roles g name (rhs.subst (defaultSubst g.args))

/-- Any declarative derivation agrees with the computed value when role
resolution succeeds. In particular, arbitrary where proofs and matching
substitutions cannot change the value. -/
theorem assoc_derivation_agrees (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (g : Goal) (name : Nat) (resolved : resolve env.cores wf g = .resolved)
    {value : Term} (derivation : AssocDerives env roles g name value) :
    assocOf env roles wf g name = some value := by
  have selected (i : AssocImpl) (member : i ∈ env.impls) (hm : Matches i.impl g) :
      candidates env.cores g = [i.impl] := by
    obtain ⟨j, hs, _⟩ := (resolve_resolved_iff env.cores wf g).mp resolved
    have hc : i.impl ∈ candidates env.cores g := mem_candidates.mpr
      ⟨List.mem_map.mpr ⟨i, member, rfl⟩, hm⟩
    have he : i.impl = j := by simpa [hs] using hc
    simpa [he] using hs
  cases derivation with
  | explicit i σ member role head _ rhs body =>
    exact assoc_explicit_eq env roles wf awf g name resolved i member
      (selected i member ⟨role, σ, head⟩) σ head rhs body
  | default i σ member role head _ rhs omitted body =>
    rw [assoc_independent_of_constraints env roles wf g name resolved i member
      (selected i member ⟨role, σ, head⟩)]
    simp [assocValue, omitted, body]

/-- Uniqueness across two independent derivations, not merely proof irrelevance
of two equalities about a deterministic function. -/
theorem assoc_derivations_unique (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (g : Goal) (name : Nat) (resolved : resolve env.cores wf g = .resolved)
    {a b : Term} (ha : AssocDerives env roles g name a)
    (hb : AssocDerives env roles g name b) : a = b := by
  exact Option.some.inj ((assoc_derivation_agrees env roles wf awf g name resolved ha).symm.trans
    (assoc_derivation_agrees env roles wf awf g name resolved hb))

/-- Exact size formula for explicit bodies; no new recursive size rule is needed. -/
theorem assoc_explicit_size (env : AssocEnv) (roles : RoleDecls)
    (wf : WellFormed env.cores) (awf : AssocWellFormed env roles)
    (g : Goal) (name : Nat) (resolved : resolve env.cores wf g = .resolved)
    (i : AssocImpl) (member : i ∈ env.impls)
    (selected : candidates env.cores g = [i.impl])
    (σ : Subst) (head : substArgs σ i.impl.head = g.args)
    (rhs : Term) (body : i.assoc.lookup name = some rhs)
    (value : Term) (result : assocOf env roles wf g name = some value) :
    value.size = rhs.size + sumBelow rhs.bound
      (fun v => rhs.occurrences v * ((σ v).size - 1)) := by
  have he := assoc_explicit_eq env roles wf awf g name resolved i member selected σ head rhs body
  have hv : value = rhs.subst σ := Option.some.inj (result.symm.trans he)
  rw [hv]
  exact rhs.subst_size σ rhs.bound (Nat.le_refl _)

namespace AssocExamples

open Examples (int str)

def char : Term := .app 3 []
def box (t : Term) : Term := .app 4 [t]
def index (container key : Term) : Goal := ⟨2, [container, key]⟩

def requiredDecl : RoleDecl where
  arity := 2
  assoc := fun name => if name = 0 then some none else none
  defaultsScoped := by intro name rhs h; split at h <;> simp_all

def defaultDecl : RoleDecl where
  arity := 2
  assoc := fun name => if name = 0 then some (some char) else none
  defaultsScoped := by
    intro name rhs h
    split at h
    · simp only [Option.some.injEq] at h
      cases h
      decide
    · contradiction

/-- The first role parameter, rather than an impl-local variable. -/
def parameterDefaultDecl : RoleDecl where
  arity := 2
  assoc := fun name => if name = 0 then some (some (.var 0)) else none
  defaultsScoped := by
    intro name rhs h
    split at h
    · simp only [Option.some.injEq] at h
      cases h
      decide
    · contradiction

def parameterDefaultRoles : RoleDecls := fun _ => parameterDefaultDecl

def requiredRoles : RoleDecls := fun _ => requiredDecl
def defaultRoles : RoleDecls := fun _ => defaultDecl

/-- A single declaration automatically satisfies annotation coherence. -/
def singletonEnv (i : AssocImpl) : AssocEnv where
  impls := [i]
  coherent := by
    intro j hj k hk _
    simp only [List.mem_singleton] at hj hk
    subst j; subst k; rfl

def strImpl : AssocImpl := ⟨⟨2, [str, int], [], 10⟩, [(0, char)], by decide⟩
def boxImpl : AssocImpl := ⟨⟨2, [box (.var 0), int], [], 11⟩, [(0, .var 0)], by decide⟩
def omittedImpl : AssocImpl := ⟨⟨2, [str, int], [], 12⟩, [], by decide⟩

theorem str_paterson : WellFormed (singletonEnv strImpl).cores := by
  simp [WellFormed, AssocEnv.cores, singletonEnv, strImpl, Impl.WellFormed]

theorem box_paterson : WellFormed (singletonEnv boxImpl).cores := by
  simp [WellFormed, AssocEnv.cores, singletonEnv, boxImpl, Impl.WellFormed]

theorem omitted_paterson : WellFormed (singletonEnv omittedImpl).cores := by
  simp [WellFormed, AssocEnv.cores, singletonEnv, omittedImpl, Impl.WellFormed]

theorem str_assoc_wellFormed : AssocWellFormed (singletonEnv strImpl) requiredRoles := by
  intro i hi
  have he : i = strImpl := by simpa [singletonEnv] using hi
  subst i
  simp [AssocHeadVars, AssocComplete, AssocDeclared, strImpl, requiredRoles, requiredDecl,
    char, Term.occurrences, argsOccurrences]

theorem box_assoc_wellFormed : AssocWellFormed (singletonEnv boxImpl) requiredRoles := by
  intro i hi
  have he : i = boxImpl := by simpa [singletonEnv] using hi
  subst i
  simp [AssocHeadVars, AssocComplete, AssocDeclared, boxImpl, requiredRoles, requiredDecl,
    box, int, Term.occurrences, argsOccurrences]

theorem omitted_assoc_wellFormed : AssocWellFormed (singletonEnv omittedImpl) defaultRoles := by
  intro i hi
  have he : i = omittedImpl := by simpa [singletonEnv] using hi
  subst i
  simp [AssocHeadVars, AssocComplete, AssocDeclared, omittedImpl, defaultRoles, defaultDecl]

theorem str_resolved : resolve (singletonEnv strImpl).cores str_paterson (index str int) = .resolved := by
  rw [resolve_one _ _ _ strImpl.impl (by decide)]
  rfl

theorem box_resolved : resolve (singletonEnv boxImpl).cores box_paterson (index (box str) int) = .resolved := by
  rw [resolve_one _ _ _ boxImpl.impl (by decide)]
  rfl

theorem omitted_resolved : resolve (singletonEnv omittedImpl).cores omitted_paterson (index str int) = .resolved := by
  rw [resolve_one _ _ _ omittedImpl.impl (by decide)]
  rfl

/-- `impl Index str int: type value = char`. -/
theorem str_value :
    assocOf (singletonEnv strImpl) requiredRoles str_paterson (index str int) 0 = some char := by
  rw [assoc_independent_of_constraints _ _ _ _ _ str_resolved strImpl (by simp [singletonEnv]) (by decide)]
  rfl

/-- `impl Index (box 'a) int: type value = 'a`, instantiated at `box str`. -/
theorem box_value :
    assocOf (singletonEnv boxImpl) requiredRoles box_paterson (index (box str) int) 0 = some str := by
  rw [assoc_independent_of_constraints _ _ _ _ _ box_resolved boxImpl (by simp [singletonEnv]) (by decide)]
  rfl

/-- A default `type value = char` supplies an omitted implementation body. -/
theorem default_value :
    assocOf (singletonEnv omittedImpl) defaultRoles omitted_paterson (index str int) 0 = some char := by
  rw [assoc_independent_of_constraints _ _ _ _ _ omitted_resolved omittedImpl (by simp [singletonEnv]) (by decide)]
  rfl

/-- Impl variable 0 maps to rigid goal variable 17; its image is not substituted
again. Goal variable ids do not acquire impl-variable meaning. -/
theorem rigid_goal_value :
    assocOf (singletonEnv boxImpl) requiredRoles box_paterson (index (box (.var 17)) int) 0 = some (.var 17) := by
  have resolved : resolve (singletonEnv boxImpl).cores box_paterson
      (index (box (.var 17)) int) = .resolved := by
    rw [resolve_one _ _ _ boxImpl.impl (by decide)]
    rfl
  rw [assoc_independent_of_constraints _ _ _ _ _ resolved boxImpl (by simp [singletonEnv]) (by decide)]
  rfl

/-- A positional default uses the goal argument even when the impl head
contains no variable at all. -/
theorem parameter_default_value :
    assocOf (singletonEnv omittedImpl) parameterDefaultRoles omitted_paterson
      (index str int) 0 = some str := by
  rw [assoc_independent_of_constraints _ _ _ _ _ omitted_resolved omittedImpl
    (by simp [singletonEnv]) (by decide)]
  rfl

/-- An explicit body overrides a positional default. -/
theorem explicit_overrides_default :
    assocOf (singletonEnv strImpl) parameterDefaultRoles str_paterson
      (index str int) 0 = some char := by
  rw [assoc_independent_of_constraints _ _ _ _ _ str_resolved strImpl
    (by simp [singletonEnv]) (by decide)]
  rfl

def escapingImpl : AssocImpl := ⟨boxImpl.impl, [(0, .var 1)], by decide⟩
def undeclaredImpl : AssocImpl := ⟨strImpl.impl, [(0, char), (1, char)], by decide⟩

theorem escaping_not_assocWellFormed :
    ¬ AssocWellFormed (singletonEnv escapingImpl) requiredRoles := by
  intro wf
  have h := (wf escapingImpl (by simp [singletonEnv])).1 0 (.var 1)
    (by simp [escapingImpl]) 1 (by simp [Term.occurrences])
  simp [escapingImpl, boxImpl, box, int, Term.occurrences, argsOccurrences] at h

theorem missing_not_assocWellFormed :
    ¬ AssocWellFormed (singletonEnv omittedImpl) requiredRoles := by
  intro wf
  have h := (wf omittedImpl (by simp [singletonEnv])).2.1.2 0 none (by rfl)
  simp [omittedImpl] at h

theorem undeclared_not_assocWellFormed :
    ¬ AssocWellFormed (singletonEnv undeclaredImpl) requiredRoles := by
  intro wf
  have h := (wf undeclaredImpl (by simp [singletonEnv])).2.2 1 char (by simp [undeclaredImpl])
  simp [requiredRoles, requiredDecl] at h

end AssocExamples
end Yulang.Roles
