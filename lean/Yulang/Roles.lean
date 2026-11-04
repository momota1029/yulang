import Std

/-!
# First-order role resolution

Spec §6.2–6.3: head overlap is ambiguous, before checking `where`.
Goal variables are rigid. Only impl variables are substituted, once (images
are not recursively substituted). Every recursive call strictly decreases the
sum of argument sizes; no fuel or depth limit is used.

Associated types, method dispatch, receiver deferral, operation-local role
constraints, effects and the inference constraint language are outside this core.
-/
namespace Yulang.Roles

inductive Term where
  | var : Nat → Term
  | app : Nat → List Term → Term
  deriving Repr

mutual
  def Term.decEq (a b : Term) : Decidable (a = b) := by
    cases a with
    | var v =>
      cases b with
      | var w => exact decidable_of_iff (v = w) (by simp)
      | app _ _ => exact isFalse (by intro h; cases h)
    | app k ts =>
      cases b with
      | var _ => exact isFalse (by intro h; cases h)
      | app l us =>
        have := argsDecEq ts us
        exact decidable_of_iff (k = l ∧ ts = us) (by simp)
  def argsDecEq (ts us : List Term) : Decidable (ts = us) := by
    cases ts with
    | nil => cases us <;> exact inferInstance
    | cons t ts =>
      cases us with
      | nil => exact isFalse (by intro h; cases h)
      | cons u us =>
        have := Term.decEq t u
        have := argsDecEq ts us
        exact decidable_of_iff (t = u ∧ ts = us) (by simp)
end

instance : DecidableEq Term := Term.decEq

abbrev Subst := Nat → Term

mutual
  def Term.size : Term → Nat
    | .var _ => 1
    | .app _ ts => 1 + argsSize ts
  def argsSize : List Term → Nat
    | [] => 0
    | t :: ts => t.size + argsSize ts
end

mutual
  def Term.occurrences (v : Nat) : Term → Nat
    | .var w => if v = w then 1 else 0
    | .app _ ts => argsOccurrences v ts
  def argsOccurrences (v : Nat) : List Term → Nat
    | [] => 0
    | t :: ts => t.occurrences v + argsOccurrences v ts
end

mutual
  def Term.subst (σ : Subst) : Term → Term
    | .var v => σ v
    | .app k ts => .app k (substArgs σ ts)
  def substArgs (σ : Subst) : List Term → List Term
    | [] => []
    | t :: ts => t.subst σ :: substArgs σ ts
end

mutual
  def Term.bound : Term → Nat
    | .var v => v + 1
    | .app _ ts => argsBound ts
  def argsBound : List Term → Nat
    | [] => 0
    | t :: ts => max t.bound (argsBound ts)
end

-- A finite sum indexed by all variables below n (no finite-support library).
def sumBelow (n : Nat) (f : Nat → Nat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => sumBelow n f + f n

theorem sumBelow_add (n : Nat) (f g : Nat → Nat) :
    sumBelow n (fun v => f v + g v) = sumBelow n f + sumBelow n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sumBelow, ih]; omega

theorem sumBelow_mono (n : Nat) {f g : Nat → Nat} (h : ∀ v, f v ≤ g v) :
    sumBelow n f ≤ sumBelow n g := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih => exact Nat.add_le_add ih (h n)

theorem sumBelow_single (n v : Nat) (f : Nat → Nat) (h : v < n) :
    sumBelow n (fun u => (if u = v then 1 else 0) * f u) = f v := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases e : n = v
    · subst v
      have hz : sumBelow n (fun u => (if u = n then 1 else 0) * f u) = 0 := by
        have aux : ∀ m, m ≤ n → sumBelow m (fun u => (if u = n then 1 else 0) * f u) = 0 := by
          intro m hm
          induction m with
          | zero => rfl
          | succ m ih => simp [sumBelow, ih (by omega), show m ≠ n by omega]
        exact aux n (by omega)
      simp [sumBelow, hz]
    · simp [sumBelow, e, ih (by omega)]

theorem Term.size_pos (t : Term) : 0 < t.size := by
  cases t <;> simp [Term.size] <;> omega

mutual
  theorem Term.subst_size (t : Term) (σ : Subst) (n : Nat) (h : t.bound ≤ n) :
      (t.subst σ).size = t.size +
        sumBelow n (fun v => t.occurrences v * ((σ v).size - 1)) := by
    cases t with
    | var v =>
      simp only [Term.bound] at h
      simp only [Term.subst, Term.size, Term.occurrences]
      rw [sumBelow_single n v _ (by omega)]
      have := (σ v).size_pos
      omega
    | app k ts =>
      simp only [Term.subst, Term.size, Term.occurrences]
      rw [args_subst_size ts σ n h]
      omega
  theorem args_subst_size (ts : List Term) (σ : Subst) (n : Nat) (h : argsBound ts ≤ n) :
      argsSize (substArgs σ ts) = argsSize ts +
        sumBelow n (fun v => argsOccurrences v ts * ((σ v).size - 1)) := by
    cases ts with
    | nil =>
      have hz : ∀ n, sumBelow n (fun _ => 0) = 0 := by
        intro n; induction n <;> simp_all [sumBelow]
      simp [substArgs, argsSize, argsOccurrences, hz]
    | cons t ts =>
      simp only [argsBound, Nat.max_le] at h
      simp only [substArgs, argsSize, argsOccurrences, Nat.add_mul]
      rw [sumBelow_add, Term.subst_size t σ n h.1, args_subst_size ts σ n h.2]
      omega
end

structure Goal where
  role : Nat
  args : List Term
  deriving DecidableEq, Repr

def Goal.subst (σ : Subst) (g : Goal) : Goal := ⟨g.role, substArgs σ g.args⟩

structure Impl where
  role : Nat
  head : List Term
  constraints : List Goal
  /-- Declaration identity: identical heads/constraints may belong to distinct impls. -/
  key : Nat
  deriving DecidableEq, Repr

def Impl.WellFormed (i : Impl) : Prop :=
  ∀ c ∈ i.constraints, argsSize c.args < argsSize i.head ∧
    ∀ v, argsOccurrences v c.args ≤ argsOccurrences v i.head

theorem constraint_variables_in_head {i : Impl} (wf : i.WellFormed)
    {c : Goal} (hc : c ∈ i.constraints) (v : Nat)
    (absent : argsOccurrences v i.head = 0) : argsOccurrences v c.args = 0 := by
  have := (wf c hc).2 v
  omega

theorem size_decreases {i : Impl} (wf : i.WellFormed)
    {c : Goal} (hc : c ∈ i.constraints) (σ : Subst) :
    argsSize (substArgs σ c.args) < argsSize (substArgs σ i.head) := by
  let n := max (argsBound c.args) (argsBound i.head)
  rw [args_subst_size c.args σ n (Nat.le_max_left ..),
      args_subst_size i.head σ n (Nat.le_max_right ..)]
  have hs := (wf c hc).1
  have hw := sumBelow_mono n (fun v =>
    Nat.mul_le_mul_right ((σ v).size - 1) ((wf c hc).2 v))
  omega

/-- Independent existential derivability; it does not inspect the resolver. -/
inductive Derives (impls : List Impl) : Goal → Prop where
  | impl {g : Goal} (i : Impl) (σ : Subst)
      (member : i ∈ impls) (role : i.role = g.role)
      (head : substArgs σ i.head = g.args)
      (children : ∀ c ∈ i.constraints, Derives impls (c.subst σ)) : Derives impls g

/- Extract the first image of v by walking the two trees in parallel.
Mismatches are subsequently rejected by the full head equality check. -/
mutual
  def Term.extract (v : Nat) : Term → Term → Option Term
    | .var w, t => if v = w then some t else none
    | .app _ ps, .app _ ts => extractArgs v ps ts
    | .app _ _, .var _ => none
  def extractArgs (v : Nat) : List Term → List Term → Option Term
    | p :: ps, t :: ts => (p.extract v t).orElse (fun _ => extractArgs v ps ts)
    | _, _ => none
end

mutual
  theorem Term.extract_subst (t : Term) (σ : Subst) (v : Nat) :
      t.extract v (t.subst σ) =
        if 0 < t.occurrences v then some (σ v) else none := by
    cases t with
    | var w => by_cases h : v = w <;> simp [Term.extract, Term.subst, Term.occurrences, h]
    | app k ts => exact extractArgs_subst ts σ v
  theorem extractArgs_subst (ts : List Term) (σ : Subst) (v : Nat) :
      extractArgs v ts (substArgs σ ts) =
        if 0 < argsOccurrences v ts then some (σ v) else none := by
    cases ts with
    | nil => simp [extractArgs, argsOccurrences]
    | cons t ts =>
      simp only [extractArgs, substArgs, Term.extract_subst, extractArgs_subst, argsOccurrences]
      by_cases ht : 0 < t.occurrences v
      · simp [ht, show 0 < t.occurrences v + argsOccurrences v ts by omega]
      · simp [show t.occurrences v = 0 by omega]
end

mutual
  theorem Term.subst_congr (t : Term) (σ τ : Subst)
      (h : ∀ v, 0 < t.occurrences v → σ v = τ v) : t.subst σ = t.subst τ := by
    cases t with
    | var v => exact h v (by simp [Term.occurrences])
    | app k ts => exact congrArg (Term.app k) (substArgs_congr ts σ τ h)
  theorem substArgs_congr (ts : List Term) (σ τ : Subst)
      (h : ∀ v, 0 < argsOccurrences v ts → σ v = τ v) :
      substArgs σ ts = substArgs τ ts := by
    cases ts with
    | nil => rfl
    | cons t ts =>
      simp only [substArgs]
      congr 1
      · exact t.subst_congr σ τ (fun v hv => h v (by simp only [argsOccurrences]; omega))
      · exact substArgs_congr ts σ τ (fun v hv => h v (by simp only [argsOccurrences]; omega))
end

/-- A canonical, executable one-way matcher. Unmentioned variables default to
 themselves; well-formed constraints cannot observe those defaults. -/
def matchingSubst (ps ts : List Term) : Subst :=
  fun v => (extractArgs v ps ts).getD (.var v)

theorem matchingSubst_agrees (ps : List Term) (σ : Subst) (v : Nat)
    (h : 0 < argsOccurrences v ps) : matchingSubst ps (substArgs σ ps) v = σ v := by
  simp [matchingSubst, extractArgs_subst, h]

theorem matchingSubst_head (ps : List Term) (σ : Subst) :
    substArgs (matchingSubst ps (substArgs σ ps)) ps = substArgs σ ps :=
  substArgs_congr ps _ σ (matchingSubst_agrees ps σ)

def Matches (i : Impl) (g : Goal) : Prop :=
  i.role = g.role ∧ ∃ σ : Subst, substArgs σ i.head = g.args

def headMatches (i : Impl) (g : Goal) : Bool :=
  decide (i.role = g.role ∧ substArgs (matchingSubst i.head g.args) i.head = g.args)

@[simp] theorem matches_iff (i : Impl) (g : Goal) : headMatches i g = true ↔ Matches i g := by
  simp only [headMatches, decide_eq_true_eq, Matches]
  constructor
  · rintro ⟨hr, hh⟩; exact ⟨hr, _, hh⟩
  · rintro ⟨hr, σ, hh⟩
    exact ⟨hr, hh ▸ matchingSubst_head i.head σ⟩

theorem matched_head {i : Impl} {g : Goal} (h : Matches i g) :
    substArgs (matchingSubst i.head g.args) i.head = g.args := by
  exact (of_decide_eq_true ((matches_iff i g).mpr h)).2

theorem matched_constraint {i : Impl} (wf : i.WellFormed) {g : Goal}
    (σ : Subst) (hh : substArgs σ i.head = g.args)
    {c : Goal} (hc : c ∈ i.constraints) :
    c.subst (matchingSubst i.head g.args) = c.subst σ := by
  apply congrArg (Goal.mk c.role)
  rw [← hh]
  apply substArgs_congr
  intro v hv
  apply matchingSubst_agrees
  have := (wf c hc).2 v
  omega

def distinct [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => if x ∈ xs then distinct xs else x :: distinct xs

@[simp] theorem mem_distinct [DecidableEq α] (x : α) (xs : List α) :
    x ∈ distinct xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [distinct]
  | cons y ys ih =>
    by_cases hy : y ∈ ys
    · by_cases he : x = y <;> simp_all [distinct]
    · simp [distinct, hy, ih]

theorem distinct_nodup [DecidableEq α] (xs : List α) : (distinct xs).Nodup := by
  induction xs with
  | nil => simp [distinct]
  | cons x xs ih =>
    by_cases h : x ∈ xs <;> simp [distinct, h, List.nodup_cons, ih]

/-- Duplicate values denote the same declaration; distinct impl values are candidates.
The list order never breaks ties. -/
def candidates (impls : List Impl) (g : Goal) : List Impl :=
  (distinct impls).filter (fun i => headMatches i g)

@[simp] theorem mem_candidates {impls : List Impl} {g : Goal} {i : Impl} :
    i ∈ candidates impls g ↔ i ∈ impls ∧ Matches i g := by
  simp [candidates]

theorem candidates_nodup (impls : List Impl) (g : Goal) :
    (candidates impls g).Nodup := by
  exact List.Pairwise.filter _ (distinct_nodup _)

/-- Well-formedness is checked independently for each declaration. -/
def WellFormed (impls : List Impl) : Prop := ∀ i ∈ impls, i.WellFormed

theorem wellFormed_cons (i : Impl) (impls : List Impl) :
    WellFormed (i :: impls) ↔ i.WellFormed ∧ WellFormed impls := by
  simp [WellFormed]

inductive Result where
  | resolved | noImpl | ambiguous
  deriving DecidableEq, Repr

/-- Inspect all siblings: ambiguity dominates noImpl. Thus an overlap anywhere
in the uniquely selected dependency tree is reported even if a sibling fails. -/
def combine (rs : List Result) : Result :=
  if .ambiguous ∈ rs then .ambiguous
  else if .noImpl ∈ rs then .noImpl else .resolved

/-- Total by the Paterson measure, independently of derivability. -/
def resolve (impls : List Impl) (wf : WellFormed impls) (g : Goal) : Result :=
  match h : candidates impls g with
  | [] => .noImpl
  | [i] =>
    have _hi : i ∈ impls ∧ Matches i g := mem_candidates.mp (h ▸ List.mem_singleton_self i)
    combine (i.constraints.attach.map fun c =>
      resolve impls wf (c.val.subst (matchingSubst i.head g.args)))
  | _ :: _ :: _ => .ambiguous
termination_by argsSize g.args
decreasing_by
  have hd := size_decreases (wf i _hi.1) c.property (matchingSubst i.head g.args)
  simpa only [Goal.subst, matched_head _hi.2] using hd

@[simp] theorem combine_single (r : Result) : combine [r] = r := by
  cases r <;> decide

@[simp] theorem combine_eq_resolved (rs : List Result) :
    combine rs = .resolved ↔ ∀ r ∈ rs, r = .resolved := by
  constructor
  · intro h r hr
    cases r <;> simp_all [combine]
    split at h <;> contradiction
  · intro h
    have ha : Result.ambiguous ∉ rs := by intro ha; cases h _ ha
    have hn : Result.noImpl ∉ rs := by intro hn; cases h _ hn
    simp [combine, ha, hn]

@[simp] theorem combine_eq_ambiguous (rs : List Result) :
    combine rs = .ambiguous ↔ .ambiguous ∈ rs := by
  by_cases ha : Result.ambiguous ∈ rs <;>
    by_cases hn : Result.noImpl ∈ rs <;> simp [combine, ha, hn]

@[simp] theorem combine_eq_noImpl (rs : List Result) :
    combine rs = .noImpl ↔ .ambiguous ∉ rs ∧ .noImpl ∈ rs := by
  by_cases ha : Result.ambiguous ∈ rs <;>
    by_cases hn : Result.noImpl ∈ rs <;> simp [combine, ha, hn]

theorem resolve_none (impls : List Impl) (wf : WellFormed impls) (g : Goal)
    (h : candidates impls g = []) : resolve impls wf g = .noImpl := by
  rw [resolve]; split <;> simp_all

theorem resolve_one (impls : List Impl) (wf : WellFormed impls) (g : Goal)
    (i : Impl) (h : candidates impls g = [i]) :
    resolve impls wf g = combine (i.constraints.map fun c =>
      resolve impls wf (c.subst (matchingSubst i.head g.args))) := by
  rw [resolve]; split <;> simp_all

theorem resolve_many (impls : List Impl) (wf : WellFormed impls) (g : Goal)
    (i j : Impl) (rest : List Impl) (h : candidates impls g = i :: j :: rest) :
    resolve impls wf g = .ambiguous := by
  rw [resolve]; split <;> simp_all

/-- Exact success semantics: there is one matching head, and every child succeeds. -/
theorem resolve_resolved_iff (impls : List Impl) (wf : WellFormed impls) (g : Goal) :
    resolve impls wf g = .resolved ↔ ∃ i, candidates impls g = [i] ∧
      ∀ c ∈ i.constraints, resolve impls wf (c.subst (matchingSubst i.head g.args)) = .resolved := by
  cases h : candidates impls g with
  | nil => simp [resolve_none impls wf g h]
  | cons i rest =>
    cases rest with
    | nil => simp [resolve_one impls wf g i h]
    | cons j rest => simp [resolve_many impls wf g i j rest h]

theorem resolve_sound (impls : List Impl) (wf : WellFormed impls) (g : Goal)
    (h : resolve impls wf g = .resolved) : Derives impls g := by
  obtain ⟨i, hi, children⟩ := (resolve_resolved_iff impls wf g).mp h
  have hm : i ∈ impls ∧ Matches i g := mem_candidates.mp (hi ▸ List.mem_singleton_self i)
  apply Derives.impl i (matchingSubst i.head g.args) hm.1 hm.2.1 (matched_head hm.2)
  intro c hc
  exact resolve_sound impls wf _ (children c hc)
termination_by argsSize g.args
decreasing_by
  simpa only [Goal.subst, matched_head hm.2] using
    size_decreases (wf i hm.1) hc (matchingSubst i.head g.args)

/-- At least two distinct matching impl values; no constraint has been tested. -/
def HeadOverlap (impls : List Impl) (g : Goal) : Prop :=
  2 ≤ (candidates impls g).length

theorem head_overlap_iff (impls : List Impl) (g : Goal) :
    HeadOverlap impls g ↔ ∃ i ∈ impls, ∃ j ∈ impls,
      i ≠ j ∧ Matches i g ∧ Matches j g := by
  constructor
  · intro h
    cases hs : candidates impls g with
    | nil => simp [HeadOverlap, hs] at h
    | cons i rest =>
      cases rest with
      | nil => simp [HeadOverlap, hs] at h
      | cons j rest =>
        have hi : i ∈ impls ∧ Matches i g := mem_candidates.mp (by simp [hs])
        have hj : j ∈ impls ∧ Matches j g := mem_candidates.mp (by simp [hs])
        have hn := candidates_nodup impls g
        rw [hs] at hn
        have ne : i ≠ j := by intro he; subst j; simp at hn
        exact ⟨i, hi.1, j, hj.1, ne, hi.2, hj.2⟩
  · rintro ⟨i, hi, j, hj, ne, mi, mj⟩
    have hmi := mem_candidates.mpr ⟨hi, mi⟩
    have hmj := mem_candidates.mpr ⟨hj, mj⟩
    cases hs : candidates impls g with
    | nil => simp [hs] at hmi
    | cons k rest =>
      cases rest with
      | nil => simp [hs] at hmi hmj; exact (ne (hmi.trans hmj.symm)).elim
      | cons _ _ => simp [HeadOverlap, hs]

/-- A finite path through unique matching heads ends at an overlapping goal.
All siblings are explored; no path passes through an already overlapping head. -/
inductive ReachesOverlap (impls : List Impl) : Goal → Prop where
  | here {g : Goal} (overlap : HeadOverlap impls g) : ReachesOverlap impls g
  | descend {g : Goal} {i : Impl} {c : Goal}
      (unique : candidates impls g = [i]) (constraint : c ∈ i.constraints)
      (child : ReachesOverlap impls (c.subst (matchingSubst i.head g.args))) :
      ReachesOverlap impls g

/-- Ambiguity is exactly a reachable head overlap, including overlaps in failing
siblings of the same unique candidate. -/
theorem resolve_ambiguous_iff (impls : List Impl) (wf : WellFormed impls) (g : Goal) :
    resolve impls wf g = .ambiguous ↔ ReachesOverlap impls g := by
  constructor
  · intro h
    cases hs : candidates impls g with
    | nil => simp [resolve_none impls wf g hs] at h
    | cons i rest =>
      cases rest with
      | nil =>
        rw [resolve_one impls wf g i hs] at h
        obtain ⟨c, hc, he⟩ := List.mem_map.mp ((combine_eq_ambiguous _).mp h)
        exact .descend hs hc ((resolve_ambiguous_iff impls wf _).mp he)
      | cons j rest => exact .here (by simp [HeadOverlap, hs])
  · intro h
    induction h with
    | @here g overlap =>
      cases hs : candidates impls g with
      | nil => simp [HeadOverlap, hs] at overlap
      | cons i rest =>
        cases rest with
        | nil => simp [HeadOverlap, hs] at overlap
        | cons j rest => exact resolve_many impls wf g i j rest hs
    | @descend g i c unique hc _ ih =>
      rw [resolve_one impls wf g i unique]
      exact (combine_eq_ambiguous _).mpr (List.mem_map.mpr ⟨c, hc, ih⟩)
termination_by argsSize g.args
decreasing_by
  have hm : i ∈ impls ∧ Matches i g := mem_candidates.mp (hs ▸ List.mem_singleton_self i)
  simpa only [Goal.subst, matched_head hm.2] using
    size_decreases (wf i hm.1) hc (matchingSubst i.head g.args)

/-- Completeness under absence of head overlap throughout the uniquely selected
constraint tree. Derivability supplies existence at every required node. -/
theorem resolve_complete (impls : List Impl) (wf : WellFormed impls) (g : Goal)
    (derivation : Derives impls g) (unique : ¬ ReachesOverlap impls g) :
    resolve impls wf g = .resolved := by
  cases derivation with
  | impl i σ member role head children =>
    have hm : i ∈ candidates impls g := mem_candidates.mpr ⟨member, role, σ, head⟩
    cases hs : candidates impls g with
    | nil => simp [hs] at hm
    | cons j rest =>
      cases rest with
      | nil =>
        have he : i = j := by simpa [hs] using hm
        subst j
        apply (resolve_resolved_iff impls wf g).mpr
        refine ⟨i, hs, ?_⟩
        intro c hc
        apply resolve_complete impls wf _
        · rw [matched_constraint (wf i member) σ head hc]
          exact children c hc
        · intro ho; exact unique (.descend hs hc ho)
      | cons k rest => exact (unique (.here (by simp [HeadOverlap, hs]))).elim
termination_by argsSize g.args
decreasing_by
  simpa only [Goal.subst, matched_head (show Matches i g from ⟨role, σ, head⟩)] using
    size_decreases (wf i member) hc (matchingSubst i.head g.args)

/-- Exact failure semantics, with the documented ambiguity priority. -/
theorem resolve_noImpl_iff (impls : List Impl) (wf : WellFormed impls) (g : Goal) :
    resolve impls wf g = .noImpl ↔ candidates impls g = [] ∨
      ∃ i, candidates impls g = [i] ∧
        (∀ c ∈ i.constraints, resolve impls wf (c.subst (matchingSubst i.head g.args)) ≠ .ambiguous) ∧
        ∃ c ∈ i.constraints, resolve impls wf (c.subst (matchingSubst i.head g.args)) = .noImpl := by
  cases hs : candidates impls g with
  | nil => simp [resolve_none impls wf g hs]
  | cons i rest =>
    cases rest with
    | nil =>
      rw [resolve_one impls wf g i hs]
      simp only [combine_eq_noImpl]
      simp [List.mem_map, eq_comm]
    | cons j rest => simp [resolve_many impls wf g i j rest hs]

theorem resolve_resolved_iff_derives (impls : List Impl) (wf : WellFormed impls)
    (g : Goal) (unique : ¬ ReachesOverlap impls g) :
    resolve impls wf g = .resolved ↔ Derives impls g :=
  ⟨resolve_sound impls wf g, fun h => resolve_complete impls wf g h unique⟩

namespace Examples

def int : Term := .app 0 []
def str : Term := .app 1 []
def list (t : Term) : Term := .app 2 [t]
def display (t : Term) : Goal := ⟨0, [t]⟩
def foo (t : Term) : Goal := ⟨1, [t]⟩

def listImpl : Impl := ⟨0, [list (.var 0)], [display (.var 0)], 0⟩
def intImpl : Impl := ⟨0, [int], [], 1⟩
def goodImpls : List Impl := [listImpl, intImpl]

theorem listImpl_wellFormed : listImpl.WellFormed := by
  simp [Impl.WellFormed, listImpl, display, list, argsSize, Term.size,
    argsOccurrences, Term.occurrences]

theorem intImpl_wellFormed : intImpl.WellFormed := by
  simp [Impl.WellFormed, intImpl]

theorem goodImpls_wellFormed : WellFormed goodImpls := by
  simp [WellFormed, goodImpls, listImpl_wellFormed, intImpl_wellFormed]

theorem nested_list_resolved :
    resolve goodImpls goodImpls_wellFormed (display (list (list int))) = .resolved := by
  rw [resolve_one goodImpls goodImpls_wellFormed _ listImpl (by decide)]
  change combine [resolve goodImpls goodImpls_wellFormed (display (list int))] = _
  rw [combine_single, resolve_one goodImpls goodImpls_wellFormed _ listImpl (by decide)]
  change combine [resolve goodImpls goodImpls_wellFormed (display int)] = _
  rw [combine_single, resolve_one goodImpls goodImpls_wellFormed _ intImpl (by decide)]
  rfl

theorem missing_str_noImpl :
    resolve goodImpls goodImpls_wellFormed (display (list str)) = .noImpl := by
  rw [resolve_one goodImpls goodImpls_wellFormed _ listImpl (by decide)]
  change combine [resolve goodImpls goodImpls_wellFormed (display str)] = _
  rw [combine_single]
  exact resolve_none _ _ _ (by decide)

/-- A rigid goal variable cannot be solved by the concrete int impl. -/
theorem rigid_variable_noImpl :
    resolve goodImpls goodImpls_wellFormed (display (.var 0)) = .noImpl := by
  exact resolve_none _ _ _ (by decide)

/-- Even structurally smaller constraints may duplicate a variable. -/
def duplicatingImpl : Impl :=
  ⟨1, [list (list (.var 0))], [⟨1, [.var 0, .var 0]⟩], 2⟩

theorem duplicating_not_wellFormed : ¬ duplicatingImpl.WellFormed := by
  intro wf
  have h := (wf ⟨1, [.var 0, .var 0]⟩ (by simp [duplicatingImpl])).2 0
  simp [duplicatingImpl, list, argsOccurrences, Term.occurrences] at h

def badImpl : Impl := ⟨1, [.var 0], [foo (list (.var 0))], 3⟩

theorem bad_not_wellFormed : ¬ badImpl.WellFormed := by
  intro wf
  have h := (wf (foo (list (.var 0))) (by simp [badImpl])).1
  simp [badImpl, foo, list, argsSize, Term.size] at h

/-- Stronger than Foo int: this database has no finite derivation for any goal.
Every purported derivation requires a strictly deeper child of the same rule. -/
theorem bad_no_derives (g : Goal) : ¬ Derives [badImpl] g := by
  intro h
  induction h with
  | impl i σ member _ _ _ ih =>
    have he : i = badImpl := by simpa using member
    subst i
    exact ih (foo (list (.var 0))) (by simp [badImpl])

theorem bad_foo_int_no_derives : ¬ Derives [badImpl] (foo int) := bad_no_derives _

/-- A distinct specific head overlaps the generic list head. -/
def specificImpl : Impl := ⟨0, [list int], [], 4⟩
def overlappingImpls : List Impl := [listImpl, specificImpl]

theorem overlappingImpls_wellFormed : WellFormed overlappingImpls := by
  apply (wellFormed_cons _ _).mpr
  exact ⟨listImpl_wellFormed, by simp [WellFormed, specificImpl, Impl.WellFormed]⟩

theorem overlap_ambiguous :
    resolve overlappingImpls overlappingImpls_wellFormed (display (list int)) = .ambiguous := by
  exact resolve_many _ _ _ listImpl specificImpl [] (by decide)

/-- The generic candidate would fail for str, but head overlap is still ambiguous. -/
def specificStrImpl : Impl := ⟨0, [list str], [], 5⟩

theorem failingOverlap_wellFormed : WellFormed [listImpl, specificStrImpl] := by
  apply (wellFormed_cons _ _).mpr
  exact ⟨listImpl_wellFormed, by simp [WellFormed, specificStrImpl, Impl.WellFormed]⟩

theorem overlap_before_constraints :
    resolve [listImpl, specificStrImpl] failingOverlap_wellFormed (display (list str)) = .ambiguous := by
  exact resolve_many _ _ _ listImpl specificStrImpl [] (by decide)

end Examples
end Yulang.Roles
