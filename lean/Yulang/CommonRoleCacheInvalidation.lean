import Yulang.CommonRoleSourceWorklist

/-! Dependency-directed invalidation for the actual producer. This implementation
fragment uses int-only materialization, not the full language's interval domain.
No state-changing saturation or final role classification is claimed. -/
namespace Yulang.CommonRoleCacheInvalidation
open CommonRoleMaterializedDomain CommonRoleSourceWorklist
open CommonRoleSettledConstraints (State)

def slots : Endpoint n → List (Fin n)
  | .fixed _ => []
  | .slot i => [i]
  | .wrap _ e => slots e

def dependencies (q : SourceRequest n) : List (Fin n) := slots q.lower ++ slots q.upper

def known (s : State n) (i : Fin n) : Bool :=
  decide (CommonRoleOrdinaryKnownness.materialize s.atoms i = some Roles.Examples.int)

def dirty (before after : State n) (q : SourceRequest n) : List (Fin n) :=
  (dependencies q).filter fun i => known before i != known after i

theorem dirty_exact (before after : State n) (q : SourceRequest n) (i : Fin n) :
    i ∈ dirty before after q ↔ i ∈ dependencies q ∧ known before i ≠ known after i := by
  simp [dirty]

theorem endpoint_unchanged (before after : State n) (e : Endpoint n)
    (same : ∀ i ∈ slots e, known before i = known after i) : e.eval before = e.eval after := by
  induction e with
  | fixed t => rfl
  | slot i =>
    have h := same i (by simp [slots])
    have eqv : (CommonRoleOrdinaryKnownness.materialize before.atoms i = some Roles.Examples.int) ↔
        (CommonRoleOrdinaryKnownness.materialize after.atoms i = some Roles.Examples.int) := by
      simpa [known] using congrArg (fun b => b = true) h
    simp only [Endpoint.eval]
    simp only [eqv]
  | wrap c e ih => exact congrArg (CommonRoleSettledSyntax.Ty.wrap c) (ih same)

theorem request_unchanged (before after : State n) (q : SourceRequest n)
    (same : ∀ i ∈ dependencies q, known before i = known after i) :
    q.eval before = q.eval after := by
  have lo := endpoint_unchanged before after q.lower
    (fun i h => same i (List.mem_append_left _ h))
  have hi := endpoint_unchanged before after q.upper
    (fun i h => same i (List.mem_append_right _ h))
  simp only [SourceRequest.eval, lo, hi]

theorem clean_iff (before after : State n) (q : SourceRequest n) :
    dirty before after q = [] ↔ ∀ i ∈ dependencies q, known before i = known after i := by
  simp [dirty, List.filter_eq_nil_iff]

/-- Cache reuse is justified from actual ordinary materialization, not from a
supplied equality of role outcomes. It is sufficient, not necessary. -/
theorem actual_next_cache_valid (registry : CommonRoleOpenProducer.Registry)
    (before after : State n) (q : SourceRequest n) (clean : dirty before after q = []) :
    actualNext registry before q = actualNext registry after q := by
  unfold actualNext
  rw [request_unchanged before after q ((clean_iff ..).mp clean)]

theorem changed_producer_has_dirty_dependency (registry : CommonRoleOpenProducer.Registry)
    (before after : State n) (q : SourceRequest n)
    (changed : actualNext registry before q ≠ actualNext registry after q) :
    ∃ i ∈ dependencies q, known before i ≠ known after i := by
  classical
  apply Classical.byContradiction
  intro absent
  have same : ∀ i ∈ dependencies q, known before i = known after i := by
    intro i member
    apply Classical.byContradiction
    intro different
    exact absent ⟨i, member, different⟩
  exact changed (actual_next_cache_valid registry before after q ((clean_iff ..).mpr same))

/-- Under consistent growth, invalidation is always caused by new int evidence.
Consistency is explicit; contradictory states cannot use this assertion. -/
theorem dirty_is_new_evidence (before after : State n) (q : SourceRequest n) (i : Fin n)
    (included : ∀ atom ∈ before.atoms, atom ∈ after.atoms)
    (assignment : Fin n → Core.PresenceGeneration.Comp Common.model)
    (models : PresenceNormalForm.All Common.model assignment after.atoms)
    (changed : i ∈ dirty before after q) : known before i = false ∧ known after i = true := by
  have different := ((dirty_exact ..).mp changed).2
  have monotone : known before i = true → known after i = true := by
    simp only [known, decide_eq_true_eq]
    exact materialized_int_persists before after i included assignment models
  cases hb : known before i <;> cases ha : known after i <;> simp_all

theorem changed_producer_has_new_evidence (registry : CommonRoleOpenProducer.Registry)
    (before after : State n) (q : SourceRequest n)
    (included : ∀ atom ∈ before.atoms, atom ∈ after.atoms)
    (assignment : Fin n → Core.PresenceGeneration.Comp Common.model)
    (models : PresenceNormalForm.All Common.model assignment after.atoms)
    (changed : actualNext registry before q ≠ actualNext registry after q) :
    ∃ i ∈ dependencies q, known before i = false ∧ known after i = true := by
  obtain ⟨i, member, different⟩ := changed_producer_has_dirty_dependency registry before after q changed
  exact ⟨i, member, dirty_is_new_evidence before after q i included assignment models
    ((dirty_exact ..).mpr ⟨member, different⟩)⟩

/-- A previously invalidating slot cannot invalidate again after consistent
monotone growth. States may contain arbitrary other ordinary atoms. -/
theorem dirty_cannot_repeat (a b c d : State n) (first last : SourceRequest n) (i : Fin n)
    (ab : ∀ atom ∈ a.atoms, atom ∈ b.atoms)
    (bc : ∀ atom ∈ b.atoms, atom ∈ c.atoms)
    (cd : ∀ atom ∈ c.atoms, atom ∈ d.atoms)
    (mb : b.Models) (mc : c.Models) (md : d.Models)
    (firstDirty : i ∈ dirty a b first) : i ∉ dirty c d last := by
  obtain ⟨vb, hb⟩ := mb
  obtain ⟨vc, hc⟩ := mc
  obtain ⟨vd, hd⟩ := md
  have kb := (dirty_is_new_evidence a b first i ab vb hb firstDirty).2
  have kc : known c i = true := by
    simp only [known, decide_eq_true_eq] at kb ⊢
    exact materialized_int_persists b c i bc vc hc kb
  intro lastDirty
  have notkc := (dirty_is_new_evidence c d last i cd vd hd lastDirty).1
  rw [kc] at notkc
  cases notkc

/-- No change in watched ordinary materialization means the complete fixed-state
reachability cache can be reused, not only one parent's immediate child list. -/
theorem reach_cache_valid (registry : CommonRoleOpenProducer.Registry) (root : SourceRequest n)
    (before after : State n)
    (clean : ∀ q : Node registry root, dirty before after q.val = [])
    (q : Node registry root) : Reach registry root before q ↔ Reach registry root after q := by
  constructor
  · intro h
    induction h with
    | root => exact .root
    | @step parent child _ edge ih =>
      exact .step ih (by rw [← actual_next_cache_valid registry before after parent.val (clean parent)]; exact edge)
  · intro h
    induction h with
    | root => exact .root
    | @step parent child _ edge ih =>
      exact .step ih (by rw [actual_next_cache_valid registry before after parent.val (clean parent)]; exact edge)

theorem saturated_membership_cache_valid (registry : CommonRoleOpenProducer.Registry)
    (root : SourceRequest n) (before after : State n)
    (clean : ∀ q : Node registry root, dirty before after q.val = []) (q : Node registry root) :
    q ∈ saturate registry root before ↔ q ∈ saturate registry root after := by
  rw [saturate_exact, saturate_exact]
  exact reach_cache_valid registry root before after clean q

/-- At most n strict producer invalidation events can occur along a consistent
monotone trace on n source slots. This bounds producer changes, NOT all ordinary
fact updates, and does not establish a complete saturation driver's termination. -/
theorem producer_change_events_bounded (registry : CommonRoleOpenProducer.Registry)
    (states : Nat → State n) (queries : Fin k → SourceRequest n)
    (monotone : ∀ a b, a ≤ b → ∀ atom ∈ (states a).atoms, atom ∈ (states b).atoms)
    (consistent : ∀ t, t ≤ k → (states t).Models)
    (changes : ∀ t : Fin k,
      actualNext registry (states t.val) (queries t) ≠
        actualNext registry (states (t.val + 1)) (queries t)) : k ≤ n := by
  classical
  have witnesses : ∀ t : Fin k, ∃ i : Fin n,
      known (states t.val) i = false ∧ known (states (t.val + 1)) i = true := by
    intro t
    obtain ⟨assignment, models⟩ := consistent (t.val + 1) (by omega)
    obtain ⟨i, _, h⟩ := changed_producer_has_new_evidence registry
      (states t.val) (states (t.val + 1)) (queries t)
      (monotone _ _ (by omega)) assignment models (changes t)
    exact ⟨i, h⟩
  let witness : Fin k → Fin n := fun t => Classical.choose (witnesses t)
  have props (t : Fin k) : known (states t.val) (witness t) = false ∧
      known (states (t.val + 1)) (witness t) = true := Classical.choose_spec (witnesses t)
  have distinct : ∀ a b : Fin k, a.val < b.val → witness a ≠ witness b := by
    intro a b lt eq
    have ka := (props a).2
    have kb := (props b).1
    obtain ⟨assignment, models⟩ := consistent b.val (by omega)
    have persists : known (states b.val) (witness a) = true := by
      simp only [known, decide_eq_true_eq] at ka ⊢
      exact materialized_int_persists (states (a.val + 1)) (states b.val) (witness a) (monotone (a.val + 1) b.val (by omega)) assignment models ka
    rw [eq] at persists
    rw [persists] at kb
    cases kb
  have inj : ∀ a b : Fin k, a ≠ b → witness a ≠ witness b := by
    intro a b ne
    have vals : a.val ≠ b.val := fun eq => ne (Fin.ext eq)
    rcases Nat.lt_or_gt_of_ne vals with lt | gt
    · exact distinct a b lt
    · exact fun eq => distinct b a gt eq.symm
  have nd : ((List.finRange k).map witness).Nodup :=
    List.Pairwise.map witness inj (List.nodup_finRange k)
  have bound := nd.length_le_of_subset (l₂ := List.finRange n)
    (fun i _ => List.mem_finRange i)
  simpa using bound

end Yulang.CommonRoleCacheInvalidation
