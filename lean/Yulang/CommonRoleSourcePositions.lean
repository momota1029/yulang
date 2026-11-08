import Yulang.CommonRoleCaptureOrigin

/-! Finite structural source positions and copied-subtree provenance in the
unary producer. This is not a global source identity allocator or saturation. -/
namespace Yulang.CommonRoleSourcePositions
open CommonRoleSettledSyntax CommonRoleOpenProducer CommonRoleCaptureOrigin

/-- An independent path judgment. Regular loop leaves are not unfolded. -/
inductive SourcePosition : Ty → Nat → Ty → Prop where
  | root (t : Ty) : SourcePosition t 0 t
  | wrap : SourcePosition t n payload → SourcePosition (.wrap c t) (n + 1) payload

theorem position_exact (t payload : Ty) (n : Nat) :
    atDepth n t = some payload ↔ SourcePosition t n payload := by
  constructor
  · induction n generalizing t with
    | zero => intro h; have eq : t = payload := Option.some.inj h; subst payload; exact .root t
    | succ n ih =>
      cases t <;> simp only [atDepth]
      all_goals try { intro h; cases h }
      exact fun h => .wrap (ih _ h)
  · intro h
    induction h with
    | root => rfl
    | wrap _ ih => exact ih

theorem position_bound (t payload : Ty) (n : Nat)
    (h : SourcePosition t n payload) : n < t.nodes := by
  induction h with
  | root => exact Ty.nodes_pos _
  | wrap _ ih => simpa [Ty.nodes] using Nat.succ_lt_succ ih

theorem position_exists (t : Ty) (n : Nat) :
    (∃ payload, SourcePosition t n payload) ↔ n < t.nodes := by
  constructor
  · rintro ⟨payload, h⟩; exact position_bound t payload n h
  · induction n generalizing t with
    | zero => intro _; exact ⟨t, .root t⟩
    | succ n ih =>
      cases t <;> simp only [Ty.nodes]
      all_goals try { omega }
      intro h
      rename_i c innerTy
      obtain ⟨payload, inner⟩ := ih innerTy (by omega)
      exact ⟨payload, .wrap inner⟩

/-- Selector composition respects the entire copied subtree, not only its root. -/
theorem atDepth_add (n k : Nat) (t : Ty) :
    atDepth (n + k) t = (atDepth n t).bind (atDepth k) := by
  induction n generalizing t with
  | zero => simp [atDepth]
  | succ n ih =>
    cases t <;> simp [Nat.succ_add, atDepth, ih]

/-- Every successful actual capture has finite source coordinates in each endpoint. -/
theorem production_positions (visible : List Declaration) (q : Request)
    (d : Declaration) (lp hp : Ty) (h : Nat)
    (produced : production visible q = some (d, lp, hp))
    (located : captureDepth d.head = some h) :
    SourcePosition q.lower h lp ∧ SourcePosition q.upper h hp ∧
      h < q.lower.nodes ∧ h < q.upper.nodes := by
  obtain ⟨lo, hi⟩ := production_origin visible q d lp hp h produced located
  have l := (position_exact _ _ _).mp lo
  have u := (position_exact _ _ _).mp hi
  exact ⟨l, u, position_bound _ _ _ l, position_bound _ _ _ u⟩

/-- All descendants of a variable-bearing child's payload retain parent positions.
The hypothesis is actual production, not assumed correctness of a new driver. -/
theorem copied_subtree_origin (visible : List Declaration) (q : Request)
    (d : Declaration) (lp hp : Ty) (r : Nat × Template) (h v k : Nat)
    (produced : production visible q = some (d, lp, hp))
    (located : captureDepth d.head = some h)
    (_required : r ∈ d.requirements) (varLocated : variableDepth r.2 = some v) :
    atDepth (v + k) (r.2.instantiate lp) = atDepth (h + k) q.lower ∧
    atDepth (v + k) (r.2.instantiate hp) = atDepth (h + k) q.upper := by
  obtain ⟨lo, hi⟩ := production_origin visible q d lp hp h produced located
  simp only [atDepth_add, instantiate_origin r.2 lp v varLocated,
    instantiate_origin r.2 hp v varLocated, lo, hi]
  exact ⟨True.intro, True.intro⟩

/-- Exact correspondence of descendant positions, in both directions. -/
theorem copied_positions_exact (visible : List Declaration) (q : Request)
    (d : Declaration) (lp hp payload : Ty) (r : Nat × Template) (h v k : Nat)
    (produced : production visible q = some (d, lp, hp))
    (located : captureDepth d.head = some h)
    (required : r ∈ d.requirements) (varLocated : variableDepth r.2 = some v) :
    (SourcePosition (r.2.instantiate lp) (v + k) payload ↔
      SourcePosition q.lower (h + k) payload) ∧
    (SourcePosition (r.2.instantiate hp) (v + k) payload ↔
      SourcePosition q.upper (h + k) payload) := by
  obtain ⟨lo, hi⟩ := copied_subtree_origin visible q d lp hp r h v k
    produced located required varLocated
  simp only [← position_exact, lo, hi]
  exact ⟨True.intro, True.intro⟩

/-- The statement applies to every child returned by the actual producer. -/
theorem child_subtree_origin (visible : List Declaration) (q child : Request)
    (d : Declaration) (lp hp : Ty) (h : Nat)
    (produced : production visible q = some (d, lp, hp))
    (located : captureDepth d.head = some h)
    (member : child ∈ children q d lp hp) :
    ∃ r ∈ d.requirements, child.role = r.1 ∧
      ∀ v, variableDepth r.2 = some v → ∀ k,
        atDepth (v + k) child.lower = atDepth (h + k) q.lower ∧
        atDepth (v + k) child.upper = atDepth (h + k) q.upper := by
  obtain ⟨r, required, rfl⟩ := List.mem_map.mp member
  refine ⟨r, required, rfl, ?_⟩
  intro v varLocated k
  exact copied_subtree_origin visible q d lp hp r h v k produced located required varLocated

end Yulang.CommonRoleSourcePositions
