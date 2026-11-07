import Yulang.CommonOptionalGraphExtension

/-!
# A finite optional-bound extension of the actual source pool

The old pool remains the initial segment, so every original node number is
unchanged. Only top, width, exact empty, required bounds and their optional
unions can be added. Existing terms are shared instead of duplicated. This
keeps the ordinary pool-based variable-bound solver available for the new
bound syntax, without changing row identities or assuming a model.
-/

namespace Yulang.CommonOptionalPool

open Core.PresenceGeneration (TyTerm)
open PresenceOpenTailGenerationLowering (Pool subterms)
open TypeConstraintGraph (unique mem_unique unique_nodup)

variable {m : Nat}

abbrev Query (pool : Pool m) := CommonOptionalGraphExtension.Query pool.size

def payloadTerm (pool : Pool m) (query : Query pool) : TyTerm (Fin m) :=
  match query.2 with
  | none => .top
  | some slot => pool.termAt slot

def requiredTerm (pool : Pool m) (query : Query pool) : TyTerm (Fin m) :=
  .required query.1 (payloadTerm pool query)

def optionalTerm (pool : Pool m) (query : Query pool) : TyTerm (Fin m) :=
  .union .exactEmpty (requiredTerm pool query)

def candidates (pool : Pool m) (queries : List (Query pool)) : List (TyTerm (Fin m)) :=
  [.top, .emptyRecord, .exactEmpty] ++
    queries.flatMap (fun query => [requiredTerm pool query, optionalTerm pool query])

def freshTerms (pool : Pool m) (queries : List (Query pool)) : List (TyTerm (Fin m)) :=
  (unique (candidates pool queries)).filter (fun term => decide (term ∉ pool.terms))

theorem fresh_member (pool : Pool m) (queries : List (Query pool)) (term : TyTerm (Fin m)) :
    term ∈ freshTerms pool queries ↔ term ∈ candidates pool queries ∧ term ∉ pool.terms := by
  simp only [freshTerms, List.mem_filter, mem_unique, decide_eq_true_eq]

theorem fresh_nodup (pool : Pool m) (queries : List (Query pool)) :
    (freshTerms pool queries).Nodup := (unique_nodup _).filter _

theorem candidate_present (pool : Pool m) (queries : List (Query pool)) (term : TyTerm (Fin m))
    (member : term ∈ candidates pool queries) : term ∈ pool.terms ++ freshTerms pool queries := by
  by_cases old : term ∈ pool.terms
  · exact List.mem_append_left _ old
  · exact List.mem_append_right _ ((fresh_member pool queries term).mpr ⟨member, old⟩)

theorem required_candidate (pool : Pool m) (queries : List (Query pool)) (query : Query pool)
    (member : query ∈ queries) : requiredTerm pool query ∈ candidates pool queries :=
  List.mem_append_right _ (List.mem_flatMap.mpr ⟨query, member, List.mem_cons_self⟩)

theorem optional_candidate (pool : Pool m) (queries : List (Query pool)) (query : Query pool)
    (member : query ∈ queries) : optionalTerm pool query ∈ candidates pool queries :=
  List.mem_append_right _ (List.mem_flatMap.mpr
    ⟨query, member, List.mem_cons_of_mem _ List.mem_cons_self⟩)

private theorem payload_closed (pool : Pool m) (queries : List (Query pool)) (query : Query pool)
    (child : TyTerm (Fin m)) (inside : child ∈ subterms (payloadTerm pool query)) :
    child ∈ pool.terms ∨ child ∈ candidates pool queries := by
  cases payload : query.2 with
  | none =>
      have same : child = .top := by simpa [payloadTerm, payload, subterms] using inside
      subst child
      exact Or.inr (by simp [candidates])
  | some slot =>
      apply Or.inl
      exact pool.closed _ (pool.at_mem slot) child (by simpa [payloadTerm, payload] using inside)

private theorem required_closed (pool : Pool m) (queries : List (Query pool)) (query : Query pool)
    (member : query ∈ queries) (child : TyTerm (Fin m))
    (inside : child ∈ subterms (requiredTerm pool query)) :
    child ∈ pool.terms ∨ child ∈ candidates pool queries := by
  rcases List.mem_cons.mp inside with rfl | inside
  · exact Or.inr (required_candidate pool queries query member)
  · exact payload_closed pool queries query child inside

theorem candidates_closed (pool : Pool m) (queries : List (Query pool))
    (term : TyTerm (Fin m)) (member : term ∈ candidates pool queries)
    (child : TyTerm (Fin m)) (inside : child ∈ subterms term) :
    child ∈ pool.terms ∨ child ∈ candidates pool queries := by
  rcases List.mem_append.mp member with constant | added
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at constant
    rcases constant with rfl | rfl | rfl <;>
      have same := List.mem_singleton.mp inside <;> subst child <;>
      exact Or.inr (by simp [candidates])
  · obtain ⟨query, present, selected⟩ := List.mem_flatMap.mp added
    rcases List.mem_cons.mp selected with rfl | selected
    · exact required_closed pool queries query present child inside
    · have same := List.mem_singleton.mp selected
      subst term
      rcases List.mem_cons.mp inside with rfl | inner
      · exact Or.inr (optional_candidate pool queries query present)
      · rcases List.mem_append.mp inner with empty | required
        · have same := List.mem_singleton.mp empty
          subst child
          exact Or.inr (by simp [candidates])
        · exact required_closed pool queries query present child required

/-- A genuine shared source pool, with no semantic law or solver certificate. -/
def extend (pool : Pool m) (queries : List (Query pool)) : Pool m where
  terms := pool.terms ++ freshTerms pool queries
  distinct := List.nodup_append.mpr ⟨pool.distinct, fresh_nodup pool queries, by
    intro old present fresh member same
    have absent := ((fresh_member pool queries fresh).mp member).2
    exact absent (same ▸ present)⟩
  variables := fun index => List.mem_append_left _ (pool.variables index)
  closed := by
    intro term member child inside
    rcases List.mem_append.mp member with old | fresh
    · exact List.mem_append_left _ (pool.closed term old child inside)
    · have candidate := ((fresh_member pool queries term).mp fresh).1
      exact (candidates_closed pool queries term candidate child inside).elim
        (List.mem_append_left _) (candidate_present pool queries child)

theorem original_member (pool : Pool m) (queries : List (Query pool))
    (term : TyTerm (Fin m)) (member : term ∈ pool.terms) : term ∈ (extend pool queries).terms :=
  List.mem_append_left _ member

theorem candidate_member (pool : Pool m) (queries : List (Query pool))
    (term : TyTerm (Fin m)) (member : term ∈ candidates pool queries) :
    term ∈ (extend pool queries).terms := candidate_present pool queries term member

def embed (pool : Pool m) (queries : List (Query pool)) (slot : Fin pool.size) :
    Fin (extend pool queries).size :=
  (extend pool queries).reference (pool.termAt slot)
    (original_member pool queries _ (pool.at_mem slot))

/-- This is numerical ID preservation, not just a new renaming convention. -/
@[simp] theorem embed_val (pool : Pool m) (queries : List (Query pool)) (slot : Fin pool.size) :
    (embed pool queries slot).val = slot.val := by
  change (pool.terms ++ freshTerms pool queries).idxOf (pool.termAt slot) = slot.val
  rw [List.idxOf_append, ite_eq_left (pool.at_mem slot)]
  exact pool.distinct.idxOf_getElem slot.val slot.isLt

@[simp] theorem termAt_embed (pool : Pool m) (queries : List (Query pool)) (slot : Fin pool.size) :
    (extend pool queries).termAt (embed pool queries slot) = pool.termAt slot :=
  Pool.termAt_reference _ _ _

theorem embed_injective (pool : Pool m) (queries : List (Query pool)) :
    Function.Injective (embed pool queries) := by
  intro first last same
  apply Fin.ext
  simpa only [embed_val] using congrArg Fin.val same

@[simp] theorem input_embed (pool : Pool m) (queries : List (Query pool)) (index : Fin m) :
    (extend pool queries).input index = embed pool queries (pool.input index) := by
  apply Fin.ext
  rw [embed_val]
  change (pool.terms ++ freshTerms pool queries).idxOf (.var index) = pool.terms.idxOf (.var index)
  rw [List.idxOf_append, ite_eq_left (pool.variables index)]

def restrictValues (pool : Pool m) (queries : List (Query pool))
    (values : Fin (extend pool queries).size → Common.Ty) : Fin pool.size → Common.Ty :=
  values ∘ embed pool queries

@[simp] theorem restrict_inputs (pool : Pool m) (queries : List (Query pool))
    (values : Fin (extend pool queries).size → Common.Ty) :
    CommonPresenceConstraintGraph.restrict (extend pool queries) values =
      CommonPresenceConstraintGraph.restrict pool (restrictValues pool queries values) := by
  funext index
  simp only [CommonPresenceConstraintGraph.restrict, input_embed, restrictValues, Function.comp_def]

theorem restrict_realizes (pool : Pool m) (queries : List (Query pool))
    (rows : Fin m → Common.Row) (values : Fin (extend pool queries).size → Common.Ty)
    (realizes : CommonPresenceConstraintGraph.Realizes (extend pool queries) rows values) :
    CommonPresenceConstraintGraph.Realizes pool rows (restrictValues pool queries values) := by
  let original := restrictValues pool queries values
  let canonical := CommonPresenceConstraintGraph.extend pool rows
    (CommonPresenceConstraintGraph.restrict pool original)
  have same (index : Fin pool.size) : Common.Equivalent (canonical index) (original index) := by
    have decoded := CommonPresenceConstraintGraph.realizes_evaluate (extend pool queries)
      rows values realizes (pool.termAt index) (original_member pool queries _ (pool.at_mem index))
    rw [restrict_inputs] at decoded
    exact Common.equivalent_symm decoded
  exact (CommonOptionalGraphExtension.realizes_congr (CommonPresenceConstraintGraph.graph pool)
    rows canonical original same).mp (CommonPresenceConstraintGraph.extend_realizes pool rows _)

/-- Original values are retained literally; new nodes are independently
evaluated from the original input slots. No solver is consulted. -/
def extendValues (pool : Pool m) (queries : List (Query pool)) (rows : Fin m → Common.Row)
    (values : Fin pool.size → Common.Ty) : Fin (extend pool queries).size → Common.Ty :=
  fun index => if old : index.val < pool.size then values ⟨index.val, old⟩
    else CommonPresenceConstraintGraph.evaluate rows
      (CommonPresenceConstraintGraph.restrict pool values) ((extend pool queries).termAt index)

@[simp] theorem extendValues_original (pool : Pool m) (queries : List (Query pool))
    (rows : Fin m → Common.Row) (values : Fin pool.size → Common.Ty) (index : Fin pool.size) :
    extendValues pool queries rows values (embed pool queries index) = values index := by
  simp only [extendValues, embed_val, index.isLt, ↓reduceDIte]

@[simp] theorem restrict_extend (pool : Pool m) (queries : List (Query pool))
    (rows : Fin m → Common.Row) (values : Fin pool.size → Common.Ty) :
    restrictValues pool queries (extendValues pool queries rows values) = values := by
  funext index
  exact extendValues_original pool queries rows values index

theorem extend_realizes (pool : Pool m) (queries : List (Query pool))
    (rows : Fin m → Common.Row) (values : Fin pool.size → Common.Ty)
    (realizes : CommonPresenceConstraintGraph.Realizes pool rows values) :
    CommonPresenceConstraintGraph.Realizes (extend pool queries) rows
      (extendValues pool queries rows values) := by
  let canonical := CommonPresenceConstraintGraph.extend (extend pool queries) rows
    (CommonPresenceConstraintGraph.restrict pool values)
  have same (index : Fin (extend pool queries).size) :
      Common.Equivalent (canonical index) (extendValues pool queries rows values index) := by
    by_cases old : index.val < pool.size
    · let original : Fin pool.size := ⟨index.val, old⟩
      have identity : index = embed pool queries original := by
        apply Fin.ext
        exact (embed_val pool queries original).symm
      rw [identity, extendValues_original]
      have decoded := CommonPresenceConstraintGraph.realizes_evaluate pool rows values realizes
        (pool.termAt original) (pool.at_mem original)
      rw [Pool.reference_termAt] at decoded
      change Common.Equivalent
        (CommonPresenceConstraintGraph.evaluate rows (CommonPresenceConstraintGraph.restrict pool values)
          ((extend pool queries).termAt (embed pool queries original))) (values original)
      rw [termAt_embed]
      exact Common.equivalent_symm decoded
    · change Common.Equivalent _ (if bound : index.val < pool.size then _ else _)
      rw [dite_eq_right old]
      exact Common.equivalent_refl _
  exact (CommonOptionalGraphExtension.realizes_congr
    (CommonPresenceConstraintGraph.graph (extend pool queries)) rows canonical
    (extendValues pool queries rows values) same).mp
      (CommonPresenceConstraintGraph.extend_realizes (extend pool queries) rows _)

/-- Exact conservative extension of every actual source pool, with literal
readback of all old nodes and the identical independent row assignment. -/
theorem exists_extension_exact (pool : Pool m) (queries : List (Query pool))
    (rows : Fin m → Common.Row) (values : Fin pool.size → Common.Ty) :
    CommonPresenceConstraintGraph.Realizes pool rows values ↔
      ∃ extended : Fin (extend pool queries).size → Common.Ty,
        CommonPresenceConstraintGraph.Realizes (extend pool queries) rows extended ∧
          restrictValues pool queries extended = values := by
  constructor
  · intro realizes
    exact ⟨extendValues pool queries rows values, extend_realizes pool queries rows values realizes,
      restrict_extend pool queries rows values⟩
  · rintro ⟨extended, realizes, same⟩
    simpa only [same] using restrict_realizes pool queries rows extended realizes

theorem candidates_length (pool : Pool m) (queries : List (Query pool)) :
    (candidates pool queries).length = 3 + 2 * queries.length := by
  have each (entries : List (Query pool)) :
      (entries.flatMap (fun query => [requiredTerm pool query, optionalTerm pool query])).length =
        2 * entries.length := by
    induction entries with
    | nil => rfl
    | cons query rest ih =>
        simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]
        omega
  simpa only [candidates, List.length_append, List.length_cons, List.length_nil] using
    congrArg (3 + ·) (each queries)

theorem size_bound (pool : Pool m) (queries : List (Query pool)) :
    (extend pool queries).size ≤ pool.size + 3 + 2 * queries.length := by
  have bound : (freshTerms pool queries).length ≤ (candidates pool queries).length :=
    (fresh_nodup pool queries).length_le_of_subset
      (fun term member => ((fresh_member pool queries term).mp member).1)
  change (pool.terms ++ freshTerms pool queries).length ≤ _
  rw [List.length_append]
  rw [candidates_length] at bound
  change pool.size + (freshTerms pool queries).length ≤ _
  omega

end Yulang.CommonOptionalPool
