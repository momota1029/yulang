import Yulang.CommonOptionalPool
import Yulang.CommonGeneratedWidth

/-!
# Width invariants are unchanged by optional-bound pool extension

The new candidate nodes have only constant, required or optional-union heads.
They add no record construction or whole default. Every node requiring a
tail/source width is therefore an original node, with the same original ID.

The equivalence below holds for arbitrary extended node assignments. It
assumes no constructor equations, edge model or solver output.
-/

namespace Yulang.CommonOptionalPoolWidth

open Common (Ty)
open Core.PresenceGeneration (TyTerm)
open PresenceOpenTailGenerationLowering (Pool subterms)
open CommonOptionalPool
open PresenceGeneratedWidth (widthTail)
open CommonGeneratedWidth (PoolWidth)

variable {m : Nat}

theorem candidate_no_width (pool : Pool m) (queries : List (Query pool))
    (term : TyTerm (Fin m)) (member : term ∈ candidates pool queries) : widthTail term = none := by
  rcases List.mem_append.mp member with constant | added
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at constant
    rcases constant with rfl | rfl | rfl <;> rfl
  · obtain ⟨query, _, selected⟩ := List.mem_flatMap.mp added
    rcases List.mem_cons.mp selected with rfl | selected
    · rfl
    · have same := List.mem_singleton.mp selected
      subst term
      rfl

theorem width_node_original (pool : Pool m) (queries : List (Query pool))
    (term tail : TyTerm (Fin m)) (member : term ∈ (extend pool queries).terms)
    (needed : widthTail term = some tail) : term ∈ pool.terms := by
  rcases List.mem_append.mp member with old | fresh
  · exact old
  · have absent := candidate_no_width pool queries term ((fresh_member pool queries term).mp fresh).1
    rw [absent] at needed
    cases needed

theorem widthTail_subterm (term tail : TyTerm (Fin m))
    (needed : widthTail term = some tail) : tail ∈ subterms term := by
  cases term with
  | record _ head rest | recordDefault _ rest head =>
      have same : rest = tail := Option.some.inj needed
      subst tail
      simp [subterms]
  | _ => cases needed

@[simp] theorem embed_reference (pool : Pool m) (queries : List (Query pool))
    (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    embed pool queries (pool.reference term member) =
      (extend pool queries).reference term (original_member pool queries term member) := by
  simp only [embed, Pool.termAt_reference]

/-- Every extended assignment, without a realization or any edge condition. -/
theorem pool_width_iff (pool : Pool m) (queries : List (Query pool))
    (values : Fin (extend pool queries).size → Ty) :
    PoolWidth (extend pool queries) values ↔ PoolWidth pool (restrictValues pool queries values) := by
  constructor
  · intro widths term member tail needed tailMember
    simpa only [restrictValues, Function.comp_def, embed_reference] using
      widths term (original_member pool queries term member) tail needed
        (original_member pool queries tail tailMember)
  · intro widths term member tail needed tailMember
    have old := width_node_original pool queries term tail member needed
    have oldTail := pool.closed term old tail (widthTail_subterm term tail needed)
    simpa only [restrictValues, Function.comp_def, embed_reference] using
      widths term old tail needed oldTail

end Yulang.CommonOptionalPoolWidth
