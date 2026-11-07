import Yulang.CommonOptionalPool
import Yulang.CommonGeneratedPoolRows

/-!
# Simple arrow rows survive optional-bound pool extension

An added required/optional node refers only to a top payload or an original
node. It introduces no arrow annotation. Thus the entire extended pool has
variable/empty arrow rows exactly when the original pool does, for every
finite query list. No row interpretation or solver certificate is involved.
-/

namespace Yulang.CommonOptionalPoolRows

open Core.PresenceGeneration (TyTerm)
open PresenceOpenTailGenerationLowering (Pool)
open CommonOptionalPool
open CommonGeneratedPoolRows (AllSimpleRows)
open PresenceSourceConstraintSupport (simpleTyRows)
open CommonPresenceConstraintGraph (splitAtoms)

variable {m : Nat}

theorem member_rows (pool : Pool m) (good : AllSimpleRows pool)
    (term : TyTerm (Fin m)) (member : term ∈ pool.terms) : simpleTyRows term = true := by
  simpa only [Pool.termAt_reference] using good (pool.reference term member)

theorem payload_rows (pool : Pool m) (good : AllSimpleRows pool) (query : Query pool) :
    simpleTyRows (payloadTerm pool query) = true := by
  cases found : query.2 with
  | none => simp only [payloadTerm, found, simpleTyRows]
  | some index => simpa only [payloadTerm, found] using good index

theorem candidate_rows (pool : Pool m) (good : AllSimpleRows pool) (queries : List (Query pool))
    (term : TyTerm (Fin m)) (member : term ∈ candidates pool queries) : simpleTyRows term = true := by
  rcases List.mem_append.mp member with constant | added
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at constant
    rcases constant with rfl | rfl | rfl <;> rfl
  · obtain ⟨query, _, selected⟩ := List.mem_flatMap.mp added
    rcases List.mem_cons.mp selected with rfl | selected
    · exact payload_rows pool good query
    · have same := List.mem_singleton.mp selected
      subst term
      simpa only [optionalTerm, requiredTerm, simpleTyRows, Bool.true_and] using payload_rows pool good query

theorem extend_rows (pool : Pool m) (good : AllSimpleRows pool) (queries : List (Query pool)) :
    AllSimpleRows (extend pool queries) := by
  intro index
  have member := (extend pool queries).at_mem index
  rcases List.mem_append.mp member with old | fresh
  · exact member_rows pool good _ old
  · exact candidate_rows pool good queries _ ((fresh_member pool queries _).mp fresh).1

theorem restrict_rows (pool : Pool m) (queries : List (Query pool))
    (good : AllSimpleRows (extend pool queries)) : AllSimpleRows pool := by
  intro index
  simpa only [termAt_embed] using good (embed pool queries index)

theorem allSimpleRows_iff (pool : Pool m) (queries : List (Query pool)) :
    AllSimpleRows (extend pool queries) ↔ AllSimpleRows pool :=
  ⟨restrict_rows pool queries, fun good => extend_rows pool good queries⟩

theorem generated_extended_pool_rows (expression : Inference.Expr)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (generated : clause ∈ PresenceNormalForm.normalise (Core.PresenceGeneration.principal
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (queries : List (Query (splitAtoms clause.pack).pool)) :
    AllSimpleRows (extend (splitAtoms clause.pack).pool queries) :=
  extend_rows _ (CommonGeneratedPoolRows.generated_pool_rows expression clause generated) queries

theorem generated_core_extended_pool_rows (expression : Core.Required.Term)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (generated : clause ∈ PresenceNormalForm.normalise (Core.PresenceGeneration.CoreRules.principalCore
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (queries : List (Query (splitAtoms clause.pack).pool)) :
    AllSimpleRows (extend (splitAtoms clause.pack).pool queries) :=
  extend_rows _ (CommonGeneratedPoolRows.generated_core_pool_rows expression clause generated) queries

end Yulang.CommonOptionalPoolRows
