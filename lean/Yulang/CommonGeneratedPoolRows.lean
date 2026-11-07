import Yulang.CommonGeneratedRigidPool
import Yulang.CommonPresenceSourceFamily

/-!
# Row annotations throughout the actual generated shared pool

Every nested arrow in every collected node keeps variable/empty row
annotations. The invariant is inherited by all subterms and is established
from actual source generation, normalization and packing. It therefore
covers child references created by rigid inspection, including the reversed
input comparison of an arrow, without requiring a successful row solver.

This is a finite-pool syntax invariant. It does not claim closure of new
projection nodes or solve the remaining value constraints.
-/

namespace Yulang.CommonGeneratedPoolRows

open Core.PresenceGeneration (TyTerm RowTerm)
open PresenceNormalForm (Atom Clause normalise)
open PresenceOpenTailGenerationLowering (Pool Problem subterms collect)
open CommonPresenceConstraintGraph (splitAtoms)
open PresenceSourceConstraintSupport (simpleRow simpleTyRows GoodAtoms GoodAtom)

variable {m : Nat}

theorem subterm_rows (term child : TyTerm (Fin m)) (good : simpleTyRows term = true)
    (member : child ∈ subterms term) : simpleTyRows child = true := by
  induction term with
  | var | base | bottom | top | emptyRecord | exactEmpty =>
      have same := List.mem_singleton.mp member
      subst child
      exact good
  | union first last before after | inter first last before after
  | pair first last before after | record _ first last before after
  | recordDefault _ first last before after =>
      rcases List.mem_cons.mp member with rfl | member
      · exact good
      · have both := Bool.and_eq_true_iff.mp good
        exact (List.mem_append.mp member).elim (before both.1) (after both.2)
  | required _ payload ih | variant _ payload ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact good
      · exact ih good member
  | arrow input incoming output outgoing before after =>
      rcases List.mem_cons.mp member with rfl | member
      · exact good
      · have parts : ((simpleTyRows input = true ∧ simpleRow incoming = true) ∧
            simpleTyRows output = true) ∧ simpleRow outgoing = true := by
          simpa only [simpleTyRows, Bool.and_eq_true] using good
        exact (List.mem_append.mp member).elim (before parts.1.1.1) (after parts.1.2)

theorem collected_rows (roots : List (TyTerm (Fin m)))
    (good : ∀ term ∈ roots, simpleTyRows term = true)
    (term : TyTerm (Fin m)) (member : term ∈ (collect roots).terms) :
    simpleTyRows term = true := by
  have original := (TypeConstraintGraph.mem_unique _ _).mp member
  rcases List.mem_append.mp original with input | rooted
  · obtain ⟨index, rfl⟩ := List.mem_ofFn.mp input
    rfl
  · obtain ⟨root, present, inside⟩ := List.mem_flatMap.mp rooted
    exact subterm_rows root term (good root present) inside

def AllSimpleRows (pool : Pool m) : Prop :=
  ∀ slot, simpleTyRows (pool.termAt slot) = true

theorem problem_pool_rows (problem : Problem m)
    (good : ∀ edge ∈ problem.types,
      simpleTyRows edge.1 = true ∧ simpleTyRows edge.2 = true) :
    AllSimpleRows problem.pool := by
  intro slot
  apply collected_rows problem.roots _ _ (problem.pool.at_mem slot)
  intro term member
  obtain ⟨edge, present, contains⟩ := List.mem_flatMap.mp member
  rcases List.mem_cons.mp contains with rfl | remaining
  · exact (good edge present).1
  · have same := List.mem_singleton.mp remaining
    subst term
    exact (good edge present).2

theorem compiled_pool_rows (atoms : List (Atom (Fin m))) (good : GoodAtoms atoms) :
    AllSimpleRows (splitAtoms atoms).pool := by
  apply problem_pool_rows
  intro edge member
  exact good (.tyLe edge.1 edge.2)
    ((CommonGeneratedRigidPool.split_type_member atoms edge.1 edge.2).mp member)

/-- Both polarities of an arrow comparison read simple rows from the same
original IDs. No property of assigned concrete rows is assumed. -/
theorem arrow_rows (pool : Pool m) (good : AllSimpleRows pool) (slot : Fin pool.size)
    (input output : TyTerm (Fin m)) (incoming outgoing : RowTerm (Fin m))
    (shape : pool.termAt slot = .arrow input incoming output outgoing) :
    simpleRow incoming = true ∧ simpleRow outgoing = true := by
  have all := good slot
  rw [shape] at all
  have parts : ((simpleTyRows input = true ∧ simpleRow incoming = true) ∧
      simpleTyRows output = true) ∧ simpleRow outgoing = true := by
    simpa only [simpleTyRows, Bool.and_eq_true] using all
  exact ⟨parts.1.1.2, parts.2⟩

/-- Every clause of every source expression supplies this invariant
internally; there is no support, success, model, fuel or cache premise. -/
theorem generated_pool_rows (expression : Inference.Expr) (clause : Clause (Option Empty))
    (member : clause ∈ normalise
      (Core.PresenceGeneration.principal ([] : Core.PresenceGeneration.SchemeEnv Empty) expression)) :
    AllSimpleRows (splitAtoms clause.pack).pool :=
  compiled_pool_rows clause.pack
    (PresenceSourceConstraintSupport.generated_row_shapes expression clause member)

theorem generated_core_pool_rows (expression : Core.Required.Term) (clause : Clause (Option Empty))
    (member : clause ∈ normalise
      (Core.PresenceGeneration.CoreRules.principalCore
        ([] : Core.PresenceGeneration.SchemeEnv Empty) expression)) :
    AllSimpleRows (splitAtoms clause.pack).pool :=
  compiled_pool_rows clause.pack
    (CommonPresenceSourceFamily.generated_core_row_shapes expression clause member)

end Yulang.CommonGeneratedPoolRows
