import Yulang.CommonGeneratedBoundWidth
import Yulang.CommonPresenceClampedBounds
import Yulang.CommonGeneratedRigidInspection

/-!
# Generated record widths for every clamped parameter assignment

Every generated record tail and whole-default source has a paired width
edge. Its recursive upper grammar has only six possible heads. Variable
heads satisfy that edge through the unconditional clamp bound. Width and
required heads satisfy it through their constructor equation. Base, pair and
arrow heads make the first finite symbolic discharge return no branch.

Consequently each branch actually retained by that discharge has the pool
width invariant for every independent row, type and recursive parameter
assignment. No interpretation of the retained branch and no satisfaction of
the original edge list is assumed. This only discharges the width premise;
it does not assert that all other retained constraints have been solved.
-/

namespace Yulang.CommonGeneratedClampedWidth

open Common (Ty Row Subtype)
open Core.PresenceGeneration (TyTerm RowTerm)
open PresenceNormalForm (Atom Clause normalise)
open PresenceOpenTailGenerationLowering (Pool Problem subterms)
open CommonPresenceConstraintGraph (splitAtoms compile Realizes lowerNode)
open CommonPresenceVariableBounds (inputAt classify template)
open CommonPresenceClampedBounds (solve)
open CommonGeneratedRigidInspection (inspect inspectSlot saturate)
open CommonSymbolicConstraints (Check Branch discharge)
open PresenceGeneratedChildGrammar (upper lower GoodAtoms)
open PresenceGeneratedWidth (widthTail WidthAtoms)
open CommonGeneratedWidth (PoolWidth)

variable {m : Nat}

theorem discharge_empty_of_false {Rows Node Child : Type}
    (checks : Branch Rows Node Child) (member : .flag (.literal false) ∈ checks) :
    discharge checks = [] := by
  induction checks with
  | nil => cases member
  | cons check rest ih =>
      rcases List.mem_cons.mp member with same | inside
      · subst check
        rfl
      · cases check with
        | childBelow | rowBelow | profileBelow => simp only [discharge, ih inside, List.map_nil]
        | flag expression =>
            cases expression with
            | literal value => cases value <;> simp only [discharge, ih inside]
            | atom | and | or | not => simp only [discharge, ih inside, List.map_nil]

theorem rigid_edge_retained (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (source target : Fin pool.size) (member : (source, target) ∈ edges)
    (first : inputAt pool source = none) (last : inputAt pool target = none) :
    (source, target) ∈ CommonBoundCoalescing.rigidComparisons (template pool edges) := by
  apply List.mem_flatMap.mpr
  refine ⟨.check source target, ?_, by simp⟩
  apply List.mem_map.mpr
  exact ⟨(source, target), member, by simp only [classify, first, last]⟩

theorem variable_width_bound (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (index : Fin m) (widthMember : TyTerm.emptyRecord ∈ pool.terms)
    (member : (pool.input index, pool.reference .emptyRecord widthMember) ∈ edges) :
    pool.reference .emptyRecord widthMember ∈
      LayerBoundTemplates.upperBounds (template pool edges) index := by
  apply (PresenceBoundCoalescing.mem_upperBounds _ _ _).mpr
  refine ⟨index, ?_, .nil index⟩
  apply List.mem_map.mpr
  refine ⟨(pool.input index, pool.reference .emptyRecord widthMember), member, ?_⟩
  simp only [classify, inputAt, Pool.input, Pool.termAt_reference]

theorem static_width_failure (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (source : TyTerm (Fin m)) (sourceMember : source ∈ pool.terms)
    (widthMember : TyTerm.emptyRecord ∈ pool.terms)
    (edge : (pool.reference source sourceMember, pool.reference .emptyRecord widthMember) ∈ edges)
    (rigid : inputAt pool (pool.reference source sourceMember) = none)
    (failed : inspect pool source .emptyRecord sourceMember widthMember = [.flag (.literal false)]) :
    saturate pool (CommonBoundCoalescing.rigidComparisons (template pool edges)) = [] := by
  apply discharge_empty_of_false
  apply List.mem_flatMap.mpr
  refine ⟨(pool.reference source sourceMember, pool.reference .emptyRecord widthMember),
    rigid_edge_retained pool edges _ _ edge rigid
      (by simp only [inputAt, Pool.termAt_reference]), ?_⟩
  simp only [inspectSlot, Pool.termAt_reference, failed, List.mem_singleton]

theorem widthTail_upper (source tail : TyTerm (Fin m)) (shape : lower source = true)
    (needed : widthTail source = some tail) : upper tail = true := by
  cases source with
  | record _ head rest =>
      have same : rest = tail := Option.some.inj needed
      subst tail
      exact (Bool.and_eq_true_iff.mp shape).2
  | recordDefault _ original fallback =>
      have same : original = tail := Option.some.inj needed
      subst tail
      exact (Bool.and_eq_true_iff.mp shape).1
  | _ => cases needed

/-- A single width seed, for every assignment of all three parameter
families. The only branch premise is membership in a finite syntax-only
computation, not that any check in the branch holds. -/
theorem all_parameters_width_seed (pool : Pool m)
    (edges : List (Fin pool.size × Fin pool.size))
    (source : TyTerm (Fin m)) (sourceMember : source ∈ pool.terms)
    (shape : upper source = true) (widthMember : TyTerm.emptyRecord ∈ pool.terms)
    (edge : (pool.reference source sourceMember, pool.reference .emptyRecord widthMember) ∈ edges)
    (branch : Branch (RowTerm (Fin m)) (Fin pool.size) (Fin pool.size))
    (survives : branch ∈ saturate pool (CommonBoundCoalescing.rigidComparisons (template pool edges)))
    (rows : Fin m → Row) (parameters : Fin m → Ty) (recursiveParameters : Fin pool.size → Ty) :
    Subtype (solve pool edges rows parameters recursiveParameters (pool.reference source sourceMember))
      Common.emptyRecord := by
  have realizes := CommonPresenceClampedBounds.solve_realizes pool edges rows parameters recursiveParameters
  have widthSame := CommonPresenceConstraintGraph.realizes_reference pool rows _ realizes
    .emptyRecord widthMember
  have widthBelow : Subtype
      (solve pool edges rows parameters recursiveParameters (pool.reference .emptyRecord widthMember))
      Common.emptyRecord := widthSame.2
  cases source with
  | var index =>
      exact Common.subtype_trans
        (CommonPresenceClampedBounds.all_parameters_below_bound pool edges rows parameters recursiveParameters
          index _ (variable_width_bound pool edges index widthMember edge)) widthBelow
  | emptyRecord => exact widthBelow
  | required label payload =>
      have same := CommonPresenceConstraintGraph.realizes_reference pool rows _ realizes
        (.required label payload) sourceMember
      apply Common.subtype_trans same.2
      apply (CommonRecordTargetProfiles.subtype_emptyRecord_iff _).mpr
      rfl
  | base scalar | pair first last | arrow first incoming last outgoing =>
      have failed := static_width_failure pool edges _ sourceMember widthMember edge
        (by simp only [inputAt, Pool.termAt_reference]) rfl
      rw [failed] at survives
      cases survives
  | _ => cases shape

theorem compiled_edge_member (atoms : List (Atom (Fin m))) (source target : TyTerm (Fin m))
    (member : .tyLe source target ∈ atoms)
    (sourceMember : source ∈ (splitAtoms atoms).pool.terms)
    (targetMember : target ∈ (splitAtoms atoms).pool.terms) :
    ((splitAtoms atoms).pool.reference source sourceMember,
      (splitAtoms atoms).pool.reference target targetMember) ∈ (compile atoms).edges := by
  have original := (CommonGeneratedRigidPool.split_type_member atoms source target).mpr member
  exact List.mem_map.mpr ⟨⟨(source, target), original⟩, by simp, rfl⟩

theorem compiled_all_parameters_pool_width (atoms : List (Atom (Fin m)))
    (good : GoodAtoms atoms) (widths : WidthAtoms atoms)
    (branch : Branch (RowTerm (Fin m)) (Fin (splitAtoms atoms).pool.size) (Fin (splitAtoms atoms).pool.size))
    (survives : branch ∈ saturate (splitAtoms atoms).pool
      (CommonBoundCoalescing.rigidComparisons (template (splitAtoms atoms).pool (compile atoms).edges)))
    (rows : Fin m → Row) (parameters : Fin m → Ty)
    (recursiveParameters : Fin (splitAtoms atoms).pool.size → Ty) :
    PoolWidth (splitAtoms atoms).pool
      (solve (splitAtoms atoms).pool (compile atoms).edges rows parameters recursiveParameters) := by
  intro term member tail needed tailMember
  have notUpper : ¬ upper term = true := by
    intro accepted
    rw [PresenceGeneratedWidth.upper_no_width term accepted] at needed
    cases needed
  obtain ⟨target, original⟩ := CommonGeneratedWidth.pool_lower_origin atoms good term member notUpper
  have tailShape := widthTail_upper term tail (good (.tyLe term target) original).1 needed
  have atom := widths term target original tail needed
  have edge := (CommonGeneratedRigidPool.split_type_member atoms tail .emptyRecord).mpr atom
  have widthMember := ((splitAtoms atoms).covers (tail, .emptyRecord) edge).2
  exact all_parameters_width_seed (splitAtoms atoms).pool (compile atoms).edges tail tailMember
    tailShape widthMember (compiled_edge_member atoms tail .emptyRecord atom tailMember widthMember)
    branch survives rows parameters recursiveParameters

/-- Every actual source clause, every statically retained original rigid
branch, and every row/type/recursive parameter assignment. No original edge
model or semantic satisfaction of the retained branch is required. -/
theorem generated_all_parameters_pool_width (expression : Inference.Expr)
    (clause : Clause (Option Empty))
    (generated : clause ∈ normalise (Core.PresenceGeneration.principal
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (branch : Branch (RowTerm (Fin (clause.locals + 1)))
      (Fin (splitAtoms clause.pack).pool.size) (Fin (splitAtoms clause.pack).pool.size))
    (survives : branch ∈ saturate (splitAtoms clause.pack).pool
      (CommonBoundCoalescing.rigidComparisons
        (template (splitAtoms clause.pack).pool (compile clause.pack).edges)))
    (rows : Fin (clause.locals + 1) → Row) (parameters : Fin (clause.locals + 1) → Ty)
    (recursiveParameters : Fin (splitAtoms clause.pack).pool.size → Ty) :
    PoolWidth (splitAtoms clause.pack).pool
      (solve (splitAtoms clause.pack).pool (compile clause.pack).edges rows parameters recursiveParameters) :=
  compiled_all_parameters_pool_width clause.pack
    (PresenceGeneratedChildGrammar.generated_child_grammar expression clause generated)
    (PresenceGeneratedWidth.generated_width_atoms expression clause generated)
    branch survives rows parameters recursiveParameters

theorem generated_core_all_parameters_pool_width (expression : Core.Required.Term)
    (clause : Clause (Option Empty))
    (generated : clause ∈ normalise (Core.PresenceGeneration.CoreRules.principalCore
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (branch : Branch (RowTerm (Fin (clause.locals + 1)))
      (Fin (splitAtoms clause.pack).pool.size) (Fin (splitAtoms clause.pack).pool.size))
    (survives : branch ∈ saturate (splitAtoms clause.pack).pool
      (CommonBoundCoalescing.rigidComparisons
        (template (splitAtoms clause.pack).pool (compile clause.pack).edges)))
    (rows : Fin (clause.locals + 1) → Row) (parameters : Fin (clause.locals + 1) → Ty)
    (recursiveParameters : Fin (splitAtoms clause.pack).pool.size → Ty) :
    PoolWidth (splitAtoms clause.pack).pool
      (solve (splitAtoms clause.pack).pool (compile clause.pack).edges rows parameters recursiveParameters) :=
  compiled_all_parameters_pool_width clause.pack
    (PresenceGeneratedChildGrammar.generated_core_child_grammar expression clause generated)
    (PresenceGeneratedWidth.generated_core_width_atoms expression clause generated)
    branch survives rows parameters recursiveParameters

end Yulang.CommonGeneratedClampedWidth
