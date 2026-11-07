import Yulang.CommonOptionalPoolWidth
import Yulang.CommonGeneratedClampedWidth

/-!
# Transport of generated width seeds to an extended clamped pool

Only original width seeds need to be retained by the extension. Width
recovery uses constructor equations, unconditional variable upper bounds,
and the absence of a literal false check among rigid comparisons whose
target is width. It does not require semantic validity of any residual
branch, nor does it inspect optional targets with the old dispatcher.

A surviving branch of the old static discharge implies the local absence
condition. That sufficient corollary is deliberately separate: optional
targets require their dedicated inspector, and the corollary is not a
claim that the old discharge supports the extended grammar.
-/

namespace Yulang.CommonOptionalPoolClampedWidth

open Common (Ty Row Subtype)
open Core.PresenceGeneration (TyTerm RowTerm)
open PresenceNormalForm (Atom Clause normalise)
open PresenceOpenTailGenerationLowering (Pool)
open CommonPresenceConstraintGraph (Realizes splitAtoms compile)
open CommonPresenceVariableBounds (inputAt template)
open CommonPresenceClampedBounds (solve)
open CommonGeneratedRigidInspection (inspectSlot saturate)
open CommonGeneratedClampedWidth
open CommonSymbolicConstraints (Branch)
open PresenceGeneratedChildGrammar (upper GoodAtoms)
open PresenceGeneratedWidth (widthTail WidthAtoms)
open CommonGeneratedWidth (PoolWidth)
open CommonOptionalPool (Query extend embed restrictValues original_member)
open CommonOptionalPoolWidth (embed_reference pool_width_iff)

variable {m : Nat}

/-- A finite syntactic condition only on width-target rigid comparisons. -/
def WidthChecksClear (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size)) : Prop :=
  ∀ edge ∈ CommonBoundCoalescing.rigidComparisons (template pool edges),
    pool.termAt edge.2 = .emptyRecord → .flag (.literal false) ∉ inspectSlot pool edge

theorem widthChecksClear_of_survives (pool : Pool m)
    (edges : List (Fin pool.size × Fin pool.size))
    (branch : Branch (RowTerm (Fin m)) (Fin pool.size) (Fin pool.size))
    (survives : branch ∈ saturate pool (CommonBoundCoalescing.rigidComparisons (template pool edges))) :
    WidthChecksClear pool edges := by
  intro edge member _ failed
  have absent := discharge_empty_of_false
    ((CommonBoundCoalescing.rigidComparisons (template pool edges)).flatMap (inspectSlot pool))
    (List.mem_flatMap.mpr ⟨edge, member, failed⟩)
  change branch ∈ CommonSymbolicConstraints.discharge _ at survives
  rw [absent] at survives
  cases survives

/-- General width recovery, without any solver or whole-edge model premise.
Rows and node values are arbitrary. Only constructor equations, propagated
variable upper bounds and static width checks are required. -/
theorem width_seed_of_upper_bounds (pool : Pool m)
    (edges : List (Fin pool.size × Fin pool.size)) (rows : Fin m → Row)
    (values : Fin pool.size → Ty) (realizes : Realizes pool rows values)
    (uppers : ∀ source bound, bound ∈ LayerBoundTemplates.upperBounds (template pool edges) source →
      Subtype (values (pool.input source)) (values bound))
    (clear : WidthChecksClear pool edges)
    (source : TyTerm (Fin m)) (sourceMember : source ∈ pool.terms)
    (shape : upper source = true) (widthMember : TyTerm.emptyRecord ∈ pool.terms)
    (edge : (pool.reference source sourceMember, pool.reference .emptyRecord widthMember) ∈ edges) :
    Subtype (values (pool.reference source sourceMember)) Common.emptyRecord := by
  have widthSame := CommonPresenceConstraintGraph.realizes_reference pool rows values realizes
    .emptyRecord widthMember
  have widthBelow : Subtype (values (pool.reference .emptyRecord widthMember)) Common.emptyRecord := widthSame.2
  cases source with
  | var index =>
      exact Common.subtype_trans
        (uppers index _ (variable_width_bound pool edges index widthMember edge)) widthBelow
  | emptyRecord => exact widthBelow
  | required label payload =>
      have same := CommonPresenceConstraintGraph.realizes_reference pool rows values realizes
        (.required label payload) sourceMember
      apply Common.subtype_trans same.2
      exact (CommonRecordTargetProfiles.subtype_emptyRecord_iff _).mpr rfl
  | base scalar | pair first last | arrow first incoming last outgoing =>
      have retained := rigid_edge_retained pool edges _ _ edge
        (by simp only [inputAt, Pool.termAt_reference])
        (by simp only [inputAt, Pool.termAt_reference])
      apply False.elim
      apply clear _ retained (by simp only [Pool.termAt_reference])
      simp only [inspectSlot, Pool.termAt_reference]
      exact List.mem_cons_self
  | _ => cases shape

theorem all_parameters_width_seed_of_clear (pool : Pool m)
    (edges : List (Fin pool.size × Fin pool.size)) (clear : WidthChecksClear pool edges)
    (source : TyTerm (Fin m)) (sourceMember : source ∈ pool.terms)
    (shape : upper source = true) (widthMember : TyTerm.emptyRecord ∈ pool.terms)
    (edge : (pool.reference source sourceMember, pool.reference .emptyRecord widthMember) ∈ edges)
    (rows : Fin m → Row) (parameters : Fin m → Ty) (recursiveParameters : Fin pool.size → Ty) :
    Subtype (solve pool edges rows parameters recursiveParameters (pool.reference source sourceMember))
      Common.emptyRecord :=
  width_seed_of_upper_bounds pool edges rows _
    (CommonPresenceClampedBounds.solve_realizes pool edges rows parameters recursiveParameters)
    (CommonPresenceClampedBounds.all_parameters_below_bound pool edges rows parameters recursiveParameters)
    clear source sourceMember shape widthMember edge

/-- Only edges whose original target is width need to be transported. -/
def WidthSeedsIncluded (pool : Pool m) (queries : List (Query pool))
    (originalEdges : List (Fin pool.size × Fin pool.size))
    (extendedEdges : List (Fin (extend pool queries).size × Fin (extend pool queries).size)) : Prop :=
  ∀ first last, (first, last) ∈ originalEdges → pool.termAt last = .emptyRecord →
    (embed pool queries first, embed pool queries last) ∈ extendedEdges

theorem widthSeedsIncluded_of_edges (pool : Pool m) (queries : List (Query pool))
    (originalEdges : List (Fin pool.size × Fin pool.size))
    (extendedEdges : List (Fin (extend pool queries).size × Fin (extend pool queries).size))
    (included : ∀ edge ∈ originalEdges,
      (embed pool queries edge.1, embed pool queries edge.2) ∈ extendedEdges) :
    WidthSeedsIncluded pool queries originalEdges extendedEdges :=
  fun first last member _ => included (first, last) member

/-- The extension may add arbitrary edges. The original paired width seeds
and the finite width-only static check suffice for every extended parameter. -/
theorem compiled_all_parameters_pool_width (atoms : List (Atom (Fin m)))
    (good : GoodAtoms atoms) (widths : WidthAtoms atoms)
    (queries : List (Query (splitAtoms atoms).pool))
    (edges : List (Fin (extend (splitAtoms atoms).pool queries).size ×
      Fin (extend (splitAtoms atoms).pool queries).size))
    (included : WidthSeedsIncluded (splitAtoms atoms).pool queries (compile atoms).edges edges)
    (clear : WidthChecksClear (extend (splitAtoms atoms).pool queries) edges)
    (rows : Fin m → Row) (parameters : Fin m → Ty)
    (recursiveParameters : Fin (extend (splitAtoms atoms).pool queries).size → Ty) :
    PoolWidth (extend (splitAtoms atoms).pool queries)
      (solve (extend (splitAtoms atoms).pool queries) edges rows parameters recursiveParameters) := by
  apply (pool_width_iff _ _ _).mpr
  intro term member tail needed tailMember
  have notUpper : ¬ upper term = true := by
    intro accepted
    rw [PresenceGeneratedWidth.upper_no_width term accepted] at needed
    cases needed
  obtain ⟨target, original⟩ := CommonGeneratedWidth.pool_lower_origin atoms good term member notUpper
  have tailShape := widthTail_upper term tail (good (.tyLe term target) original).1 needed
  have atom := widths term target original tail needed
  have originalEdge := (CommonGeneratedRigidPool.split_type_member atoms tail .emptyRecord).mpr atom
  have widthMember := ((splitAtoms atoms).covers (tail, .emptyRecord) originalEdge).2
  have seed := compiled_edge_member atoms tail .emptyRecord atom tailMember widthMember
  have transported := included _ _ seed (by simp only [Pool.termAt_reference])
  simp only [embed_reference] at transported
  simpa only [restrictValues, Function.comp_def, embed_reference] using
    all_parameters_width_seed_of_clear (extend (splitAtoms atoms).pool queries) edges clear
      tail (original_member _ queries tail tailMember) tailShape
      (original_member _ queries .emptyRecord widthMember) transported rows parameters recursiveParameters

/-- Arbitrary actual generated source clause and finite query inventory.
All row, type and extended recursive parameters remain unrestricted. -/
theorem generated_all_parameters_pool_width (expression : Inference.Expr)
    (clause : Clause (Option Empty))
    (generated : clause ∈ normalise (Core.PresenceGeneration.principal
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (queries : List (Query (splitAtoms clause.pack).pool))
    (edges : List (Fin (extend (splitAtoms clause.pack).pool queries).size ×
      Fin (extend (splitAtoms clause.pack).pool queries).size))
    (included : WidthSeedsIncluded (splitAtoms clause.pack).pool queries (compile clause.pack).edges edges)
    (clear : WidthChecksClear (extend (splitAtoms clause.pack).pool queries) edges)
    (rows : Fin (clause.locals + 1) → Row) (parameters : Fin (clause.locals + 1) → Ty)
    (recursiveParameters : Fin (extend (splitAtoms clause.pack).pool queries).size → Ty) :
    PoolWidth (extend (splitAtoms clause.pack).pool queries)
      (solve (extend (splitAtoms clause.pack).pool queries) edges rows parameters recursiveParameters) :=
  compiled_all_parameters_pool_width clause.pack
    (PresenceGeneratedChildGrammar.generated_child_grammar expression clause generated)
    (PresenceGeneratedWidth.generated_width_atoms expression clause generated)
    queries edges included clear rows parameters recursiveParameters

theorem generated_core_all_parameters_pool_width (expression : Core.Required.Term)
    (clause : Clause (Option Empty))
    (generated : clause ∈ normalise (Core.PresenceGeneration.CoreRules.principalCore
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (queries : List (Query (splitAtoms clause.pack).pool))
    (edges : List (Fin (extend (splitAtoms clause.pack).pool queries).size ×
      Fin (extend (splitAtoms clause.pack).pool queries).size))
    (included : WidthSeedsIncluded (splitAtoms clause.pack).pool queries (compile clause.pack).edges edges)
    (clear : WidthChecksClear (extend (splitAtoms clause.pack).pool queries) edges)
    (rows : Fin (clause.locals + 1) → Row) (parameters : Fin (clause.locals + 1) → Ty)
    (recursiveParameters : Fin (extend (splitAtoms clause.pack).pool queries).size → Ty) :
    PoolWidth (extend (splitAtoms clause.pack).pool queries)
      (solve (extend (splitAtoms clause.pack).pool queries) edges rows parameters recursiveParameters) :=
  compiled_all_parameters_pool_width clause.pack
    (PresenceGeneratedChildGrammar.generated_core_child_grammar expression clause generated)
    (PresenceGeneratedWidth.generated_core_width_atoms expression clause generated)
    queries edges included clear rows parameters recursiveParameters

end Yulang.CommonOptionalPoolClampedWidth
