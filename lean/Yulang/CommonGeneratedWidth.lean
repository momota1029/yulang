import Yulang.PresenceGeneratedWidth
import Yulang.CommonGeneratedRigidPool

/-!
# Generated width constraints for every shared record/default node

The recursive upper grammar contains no record construction or whole
default. Consequently each such node in the actual collected pool is an
original lower root, rather than an unaccounted-for nested subterm. Its paired
width atom is present in the same packed clause.

The semantic corollaries quantify over arbitrary independent row/node
assignments realizing the original graph and satisfying its edges. They
recover width for the shared tail/source node itself, not merely for a
canonical evaluation or an output selected by a solver.
-/

namespace Yulang.CommonGeneratedWidth

open Core.PresenceGeneration (TyTerm)
open PresenceNormalForm (Atom Clause normalise)
open PresenceOpenTailGenerationLowering (Pool Problem subterms collect)
open CommonPresenceConstraintGraph (splitAtoms compile Realizes EdgesHold)
open PresenceGeneratedChildGrammar (upper lower GoodAtoms)
open PresenceGeneratedWidth (widthTail WidthAtoms)
open Common (Ty Row Subtype)

variable {m : Nat}

theorem upper_subterm (source part : TyTerm (Fin m)) (good : upper source = true)
    (member : part ∈ subterms source) : upper part = true := by
  induction source with
  | var | base | emptyRecord =>
      have same := List.mem_singleton.mp member
      subst part
      exact good
  | pair first last before after | arrow first _ last _ before after =>
      rcases List.mem_cons.mp member with same | inside
      · subst part
        exact good
      · have both := Bool.and_eq_true_iff.mp good
        exact (List.mem_append.mp inside).elim (before both.1) (after both.2)
  | required _ payload ih =>
      rcases List.mem_cons.mp member with same | inside
      · subst part
        exact good
      · exact ih good inside
  | _ => cases good

theorem lower_subterm (source part : TyTerm (Fin m)) (good : lower source = true)
    (member : part ∈ subterms source) : part = source ∨ upper part = true := by
  cases source with
  | var | base | bottom | top | emptyRecord | exactEmpty =>
      exact Or.inl (List.mem_singleton.mp member)
  | union first last | pair first last | arrow first _ last _
  | record _ first last | recordDefault _ first last =>
      rcases List.mem_cons.mp member with same | inside
      · exact Or.inl same
      · apply Or.inr
        have both := Bool.and_eq_true_iff.mp good
        exact (List.mem_append.mp inside).elim
          (upper_subterm first part both.1) (upper_subterm last part both.2)
  | required _ payload | variant _ payload =>
      rcases List.mem_cons.mp member with same | inside
      · exact Or.inl same
      · exact Or.inr (upper_subterm payload part good inside)
  | inter => cases good

/-- Any collected node outside the recursive upper grammar must be an
original lower endpoint. The collector's extra variable nodes are included. -/
theorem pool_lower_origin (atoms : List (Atom (Fin m))) (good : GoodAtoms atoms)
    (term : TyTerm (Fin m)) (member : term ∈ (splitAtoms atoms).pool.terms)
    (notUpper : ¬ upper term = true) : ∃ target, .tyLe term target ∈ atoms := by
  change term ∈ TypeConstraintGraph.unique
    ((List.ofFn fun index : Fin m => TyTerm.var index) ++ (splitAtoms atoms).roots.flatMap subterms) at member
  rcases List.mem_append.mp ((TypeConstraintGraph.mem_unique _ _).mp member) with fromVariables | collected
  · obtain ⟨index, rfl⟩ := List.mem_ofFn.mp fromVariables
    exact False.elim (notUpper rfl)
  · obtain ⟨root, rootMember, inside⟩ := List.mem_flatMap.mp collected
    obtain ⟨edge, edgeMember, side⟩ := List.mem_flatMap.mp rootMember
    have original := (CommonGeneratedRigidPool.split_type_member atoms edge.1 edge.2).mp edgeMember
    have grammar := good (.tyLe edge.1 edge.2) original
    simp only [List.mem_cons, List.not_mem_nil, or_false] at side
    rcases side with rfl | rfl
    · rcases lower_subterm edge.1 term grammar.1 inside with same | upper
      · subst term
        exact ⟨edge.2, original⟩
      · exact False.elim (notUpper upper)
    · exact False.elim (notUpper (upper_subterm edge.2 term grammar.2 inside))

theorem pool_width_atom (atoms : List (Atom (Fin m))) (good : GoodAtoms atoms)
    (widths : WidthAtoms atoms) (term : TyTerm (Fin m))
    (member : term ∈ (splitAtoms atoms).pool.terms) (tail : TyTerm (Fin m))
    (needed : widthTail term = some tail) : .tyLe tail .emptyRecord ∈ atoms := by
  have notUpper : ¬ upper term = true := by
    intro accepted
    rw [PresenceGeneratedWidth.upper_no_width term accepted] at needed
    cases needed
  obtain ⟨target, included⟩ := pool_lower_origin atoms good term member notUpper
  exact widths term target included tail needed

theorem generated_pool_width_atom (expression : Inference.Expr) (clause : Clause (Option Empty))
    (generated : clause ∈ normalise (Core.PresenceGeneration.principal
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (term : TyTerm (Fin (clause.locals + 1))) (member : term ∈ (splitAtoms clause.pack).pool.terms)
    (tail : TyTerm (Fin (clause.locals + 1))) (needed : widthTail term = some tail) :
    .tyLe tail .emptyRecord ∈ clause.pack :=
  pool_width_atom clause.pack
    (PresenceGeneratedChildGrammar.generated_child_grammar expression clause generated)
    (PresenceGeneratedWidth.generated_width_atoms expression clause generated) term member tail needed

theorem generated_core_pool_width_atom (expression : Core.Required.Term) (clause : Clause (Option Empty))
    (generated : clause ∈ normalise (Core.PresenceGeneration.CoreRules.principalCore
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (term : TyTerm (Fin (clause.locals + 1))) (member : term ∈ (splitAtoms clause.pack).pool.terms)
    (tail : TyTerm (Fin (clause.locals + 1))) (needed : widthTail term = some tail) :
    .tyLe tail .emptyRecord ∈ clause.pack :=
  pool_width_atom clause.pack
    (PresenceGeneratedChildGrammar.generated_core_child_grammar expression clause generated)
    (PresenceGeneratedWidth.generated_core_width_atoms expression clause generated) term member tail needed

def PoolWidth (pool : Pool m) (values : Fin pool.size → Ty) : Prop :=
  ∀ term, term ∈ pool.terms → ∀ tail, widthTail term = some tail →
    ∀ member : tail ∈ pool.terms, Subtype (values (pool.reference tail member)) Common.emptyRecord

theorem PoolWidth.record {pool : Pool m} {values : Fin pool.size → Ty} (widths : PoolWidth pool values)
    (label : Nat) (head tail : TyTerm (Fin m)) (member : TyTerm.record label head tail ∈ pool.terms) :
    Subtype (values (pool.child (.record label head tail) member tail (by simp [subterms])))
      Common.emptyRecord :=
  widths _ member tail rfl (pool.closed _ member tail (by simp [subterms]))

theorem PoolWidth.recordDefault {pool : Pool m} {values : Fin pool.size → Ty} (widths : PoolWidth pool values)
    (label : Nat) (source fallback : TyTerm (Fin m))
    (member : TyTerm.recordDefault label source fallback ∈ pool.terms) :
    Subtype (values (pool.child (.recordDefault label source fallback) member source (by simp [subterms])))
      Common.emptyRecord :=
  widths _ member source rfl (pool.closed _ member source (by simp [subterms]))

theorem compiled_pool_width (atoms : List (Atom (Fin m))) (good : GoodAtoms atoms)
    (widths : WidthAtoms atoms) (rows : Fin m → Row)
    (values : Fin (splitAtoms atoms).pool.size → Ty)
    (realizes : Realizes (splitAtoms atoms).pool rows values)
    (edges : EdgesHold (compile atoms).edges values) : PoolWidth (splitAtoms atoms).pool values := by
  intro term member tail needed included
  have atom := pool_width_atom atoms good widths term member tail needed
  have edge := (CommonGeneratedRigidPool.split_type_member atoms tail .emptyRecord).mpr atom
  have original := (CommonPresenceConstraintGraph.compiled_edges_exact
    (splitAtoms atoms) rows values realizes).mp edges
  have same := CommonPresenceConstraintGraph.realizes_evaluate
    (splitAtoms atoms).pool rows values realizes tail included
  exact Common.subtype_trans same.1 (original (tail, .emptyRecord) edge)

/-- Every actual source clause and every independent original graph model.
The width condition is derived from generated atoms, not supplied separately. -/
theorem generated_pool_width (expression : Inference.Expr) (clause : Clause (Option Empty))
    (member : clause ∈ normalise (Core.PresenceGeneration.principal
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (rows : Fin (clause.locals + 1) → Row)
    (values : Fin (splitAtoms clause.pack).pool.size → Ty)
    (realizes : Realizes (splitAtoms clause.pack).pool rows values)
    (edges : EdgesHold (compile clause.pack).edges values) : PoolWidth (splitAtoms clause.pack).pool values :=
  compiled_pool_width clause.pack
    (PresenceGeneratedChildGrammar.generated_child_grammar expression clause member)
    (PresenceGeneratedWidth.generated_width_atoms expression clause member) rows values realizes edges

theorem generated_core_pool_width (expression : Core.Required.Term) (clause : Clause (Option Empty))
    (member : clause ∈ normalise (Core.PresenceGeneration.CoreRules.principalCore
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (rows : Fin (clause.locals + 1) → Row)
    (values : Fin (splitAtoms clause.pack).pool.size → Ty)
    (realizes : Realizes (splitAtoms clause.pack).pool rows values)
    (edges : EdgesHold (compile clause.pack).edges values) : PoolWidth (splitAtoms clause.pack).pool values :=
  compiled_pool_width clause.pack
    (PresenceGeneratedChildGrammar.generated_core_child_grammar expression clause member)
    (PresenceGeneratedWidth.generated_core_width_atoms expression clause member) rows values realizes edges

theorem generated_models_pool_width (expression : Inference.Expr) (clause : Clause (Option Empty))
    (member : clause ∈ normalise (Core.PresenceGeneration.principal
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (rows : Fin (clause.locals + 1) → Row)
    (values : Fin (compile clause.pack).size → Ty) (models : (compile clause.pack).Models rows values) :
    PoolWidth (splitAtoms clause.pack).pool values :=
  generated_pool_width expression clause member rows values models.1 models.2.1

theorem generated_core_models_pool_width (expression : Core.Required.Term) (clause : Clause (Option Empty))
    (member : clause ∈ normalise (Core.PresenceGeneration.CoreRules.principalCore
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (rows : Fin (clause.locals + 1) → Row)
    (values : Fin (compile clause.pack).size → Ty) (models : (compile clause.pack).Models rows values) :
    PoolWidth (splitAtoms clause.pack).pool values :=
  generated_core_pool_width expression clause member rows values models.1 models.2.1

end Yulang.CommonGeneratedWidth
