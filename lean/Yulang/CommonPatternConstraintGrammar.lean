import Yulang.CommonPatternBoundWorklist
import Yulang.CommonGeneratedWidth

/-! Compiled syntax provenance and the record-width invariant for pattern
upper bounds. Assigned Common types and rows remain unrestricted. -/

namespace Yulang.CommonPatternConstraintGrammar

open Core.PresenceGeneration (TyTerm)
open PresenceNormalForm (Atom)
open PresenceOpenTailGenerationLowering (Pool subterms)
open CommonPresenceConstraintGraph (splitAtoms compile Realizes EdgesHold)
open PresenceGeneratedChildGrammar (upper lower)
open PresenceGeneratedWidth (widthTail WidthAtoms)
open CommonPatternBoundInspection (Upper)
open CommonBoundRefWorklist (originalEdges edgeHolds auxHolds)

variable {m : Nat}

def GoodAtoms (atoms : List (Atom α)) : Prop :=
  ∀ source target, .tyLe source target ∈ atoms → lower source = true ∧ Upper target

theorem upper_no_width_subterm (source part : TyTerm (Fin m)) (good : Upper source)
    (member : part ∈ subterms source) : widthTail part = none := by
  cases good with
  | old good =>
      exact PresenceGeneratedWidth.upper_no_width part
        (CommonGeneratedWidth.upper_subterm source part good member)
  | variant good =>
      rcases List.mem_cons.mp member with same | inside
      · subst part; rfl
      · exact PresenceGeneratedWidth.upper_no_width part
          (CommonGeneratedWidth.upper_subterm _ part good inside)
  | optional good =>
      simp only [subterms, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | inside
      · rfl
      · rfl
      · rfl
      · exact PresenceGeneratedWidth.upper_no_width part
          (CommonGeneratedWidth.upper_subterm _ part good inside)

theorem pool_width_origin (atoms : List (Atom (Fin m))) (good : GoodAtoms atoms)
    (term : TyTerm (Fin m)) (member : term ∈ (splitAtoms atoms).pool.terms)
    (tail : TyTerm (Fin m)) (needed : widthTail term = some tail) :
    ∃ target, .tyLe term target ∈ atoms := by
  change term ∈ TypeConstraintGraph.unique
    ((List.ofFn fun index : Fin m => TyTerm.var index) ++ (splitAtoms atoms).roots.flatMap subterms) at member
  rcases List.mem_append.mp ((TypeConstraintGraph.mem_unique _ _).mp member) with fromVariables | collected
  · obtain ⟨index, rfl⟩ := List.mem_ofFn.mp fromVariables
    cases needed
  · obtain ⟨root, rootMember, inside⟩ := List.mem_flatMap.mp collected
    obtain ⟨edge, edgeMember, side⟩ := List.mem_flatMap.mp rootMember
    have original := (CommonGeneratedRigidPool.split_type_member atoms edge.1 edge.2).mp edgeMember
    have grammar := good edge.1 edge.2 original
    simp only [List.mem_cons, List.not_mem_nil, or_false] at side
    rcases side with rfl | rfl
    · rcases CommonGeneratedWidth.lower_subterm edge.1 term grammar.1 inside with same | proper
      · subst term; exact ⟨edge.2, original⟩
      · rw [PresenceGeneratedWidth.upper_no_width term proper] at needed
        cases needed
    · rw [upper_no_width_subterm edge.2 term grammar.2 inside] at needed
      cases needed

theorem pool_width_atom (atoms : List (Atom (Fin m))) (good : GoodAtoms atoms)
    (widths : WidthAtoms atoms) (term : TyTerm (Fin m))
    (member : term ∈ (splitAtoms atoms).pool.terms) (tail : TyTerm (Fin m))
    (needed : widthTail term = some tail) : .tyLe tail .emptyRecord ∈ atoms := by
  obtain ⟨target, included⟩ := pool_width_origin atoms good term member tail needed
  exact widths term target included tail needed

theorem compiled_pool_width (atoms : List (Atom (Fin m))) (good : GoodAtoms atoms)
    (widths : WidthAtoms atoms) (rows : Fin m → Common.Row)
    (values : Fin (splitAtoms atoms).pool.size → Common.Ty)
    (realizes : Realizes (splitAtoms atoms).pool rows values)
    (edges : EdgesHold (compile atoms).edges values) :
    CommonGeneratedWidth.PoolWidth (splitAtoms atoms).pool values := by
  intro term member tail needed included
  have atom := pool_width_atom atoms good widths term member tail needed
  have edge := (CommonGeneratedRigidPool.split_type_member atoms tail .emptyRecord).mpr atom
  have original := (CommonPresenceConstraintGraph.compiled_edges_exact
    (splitAtoms atoms) rows values realizes).mp edges
  have same := CommonPresenceConstraintGraph.realizes_evaluate
    (splitAtoms atoms).pool rows values realizes tail included
  exact Common.subtype_trans same.1 (original (tail, .emptyRecord) edge)

theorem compiled_grammar (atoms : List (Atom (Fin m))) (good : GoodAtoms atoms) :
    CommonPatternBoundWorklist.Grammar (splitAtoms atoms).pool
      (originalEdges (splitAtoms atoms).pool (compile atoms).edges) := by
  intro edge member
  obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp included
  have shape := good original.val.1 original.val.2
    ((CommonGeneratedRigidPool.split_type_member atoms original.val.1 original.val.2).mp original.property)
  simpa only [CommonBoundRefCoalescing.original, CommonBoundRefInspection.LowerRef,
    CommonPatternBoundInspection.UpperRef, Pool.termAt_reference] using shape

theorem compiled_run_models_exact (atoms : List (Atom (Fin m))) (good : GoodAtoms atoms)
    (widths : WidthAtoms atoms) (rows : Fin m → Common.Row)
    (values : Fin (splitAtoms atoms).pool.size → Common.Ty)
    (realizes : Realizes (splitAtoms atoms).pool rows values) :
    EdgesHold (compile atoms).edges values ↔
      ∃ final ∈ CommonPatternBoundWorklist.run (splitAtoms atoms).pool
          (originalEdges (splitAtoms atoms).pool (compile atoms).edges),
        final.Models (edgeHolds (splitAtoms atoms).pool values) (auxHolds (splitAtoms atoms).pool rows values) := by
  constructor
  · intro accepted
    exact (CommonPatternBoundWorklist.run_models_exact _ _ (compiled_grammar atoms good) rows values realizes
      (compiled_pool_width atoms good widths rows values realizes accepted)).mp
      ((CommonBoundRefWorklist.original_edges_exact _ _ values).mpr accepted)
  · rintro ⟨final, returned, models⟩
    apply (CommonBoundRefWorklist.original_edges_exact _ _ values).mp
    intro edge member
    exact models.1 edge (CommonPatternBoundWorklist.run_retains _ _ final returned member)

end Yulang.CommonPatternConstraintGrammar
