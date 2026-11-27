import Yulang.GeneralDeclarativeI65I74ProjectionBatchInput464
import Yulang.GeneralDeclarativeI65I74ProjectionFullFits464

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NamedProjection464
open Yulang.GeneralDeclarativeI65
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeK2Graph321.AddAtOneSource
open GeneralDeclarativeGraphRows321 (observed shapeOf)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open PreparedDeclarations463
open PhysicalVisit463 PhysicalVisit463.IssuedProjection464
open RoutedInlineStructural458 (ModelOpening)
open RecordTraversal455.MixedQA (ChildAt)

structure ProjectionBatchWire (p : SnapshotPair) where
  rows : List ProjectionWire
  field : HeadFieldWire p.after.old

def readProjectionBatchField (p : SnapshotPair) (t : CheckedTable p.before.state.base.core.current)
    (w : ProjectionBatchWire p) : Option HeadFieldReceipt := do
  if !checkSuppliedBatch p.pre p.post w.rows then none else
    let r ← readHeadField (p := p.after.old) (p.afterTable t) w.field
    if r.rows.any (fun i => decide (p.pre.equations.length ≤ i)) then some r else none

def ExactProjectionBatchField (p : SnapshotPair)
    (t : CheckedTable p.before.state.base.core.current) (r : HeadFieldReceipt) : Prop :=
  ActualSuppliedBatch p.pre p.post ∧
    ExactHeadField (p := p.after.old) (p.afterTable t) r ∧
    ∃ i ∈ r.rows, p.pre.equations.length ≤ i

theorem exact_batch_field_iff_a_single_data_only_verification
    (p : SnapshotPair) (t : CheckedTable p.before.state.base.core.current) (r : HeadFieldReceipt) :
    ExactProjectionBatchField p t r ↔ ∃ w, readProjectionBatchField p t w = some r := by
  constructor
  · rintro ⟨batch,found,occurs⟩
    obtain ⟨proof,ok⟩ := (exact_supplied_phase_iff_finite_prefix_proof_data ..).mp batch
    obtain ⟨field,passes⟩ := (prechecked_head_field_iff_finite_exact_wire ..).mp found
    exact ⟨⟨proof,field⟩,by simp [readProjectionBatchField,occurs,ok,passes,Option.bind]⟩
  · rintro ⟨w,pass⟩
    by_cases phase : checkSuppliedBatch p.pre p.post w.rows = true
    · cases finds : readHeadField (p := p.after.old) (p.afterTable t) w.field with
      | none => simp [readProjectionBatchField,phase,finds,Option.bind] at pass
      | some got =>
        by_cases used : ∃ i ∈ got.rows, p.pre.equations.length ≤ i
        · have eq : got = r := by
            simpa [readProjectionBatchField,phase,finds,used,Option.bind] using pass
          cases eq
          exact ⟨checked_batch_has_exact_independent_supplied_prefix_evidence phase,
            (prechecked_head_field_iff_finite_exact_wire ..).mpr ⟨_,finds⟩,used⟩
        · simp [readProjectionBatchField,phase,finds,used,Option.bind] at pass
    · simp [readProjectionBatchField,phase] at pass

private theorem same_routes {s t : GeneralDeclarativeI65.State} (eq : s.routes = t.routes) (o : Origin) (site : Nat) :
    OriginRoute s o site ↔ OriginRoute t o site := by
  constructor
  · intro openRoute
    cases openRoute with
    | direct => exact .direct
    | authored seen => exact .authored (eq ▸ seen)
  · intro openRoute
    cases openRoute with
    | direct => exact .direct
    | authored seen => exact .authored (eq ▸ seen)

/-- Every selected physical hop retains its actual original (or new suffix)
ordinal and an exact native issuer in the after input. Under independent
unchanged stored origin/route facts, it is the very same issuer in the old
input as well; equality of semantic assignments alone never provides that. -/
theorem all_selected_batch_hops_keep_exact_ordinal_and_original_issuer
    {p : SnapshotPair} {t : CheckedTable p.before.state.base.core.current} {r : HeadFieldReceipt}
    (h : ExactProjectionBatchField p t r)
    (origins : p.before.state.base.core.origins = p.after.state.base.core.origins)
    (routes : p.before.state.base.core.routes = p.after.state.base.core.routes)
    (m : I72.Model) (fit : FitsFull p.after.state m) :
    r.literal ≠ [] ∧ AliasCycle p.pre (observed p.pre) r.terminal ∧
    ∀ hop ordinal : Nat, r.rows[hop]? = some ordinal →
      ∃ logical query row shape addr child next used origin,
        r.path[hop]? = some (addr,child) ∧
        p.post.equations[ordinal]? = some row ∧
        ((ordinal < p.pre.equations.length ∧ p.pre.equations[ordinal]? = some row) ∨
          (p.pre.equations.length ≤ ordinal ∧
           (suppliedRows p.pre p.post)[ordinal - p.pre.equations.length]? = some row ∧
           Derives p.pre (.variable row.left) row.right)) ∧
        GeneralDeclarativeLowerKnown321.Alias p.pre logical row.left ∧
        shapeOf row.right = some shape ∧ ChildAt shape query addr child next ∧
        origin ∈ p.before.state.base.core.origins ∧ origin ∈ p.after.state.base.core.origins ∧
        OriginRoute p.before.state.base.core origin logical ∧ OriginRoute p.after.state.base.core origin logical ∧
        origin.slot = row.left ∧ m.nativeSyntax origin.slot = some origin.endpoint ∧
        ModelOpening p.after.state.base.core m logical row shape query addr child next used := by
  obtain ⟨_,_,_,nonempty,_,cycle⟩ := exact_prechecked_head_field_keeps_original_and_evidence_in_each_fit
    ⟨p.after,p.afterTable t⟩ h.2.1 m fit
  refine ⟨nonempty,(accepted_batch_preserves_every_exact_original_k2 h.1.1 _).mp cycle,?_⟩
  intro hop ordinal pick
  obtain ⟨_,_,_,trail,_,_,_⟩ := h.2.1
  obtain ⟨logical,query,row,shape,addr,child,next,used,origin,selected,atPost,alias,form,position,_,
    issued,route,physical,reads,model⟩ :=
      selected_index_keeps_the_exact_issued_owner_in_the_same_fit trail m fit.1 pick
  have ordered := (literal_row_order_and_ordinary_constraints_are_exact h.1.1).2
  have physicalRow : (ordinal < p.pre.equations.length ∧ p.pre.equations[ordinal]? = some row) ∨
          (p.pre.equations.length ≤ ordinal ∧
           (suppliedRows p.pre p.post)[ordinal - p.pre.equations.length]? = some row ∧
           Derives p.pre (.variable row.left) row.right) := by
    by_cases old : ordinal < p.pre.equations.length
    · left
      have chosen : p.post.equations[ordinal]? = some row := atPost
      rw [ordered,List.getElem?_append_left old] at chosen
      exact ⟨old,chosen⟩
    · right
      have new := Nat.le_of_not_gt old
      have chosen : p.post.equations[ordinal]? = some row := atPost
      rw [ordered,List.getElem?_append_right new] at chosen
      exact ⟨new,chosen,(independent_prefix_derivations_are_iff_literal_derivability_in_first_state
        h.1.1).mp h.1.2 row (List.mem_of_getElem? chosen)⟩
  exact ⟨logical,query,row,shape,addr,child,next,used,origin,selected,atPost,physicalRow,
    (accepted_batch_preserves_exact_original_aliases h.1.1 _ _).mp alias,form,position,
    origins.symm ▸ issued,issued,(same_routes routes _ _).mpr route,route,physical,reads,model⟩

end Yulang.GeneralDeclarativeI65.I72.NamedProjection464
