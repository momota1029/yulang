import Yulang.CommonPatternFiniteInspection
import Yulang.CommonBoundRefClosedSoundness

/-!
# Clamped soundness for the actual pattern-bound worklist

The historical finite encoding and clamped construction are retained, while
closure and both finite inspection/descent certificates come from the new
pattern dispatcher and worklist. No source grammar or model predicate is
added to the free parameter product. This is a solver-internal soundness
step; full pattern/case generation and retraction remain separate.
-/

namespace Yulang.CommonPatternClosedSoundness

open Common (Ty Row)
open PresenceOpenTailGenerationLowering (Pool)
open CommonOptionalPoolQueries (queries)
open CommonOptionalPool (extend restrictValues)
open CommonOptionalBoundEncoding (InputCheck encodeCheck encodeBranch)
open CommonSymbolicBoundSupport (CheckSupported BranchSupported)
open CommonSymbolicConstraints (Check)
open CommonPresenceConstraintGraph (rowEval Realizes EdgesHold)
open CommonBoundRefWorklist (State)
open CommonFiniteChildInspection (BelowAt BranchAt)
open CommonFiniteBoundRefInspection (RigidRef)

variable {m : Nat}

abbrev Extended (pool : Pool m) := extend pool (queries pool)

def encodedEdges (pool : Pool m) (state : State pool) :
    List (Fin (Extended pool).size × Fin (Extended pool).size) :=
  state.edges.map (CommonBoundRefCoalescing.encodeEdge pool (queries pool))

def AuxHolds (pool : Pool m) (state : State pool) (rows : Fin m → Row)
    (values : Fin (Extended pool).size → Ty) : Prop :=
  ∀ check ∈ state.aux,
    CommonBoundRefBranches.auxHolds pool rows (restrictValues pool (queries pool) values) check

private theorem rigidRef_of_nonvariable (pool : Pool m) (index : CommonBoundRefWorklist.Index pool)
    (nonvariable : CommonBoundRefCoalescing.inputAt pool (queries pool) index = none) :
    RigidRef pool index.val := by
  rcases index with ⟨reference, supported⟩
  cases reference with
  | original slot => exact CommonGeneratedRigidDescent.rigid_termAt pool slot nonvariable
  | _ => trivial

theorem encoded_children_retained (pool : Pool m) (edges : List (CommonBoundRefWorklist.Edge pool))
    (branch : List (InputCheck pool)) (supported : BranchSupported (queries pool) branch)
    (children : (CommonBoundRefBranches.splitBranch pool (queries pool) branch supported).children ⊆ edges)
    (first last : Fin (Extended pool).size)
    (included : Check.childBelow (.ref first) (.ref last) ∈ encodeBranch pool (queries pool) branch supported) :
    (first, last) ∈ edges.map (CommonBoundRefCoalescing.encodeEdge pool (queries pool)) := by
  obtain ⟨⟨check, member⟩, _, same⟩ := List.mem_map.mp included
  have allowed := supported check member
  cases check with
  | childBelow firstPayload lastPayload =>
      cases firstPayload with
      | ref source =>
          cases lastPayload with
          | ref target =>
              simp only [encodeCheck, Check.childBelow.injEq, CommonPayloadProjection.Payload.ref.injEq] at same
              rcases same with ⟨rfl, rfl⟩
              exact List.mem_map.mpr ⟨_, children
                (CommonBoundRefBranches.splitBranch_child_complete pool (queries pool) branch supported
                  source target member), rfl⟩
          | _ => cases allowed
      | _ => cases allowed
  | rowBelow => cases same
  | flag expression =>
      cases expression
      case literal => cases same
      all_goals cases allowed
  | profileBelow => cases allowed

theorem encoded_nonChild_of_aux (pool : Pool m) (branch : List (InputCheck pool))
    (supported : BranchSupported (queries pool) branch) (rows : Fin m → Row)
    (values : Fin (Extended pool).size → Ty)
    (accepted : ∀ check ∈ (CommonBoundRefBranches.splitBranch pool (queries pool) branch supported).aux,
      CommonBoundRefBranches.auxHolds pool rows (restrictValues pool (queries pool) values) check) :
    ∀ check ∈ encodeBranch pool (queries pool) branch supported,
      CommonClampedClosureSoundness.NonChildHolds (Extended pool) rows values check := by
  intro check included
  obtain ⟨⟨original, member⟩, _, rfl⟩ := List.mem_map.mp included
  have allowed := supported original member
  cases original with
  | childBelow first last => cases first <;> cases last <;> first | trivial | cases allowed
  | rowBelow first last =>
      exact accepted _ (CommonBoundRefBranches.splitBranch_aux_complete pool (queries pool)
        branch supported _ member trivial)
  | flag expression =>
      cases expression
      case literal value =>
        exact accepted _ (CommonBoundRefBranches.splitBranch_aux_complete pool (queries pool)
          branch supported _ member trivial)
      all_goals cases allowed
  | profileBelow => cases allowed

private structure RawChoice (pool : Pool m) (state : State pool)
    (actual : Fin (Extended pool).size × Fin (Extended pool).size) where
  origin : CommonBoundRefWorklist.Edge pool
  active : origin ∈ CommonBoundRefWorklist.rigid pool state.edges
  same : CommonBoundRefCoalescing.encodeEdge pool (queries pool) origin = actual
  branch : List (InputCheck pool)
  returned : branch ∈ CommonPatternBoundInspection.inspect pool origin.1.val origin.2.val
  supported : BranchSupported (queries pool) branch
  children : (CommonBoundRefBranches.splitBranch pool (queries pool) branch supported).children ⊆ state.edges
  auxiliaries : (CommonBoundRefBranches.splitBranch pool (queries pool) branch supported).aux ⊆ state.aux

private theorem rawChoice_exists (pool : Pool m) (state : State pool)
    (closed : FiniteBranchingWorklist.Closed (CommonBoundRefWorklist.rigid pool)
      (CommonPatternBoundWorklist.inspect pool) state)
    (actual : Fin (Extended pool).size × Fin (Extended pool).size)
    (member : actual ∈ CommonClampedClosureSoundness.RigidEdges (Extended pool) (encodedEdges pool state)) :
    Nonempty (RawChoice pool state actual) := by
  change actual ∈ CommonBoundCoalescing.rigidComparisons
    (CommonPresenceVariableBounds.template (extend pool (queries pool))
      (state.edges.map (CommonBoundRefCoalescing.encodeEdge pool (queries pool)))) at member
  rw [CommonBoundRefCoalescing.rigid_encode] at member
  obtain ⟨origin, active, same⟩ := List.mem_map.mp member
  obtain ⟨split, returned, _, children, auxiliaries⟩ := closed origin active
  obtain ⟨⟨branch, present⟩, _, equal⟩ := List.mem_map.mp returned
  subst split
  exact ⟨⟨origin, active, same, branch, present, _, children, auxiliaries⟩⟩

private noncomputable def rawChoice (pool : Pool m) (state : State pool)
    (closed : FiniteBranchingWorklist.Closed (CommonBoundRefWorklist.rigid pool)
      (CommonPatternBoundWorklist.inspect pool) state)
    (actual : Fin (Extended pool).size × Fin (Extended pool).size)
    (member : actual ∈ CommonClampedClosureSoundness.RigidEdges (Extended pool) (encodedEdges pool state)) :
    RawChoice pool state actual := Classical.choice (rawChoice_exists pool state closed actual member)

/-- A proof-only selection extracted from the actual finite worklist trace.
The computation and its finite states remain independent of these proofs. -/
noncomputable def selection (pool : Pool m) (state : State pool)
    (closed : FiniteBranchingWorklist.Closed (CommonBoundRefWorklist.rigid pool)
      (CommonPatternBoundWorklist.inspect pool) state) :
    CommonClampedSelectedSoundness.Selection (Extended pool) (encodedEdges pool state) := by
  classical
  refine {
    branch := fun actual => if member : actual ∈ CommonClampedClosureSoundness.RigidEdges
        (Extended pool) (encodedEdges pool state) then
      encodeBranch pool (queries pool) (rawChoice pool state closed actual member).branch
        (rawChoice pool state closed actual member).supported else []
    current := fun actual => if member : actual ∈ CommonClampedClosureSoundness.RigidEdges
        (Extended pool) (encodedEdges pool state) then
      CommonFiniteBoundRefInspection.current pool (rawChoice pool state closed actual member).origin.1.val else false
    measure := fun index => CommonGeneratedRigidDescent.weight ((Extended pool).termAt index)
    ordinary := ?_
    childClosed := ?_
    currentDecreases := ?_ }
  · intro actual member check included
    simp only [dite_eq_left member] at included
    exact CommonFiniteBoundEncoding.encodeBranch_ordinary pool (queries pool)
      (rawChoice pool state closed actual member).branch (rawChoice pool state closed actual member).supported
      check included
  · intro actual member first last included
    simp only [dite_eq_left member] at included
    exact encoded_children_retained pool state.edges (rawChoice pool state closed actual member).branch
      (rawChoice pool state closed actual member).supported (rawChoice pool state closed actual member).children
      first last included
  · intro actual member requested first last included
    simp only [dite_eq_left member] at requested included
    let chosen := rawChoice pool state closed actual member
    have endpoints := CommonBoundRefCoalescing.rigid_endpoints pool (queries pool) state.edges chosen.origin chosen.active
    have smaller := CommonPatternFiniteInspection.encoded_inspect_current_decreases pool (queries pool)
      chosen.origin.1.val chosen.origin.2.val chosen.origin.1.property
      (rigidRef_of_nonvariable pool chosen.origin.1 endpoints.1)
      (rigidRef_of_nonvariable pool chosen.origin.2 endpoints.2) requested
      chosen.branch chosen.returned chosen.supported first last included
    change CommonGeneratedRigidDescent.weight ((Extended pool).termAt first) <
      CommonGeneratedRigidDescent.weight ((Extended pool).termAt
        (CommonBoundRefCoalescing.encodeEdge pool (queries pool) chosen.origin).1) at smaller
    exact chosen.same ▸ smaller

theorem selection_finiteInspection (pool : Pool m) (state : State pool)
    (closed : FiniteBranchingWorklist.Closed (CommonBoundRefWorklist.rigid pool)
      (CommonPatternBoundWorklist.inspect pool) state)
    (rows : Fin m → Row) (values : Fin (Extended pool).size → Ty)
    (realizes : Realizes (Extended pool) rows values) :
    CommonClampedSelectedSoundness.FiniteInspection (Extended pool) (encodedEdges pool state)
      (selection pool state closed) rows values := by
  intro depth actual member guarded sameDepth
  simp only [selection, dite_eq_left member] at guarded sameDepth
  let chosen := rawChoice pool state closed actual member
  have endpoints := CommonBoundRefCoalescing.rigid_endpoints pool (queries pool) state.edges chosen.origin chosen.active
  have finite := CommonPatternFiniteInspection.encoded_inspect_at_sound depth pool (queries pool)
    chosen.origin.1.val chosen.origin.2.val chosen.origin.1.property chosen.origin.2.property
    (rigidRef_of_nonvariable pool chosen.origin.2 endpoints.2) rows values realizes
    chosen.branch chosen.returned chosen.supported guarded sameDepth
  change BelowAt depth (values (CommonBoundRefCoalescing.encodeEdge pool (queries pool) chosen.origin).1)
    (values (CommonBoundRefCoalescing.encodeEdge pool (queries pool) chosen.origin).2) at finite
  exact chosen.same ▸ finite

theorem selection_nonChild (pool : Pool m) (state : State pool)
    (closed : FiniteBranchingWorklist.Closed (CommonBoundRefWorklist.rigid pool)
      (CommonPatternBoundWorklist.inspect pool) state)
    (rows : Fin m → Row) (values : Fin (Extended pool).size → Ty)
    (auxiliary : AuxHolds pool state rows values) :
    CommonClampedSelectedSoundness.NonChildChecks (Extended pool) (encodedEdges pool state)
      (selection pool state closed) rows values := by
  intro actual member check included
  simp only [selection, dite_eq_left member] at included
  let chosen := rawChoice pool state closed actual member
  exact encoded_nonChild_of_aux pool chosen.branch chosen.supported rows values
    (fun check present => auxiliary check (chosen.auxiliaries present)) check included

/-- All ordinary edges of an actual closed worklist state hold in every
clamped independent model whose row/literal auxiliary constraints hold. -/
theorem closed_soundness (pool : Pool m) (state : State pool)
    (closed : FiniteBranchingWorklist.Closed (CommonBoundRefWorklist.rigid pool)
      (CommonPatternBoundWorklist.inspect pool) state)
    (rows : Fin m → Row) (parameters : Fin m → Ty) (values : Fin (Extended pool).size → Ty)
    (model : CommonPresenceTailRegular.Models
      (CommonPresenceClampedBounds.graph (Extended pool) (encodedEdges pool state) rows parameters) values)
    (auxiliary : AuxHolds pool state rows values) : EdgesHold (encodedEdges pool state) values :=
  CommonClampedSelectedSoundness.conditional_soundness (Extended pool) (encodedEdges pool state)
    (selection pool state closed) rows parameters values model
    (selection_finiteInspection pool state closed rows values
      ((CommonPresenceClampedBounds.models_exact (Extended pool) (encodedEdges pool state)
        rows parameters values).mp model).1)
    (selection_nonChild pool state closed rows values auxiliary)

/-- Closure and the finite inspection certificate are supplied by the real
executable run. Only its explicit row/literal constraints remain. -/
theorem returned_soundness (pool : Pool m) (edges : List (CommonBoundRefWorklist.Edge pool))
    (state : State pool) (returned : state ∈ CommonPatternBoundWorklist.run pool edges)
    (rows : Fin m → Row) (parameters : Fin m → Ty) (values : Fin (Extended pool).size → Ty)
    (model : CommonPresenceTailRegular.Models
      (CommonPresenceClampedBounds.graph (Extended pool) (encodedEdges pool state) rows parameters) values)
    (auxiliary : AuxHolds pool state rows values) : EdgesHold (encodedEdges pool state) values :=
  closed_soundness pool state (CommonPatternBoundWorklist.run_closed pool edges state returned)
    rows parameters values model auxiliary

theorem returned_solve_soundness (pool : Pool m) (edges : List (CommonBoundRefWorklist.Edge pool))
    (state : State pool) (returned : state ∈ CommonPatternBoundWorklist.run pool edges)
    (rows : Fin m → Row) (parameters : Fin m → Ty) (recursiveParameters : Fin (Extended pool).size → Ty)
    (auxiliary : AuxHolds pool state rows
      (CommonPresenceClampedBounds.solve (Extended pool) (encodedEdges pool state) rows parameters recursiveParameters)) :
    EdgesHold (encodedEdges pool state)
      (CommonPresenceClampedBounds.solve (Extended pool) (encodedEdges pool state) rows parameters recursiveParameters) :=
  returned_soundness pool edges state returned rows parameters _
    (CommonPresenceTailRegular.solveBlock_models _ recursiveParameters) auxiliary

end Yulang.CommonPatternClosedSoundness
