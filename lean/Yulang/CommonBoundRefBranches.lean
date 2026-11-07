import Yulang.CommonBoundRefCoalescing
import Yulang.FiniteBranchingWorklist

/-!
# Split actual symbolic branches into finite edges and auxiliary checks

This translation preserves the independent meaning of every supported
branch. Its finite edge indices carry only query-membership proofs.
Auxiliary checks retain their original syntax and shared row IDs. No model
or residual-holds premise is packaged into the translated branch.
-/

namespace Yulang.CommonBoundRefBranches

open PresenceOpenTailGenerationLowering (Pool)
open CommonOptionalPool (Query)
open CommonSymbolicBoundInspection (BoundRef)
open CommonSymbolicBoundSupport (CheckSupported BranchSupported OutputSupported)
open CommonOptionalBoundEncoding (InputCheck)
open CommonBoundRefCoalescing (Index Edge)
open CommonSymbolicConstraints (Check)

variable {m : Nat}

abbrev Split (pool : Pool m) (queries : List (Query pool)) :=
  FiniteBranchingWorklist.Branch (Edge pool queries) (InputCheck pool)

def edgeHolds (pool : Pool m) (queries : List (Query pool))
    (values : Fin pool.size → Common.Ty) (edge : Edge pool queries) : Prop :=
  Common.Subtype (edge.1.val.eval values) (edge.2.val.eval values)

def auxHolds (pool : Pool m) (rows : Fin m → Common.Row) (values : Fin pool.size → Common.Ty)
    (check : InputCheck pool) : Prop :=
  check.Holds (CommonPresenceConstraintGraph.rowEval rows) values (BoundRef.eval values)

def append (pool : Pool m) (queries : List (Query pool))
    (first last : Split pool queries) : Split pool queries :=
  ⟨first.children ++ last.children, first.aux ++ last.aux⟩

theorem append_models (pool : Pool m) (queries : List (Query pool))
    (first last : Split pool queries) (edgeValid : Edge pool queries → Prop) (auxValid : InputCheck pool → Prop) :
    (append pool queries first last).Models edgeValid auxValid ↔
      first.Models edgeValid auxValid ∧ last.Models edgeValid auxValid := by
  simp only [append, FiniteBranchingWorklist.Branch.Models, List.mem_append,
    or_imp, forall_and]
  exact and_and_and_comm

def splitCheck (pool : Pool m) (queries : List (Query pool)) :
    (check : InputCheck pool) → CheckSupported queries check → Split pool queries
  | .childBelow (.ref source) (.ref target), supported =>
      ⟨[(⟨source, supported.1⟩, ⟨target, supported.2⟩)], []⟩
  | other, _ => ⟨[], [other]⟩

theorem splitCheck_exact (pool : Pool m) (queries : List (Query pool))
    (rows : Fin m → Common.Row) (values : Fin pool.size → Common.Ty)
    (check : InputCheck pool) (supported : CheckSupported queries check) :
    (splitCheck pool queries check supported).Models (edgeHolds pool queries values) (auxHolds pool rows values) ↔
      auxHolds pool rows values check := by
  cases check with
  | childBelow source target =>
      cases source <;> cases target <;>
        simp [splitCheck, FiniteBranchingWorklist.Branch.Models, edgeHolds,
          auxHolds, Check.Holds, CommonPayloadProjection.Payload.evalLayer]
  | _ => simp [splitCheck, FiniteBranchingWorklist.Branch.Models]

def splitBranch (pool : Pool m) (queries : List (Query pool)) :
    (branch : List (InputCheck pool)) → BranchSupported queries branch → Split pool queries
  | [], _ => ⟨[], []⟩
  | check :: rest, supported => append pool queries
      (splitCheck pool queries check (supported check List.mem_cons_self))
      (splitBranch pool queries rest (fun actual member => supported actual (List.mem_cons_of_mem _ member)))

theorem splitBranch_exact (pool : Pool m) (queries : List (Query pool))
    (rows : Fin m → Common.Row) (values : Fin pool.size → Common.Ty)
    (branch : List (InputCheck pool)) (supported : BranchSupported queries branch) :
    (splitBranch pool queries branch supported).Models (edgeHolds pool queries values) (auxHolds pool rows values) ↔
      CommonSymbolicConstraints.Branch.Holds
        (CommonPresenceConstraintGraph.rowEval rows) values (BoundRef.eval values) branch := by
  induction branch with
  | nil => simp [splitBranch, FiniteBranchingWorklist.Branch.Models]
  | cons check rest ih =>
      rw [CommonSymbolicConstraints.holds_cons]
      exact (append_models pool queries _ _ _ _).trans
        (and_congr (splitCheck_exact pool queries rows values check _) (ih _))

def Auxiliary (check : InputCheck pool) : Prop :=
  match check with
  | .rowBelow _ _ | .flag (.literal _) => True
  | _ => False

theorem splitCheck_auxiliary (pool : Pool m) (queries : List (Query pool))
    (check : InputCheck pool) (supported : CheckSupported queries check)
    (actual : InputCheck pool) (member : actual ∈ (splitCheck pool queries check supported).aux) :
    Auxiliary actual := by
  cases check with
  | childBelow source target =>
      cases source <;> cases target
      all_goals first
      | exact False.elim supported
      | cases member
  | rowBelow =>
      have same := List.mem_singleton.mp member
      subst actual
      trivial
  | flag expression =>
      cases expression
      case literal =>
        have same := List.mem_singleton.mp member
        subst actual
        trivial
      all_goals exact False.elim supported
  | profileBelow => exact False.elim supported

theorem splitBranch_auxiliary (pool : Pool m) (queries : List (Query pool))
    (branch : List (InputCheck pool)) (supported : BranchSupported queries branch)
    (actual : InputCheck pool) (member : actual ∈ (splitBranch pool queries branch supported).aux) :
    Auxiliary actual := by
  induction branch with
  | nil => cases member
  | cons check rest ih =>
      rcases List.mem_append.mp member with here | remaining
      · exact splitCheck_auxiliary pool queries check _ actual here
      · exact ih _ remaining

theorem splitCheck_child_origin (pool : Pool m) (queries : List (Query pool))
    (check : InputCheck pool) (supported : CheckSupported queries check)
    (edge : Edge pool queries) (member : edge ∈ (splitCheck pool queries check supported).children) :
    check = .childBelow (.ref edge.1.val) (.ref edge.2.val) := by
  cases check with
  | childBelow source target =>
      cases source <;> cases target
      all_goals first
      | exact False.elim supported
      | have same := List.mem_singleton.mp member
        subst edge
        rfl
  | rowBelow | flag | profileBelow => cases member

theorem splitBranch_child_origin (pool : Pool m) (queries : List (Query pool))
    (branch : List (InputCheck pool)) (supported : BranchSupported queries branch)
    (edge : Edge pool queries) (member : edge ∈ (splitBranch pool queries branch supported).children) :
    Check.childBelow (.ref edge.1.val) (.ref edge.2.val) ∈ branch := by
  induction branch with
  | nil => cases member
  | cons check rest ih =>
      rcases List.mem_append.mp member with here | remaining
      · exact List.mem_cons.mpr (Or.inl (splitCheck_child_origin pool queries check _ edge here).symm)
      · exact List.mem_cons_of_mem _ (ih _ remaining)

theorem splitCheck_aux_origin (pool : Pool m) (queries : List (Query pool))
    (check : InputCheck pool) (supported : CheckSupported queries check)
    (actual : InputCheck pool) (member : actual ∈ (splitCheck pool queries check supported).aux) :
    actual = check := by
  cases check with
  | childBelow source target =>
      cases source <;> cases target
      all_goals first
      | exact False.elim supported
      | cases member
  | rowBelow | flag | profileBelow => exact List.mem_singleton.mp member

theorem splitBranch_aux_origin (pool : Pool m) (queries : List (Query pool))
    (branch : List (InputCheck pool)) (supported : BranchSupported queries branch)
    (actual : InputCheck pool) (member : actual ∈ (splitBranch pool queries branch supported).aux) : actual ∈ branch := by
  induction branch with
  | nil => cases member
  | cons check rest ih =>
      rcases List.mem_append.mp member with here | remaining
      · exact List.mem_cons.mpr (Or.inl (splitCheck_aux_origin pool queries check _ actual here))
      · exact List.mem_cons_of_mem _ (ih _ remaining)

def splitOutput (pool : Pool m) (queries : List (Query pool))
    (output : List (List (InputCheck pool))) (supported : OutputSupported queries output) :
    List (Split pool queries) :=
  output.attach.map (fun branch => splitBranch pool queries branch.val (supported branch.val branch.property))

theorem splitOutput_exact (pool : Pool m) (queries : List (Query pool))
    (rows : Fin m → Common.Row) (values : Fin pool.size → Common.Ty)
    (output : List (List (InputCheck pool))) (supported : OutputSupported queries output) :
    (∃ branch ∈ splitOutput pool queries output supported,
      branch.Models (edgeHolds pool queries values) (auxHolds pool rows values)) ↔
      CommonSymbolicBoundInspection.Holds (CommonPresenceConstraintGraph.rowEval rows) values output := by
  constructor
  · rintro ⟨branch, member, accepted⟩
    obtain ⟨⟨original, included⟩, _, rfl⟩ := List.mem_map.mp member
    exact ⟨original, included, (splitBranch_exact pool queries rows values original _).mp accepted⟩
  · rintro ⟨original, included, accepted⟩
    exact ⟨_, List.mem_map.mpr ⟨⟨original, included⟩, List.mem_attach _ _, rfl⟩,
      (splitBranch_exact pool queries rows values original _).mpr accepted⟩

end Yulang.CommonBoundRefBranches
