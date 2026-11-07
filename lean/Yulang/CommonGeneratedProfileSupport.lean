import Yulang.CommonSymbolicProfileSupport
import Yulang.CommonGeneratedRigidDescent

/-!
# A static reference universe for the actual rigid inspection pass

The only profile labels used by this pass are zero for width-shape queries
and labels of required-field targets already present in the original pool.
All primitive masks are empty at this entry point. Guarded payloads retain
their original finite node IDs, including negative arrow arguments.

Every check in every returned first-pass branch fits the finite universe
below. This statement is purely syntactic and holds for every pool and edge
list; it needs neither a model assignment nor a source-support premise.
It does not prove that later projection expansion and variable propagation
remain in this universe. Row expressions are retained by the inspector in
their own original ID domain and are not counted as type references here.
-/

namespace Yulang.CommonGeneratedProfileSupport

open CommonSymbolicProfileSupport
open CommonSymbolicRecordProfiles
open CommonPayloadProjection (Payload)
open CommonSymbolicConstraints (Check Branch)
open CommonGeneratedRigidInspection (inspect inspectSource inspectSlot saturate)
open Core.PresenceGeneration (TyTerm RowTerm)
open PresenceOpenTailGenerationLowering (Pool)

variable {m : Nat}

def requiredLabels : TyTerm α → List Nat
  | .required label _ => [label]
  | _ => []

def targetLabels (pool : Pool m) : List Nat := 0 :: pool.terms.flatMap requiredLabels

def queries (pool : Pool m) : List (List Nat × Nat) := (targetLabels pool).map (fun label => ([], label))

def passUniverse (pool : Pool m) : List (Reference (Fin pool.size) (Fin pool.size)) :=
  queriesUniverse pool (queries pool)

def checkReferences : Check Rows Node Child → List (Reference Node Child)
  | .childBelow source target => payloadReferences source ++ payloadReferences target
  | .rowBelow _ _ => []
  | .flag condition => boolReferences condition
  | .profileBelow source target => profileReferences source ++ payloadReferences target

def branchReferences (branch : Branch Rows Node Child) : List (Reference Node Child) :=
  branch.flatMap checkReferences

theorem zero_mem_targetLabels (pool : Pool m) : 0 ∈ targetLabels pool := List.mem_cons_self

theorem required_mem_targetLabels (pool : Pool m) (label : Nat) (payload : TyTerm (Fin m))
    (member : .required label payload ∈ pool.terms) : label ∈ targetLabels pool :=
  List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨.required label payload, member, List.mem_cons_self⟩)

theorem query_mem (pool : Pool m) (label : Nat) (member : label ∈ targetLabels pool) : ([], label) ∈ queries pool :=
  List.mem_map.mpr ⟨label, member, rfl⟩

theorem payload_mem_universe (pool : Pool m) (child : Fin pool.size) : Reference.payload child ∈ passUniverse pool :=
  List.mem_flatMap.mpr ⟨([], 0), query_mem pool 0 (zero_mem_targetLabels pool),
    payload_mem_poolUniverse pool [] 0 child⟩

theorem payload_support (pool : Pool m) (payload : Payload (Fin pool.size)) :
    Fits (fun reference => reference ∈ passUniverse pool) (payloadReferences payload) := by
  induction payload with
  | ref child => simpa [Fits, payloadReferences] using payload_mem_universe pool child
  | bottom | top => simp [Fits, payloadReferences]
  | union first last before after | inter first last before after =>
      intro reference member
      exact (List.mem_append.mp member).elim (before reference) (after reference)

theorem compiled_summary_support (pool : Pool m) (source : TyTerm (Fin m)) (member : source ∈ pool.terms)
    (label : Nat) (labelPresent : label ∈ targetLabels pool) :
    Fits (fun reference => reference ∈ passUniverse pool)
      (summaryReferences (CommonSymbolicSourceProfiles.compileNode pool [] label source member)) :=
  compileNode_queries_support pool source member (queries pool) [] label (query_mem pool label labelPresent)

theorem inspectSource_support (pool : Pool m) (source : TyTerm (Fin m)) (member : source ∈ pool.terms)
    (target : CommonGeneratedRigidInspection.RigidNode pool) (targetSlot : Fin pool.size) :
    Fits (fun reference => reference ∈ passUniverse pool)
      (branchReferences (inspectSource pool source member target targetSlot)) := by
  cases source <;> cases target <;>
    simp [inspectSource, CommonSymbolicRigidInspection.inspect, CommonSymbolicRigidInspection.unionLeft,
      branchReferences, checkReferences, payloadReferences, boolReferences, Fits, payload_mem_universe]

theorem inspect_support (pool : Pool m) (source target : TyTerm (Fin m))
    (sourceMember : source ∈ pool.terms) (targetMember : target ∈ pool.terms) :
    Fits (fun reference => reference ∈ passUniverse pool)
      (branchReferences (inspect pool source target sourceMember targetMember)) := by
  cases target with
  | emptyRecord =>
      intro reference member
      simp only [inspect, branchReferences, List.flatMap_cons, List.flatMap_nil, List.append_nil, checkReferences] at member
      exact compiled_summary_support pool source sourceMember 0 (zero_mem_targetLabels pool) reference
        (by simp [summaryReferences, member])
  | required label payload =>
      intro reference member
      simp only [inspect, branchReferences, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        checkReferences, List.mem_append] at member
      rcases member with projected | child
      · exact compiled_summary_support pool source sourceMember label
          (required_mem_targetLabels pool label payload targetMember) reference
          (by simp [summaryReferences, projected])
      · exact payload_support pool _ reference child
  | base | pair | arrow | bottom | variant => exact inspectSource_support pool _ _ _ _
  | var | top | inter | union | exactEmpty | record | recordDefault =>
      simp [inspect, CommonSymbolicRigidInspection.interRight, branchReferences,
        checkReferences, payloadReferences, boolReferences, Fits, payload_mem_universe]

theorem inspectSlot_support (pool : Pool m) (edge : Fin pool.size × Fin pool.size) :
    Fits (fun reference => reference ∈ passUniverse pool) (branchReferences (inspectSlot pool edge)) :=
  inspect_support pool _ _ _ _

/-- All first-pass branches, including those of every actual generated
clause, retain this input-computable reference universe. This is not recursive
worklist closure and does not constrain the independent row/type assignments. -/
theorem saturate_support (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (branch : CommonGeneratedRigidInspection.Checks pool) (returned : branch ∈ saturate pool edges) :
    Fits (fun reference => reference ∈ passUniverse pool) (branchReferences branch) := by
  intro reference member
  obtain ⟨check, inBranch, inCheck⟩ := List.mem_flatMap.mp member
  have original := CommonGeneratedRigidDescent.discharge_subset _ branch returned check inBranch
  obtain ⟨edge, _, emitted⟩ := List.mem_flatMap.mp original
  exact inspectSlot_support pool edge reference (List.mem_flatMap.mpr ⟨check, emitted, inCheck⟩)

theorem targetLabels_length_le (pool : Pool m) : (targetLabels pool).length ≤ pool.size + 1 := by
  have bounded (terms : List (TyTerm (Fin m))) : (terms.flatMap requiredLabels).length ≤ terms.length := by
    induction terms with
    | nil => exact Nat.le_refl 0
    | cons term rest ih =>
        rw [List.flatMap_cons, List.length_append]
        cases term <;> simp_all [requiredLabels] <;> omega
  exact Nat.add_le_add_right (bounded pool.terms) 1

theorem universe_length (pool : Pool m) :
    (passUniverse pool).length = 8 * pool.size * (targetLabels pool).length := by
  simp only [passUniverse, queriesUniverse_length, queries, List.length_map]

theorem universe_length_le (pool : Pool m) : (passUniverse pool).length ≤ 8 * pool.size * (pool.size + 1) := by
  rw [universe_length]
  exact Nat.mul_le_mul_left _ (targetLabels_length_le pool)

end Yulang.CommonGeneratedProfileSupport
