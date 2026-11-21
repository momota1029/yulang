import Yulang.GeneralCommittedReadAddress309

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralCommittedReadErasure309
open GeneralDeclarations (Registry)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralGeneratedDictionaryRun299 (Read)
open GeneralCommittedReadTrace309 (Trace)
open GeneralCommittedReadAddress309 (cursor subtree subtrace)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls} {r : Registry} {s : State roles} {root : Occurrence roles}
variable {m : Assignment} {read : Read} {decode : Nat → Occurrence roles}

mutual
  /-- The actual node proofs suffice to erase a verified trace. No new
  global model, stable state, or output witness is chosen in recursion. -/
  theorem erase (d : Payload) (i : Nat) (proof : Trace r s root m read decode i d) :
      (boundary roles).Evidence r s m (decode i) d := by
    cases proof with
    | node j row ds _ frame proofs =>
      obtain ⟨_,p,certificate⟩ := frame
      exact GeneralNominalVersionedEvidence231.evidence_node ⟨p,certificate⟩
        (eraseForest ds row.children proofs)
  termination_by sizeOf d

  theorem eraseForest (ds : List Payload) (is : List Nat)
      (proof : All₂ (Trace r s root m read decode) is ds) :
      All₂ ((boundary roles).Evidence r s m) (is.map decode) ds := by
    cases proof with
    | nil => exact .nil
    | @cons i d rest payloads one many =>
      exact .cons (erase d i one) (eraseForest payloads rest many)
  termination_by sizeOf ds
end

theorem evidence_at_address {ps : List Nat} {i j : Nat} {d e : Payload}
    (verified : Trace r s root m read decode i d)
    (position : cursor read i ps = some j) (piece : subtree d ps = some e) :
    (boundary roles).Evidence r s m (decode j) e :=
  erase e j (subtrace verified position piece)

end Yulang.GeneralCommittedReadErasure309
