import Yulang.GeneralPositiveForkNodes309

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24500
set_option maxHeartbeats 14500000
namespace Yulang.GeneralPositiveForkPayload309
open GeneralPositiveForkSource309 (compiled registry root)
open GeneralPositiveForkInstall309 (after inhabited)
open GeneralPositiveForkEvidence309 (payload leaf_evidence root_evidence)
open GeneralPositiveForkNodes309
open GeneralNominalVersionedEvidence231 (Evidence Instance)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload PayloadEvidence)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)

def expected : Node → Payload
  | .parent => payload | .low => .node 2 [] | .high => .node 3 []

theorem instance_shape (n : Node) (m : Assignment) (k : Nat) (cs)
    (cert : Instance compiled after.core m (focus n) k cs) :
    k = key n ∧ cs = (links n).map focus := by
  obtain ⟨p,proof⟩ := cert
  have close := exact_frame n proof.frame
  subst p
  exact ⟨proof.frame.key_eq.symm,proof.children_eq.trans (child_list n)⟩

private theorem indexed_leaf (n : Node) (noChildren : links n = [])
    (m : Assignment) (d : Payload) (ev : PayloadEvidence (Instance compiled after.core m) (focus n) d) :
    d = .node (key n) [] := by
  cases ev with
  | node here below =>
    obtain ⟨rfl,eq⟩ := instance_shape n m _ _ here
    rw [noChildren] at eq
    cases eq
    cases below
    rfl

theorem payload_exact (n : Node) (m : Assignment) (d : Payload)
    (ev : Evidence compiled after.core m (focus n) d) : d = expected n := by
  have exactIndexed := (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr ev
  cases n with
  | low => exact indexed_leaf .low rfl m d exactIndexed
  | high => exact indexed_leaf .high rfl m d exactIndexed
  | parent =>
    cases exactIndexed with
    | node ins children =>
      obtain ⟨rfl,eq⟩ := instance_shape .parent m _ _ ins
      change _ = [focus .low,focus .high] at eq
      cases eq
      cases children with
      | cons a tail =>
        cases tail with
        | cons b empty =>
          cases empty
          rw [indexed_leaf .low rfl m _ a,indexed_leaf .high rfl m _ b]
          rfl

theorem iff_expected (n : Node) (m : Assignment) (valid : Models after m) (d : Payload) :
    (boundary roles).Evidence registry after m (focus n) d ↔ d = expected n := by
  constructor
  · exact payload_exact n m d
  · rintro rfl
    cases n
    · exact root_evidence m valid
    · exact leaf_evidence .low m valid
    · exact leaf_evidence .high m valid

theorem swapped_rejected (m : Assignment) :
    ¬ (boundary roles).Evidence registry after m root (.node 1 [.node 3 [],.node 2 []]) := by
  intro got
  have equal := payload_exact .parent m _ got
  cases equal

theorem duplicated_rejected (m : Assignment) :
    ¬ (boundary roles).Evidence registry after m root (.node 1 [.node 2 [],.node 2 []]) := by
  intro got
  have equal := payload_exact .parent m _ got
  cases equal

theorem truncated_rejected (m : Assignment) :
    ¬ (boundary roles).Evidence registry after m root (.node 1 [.node 2 []]) := by
  intro got
  have equal := payload_exact .parent m _ got
  cases equal

end Yulang.GeneralPositiveForkPayload309
