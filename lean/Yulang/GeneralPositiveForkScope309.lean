import Yulang.GeneralPositiveForkVerified309
import Yulang.GeneralSelectedReadScope309

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 13000000
namespace Yulang.GeneralPositiveForkScope309
open GeneralPositiveForkSource309 (registry root checked)
open GeneralPositiveForkInstall309 (after inhabited reachable)
open GeneralPositiveForkCompiler309 (read decode)
open GeneralPositiveForkCheck309 (read_root read_low read_high accepted)
open GeneralPositiveForkVerified309 (certified_reader)
open GeneralPositiveForkEvidence309 (payload)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (Models)
open GeneralOrderedDictionaryFootprint309 (need AgreeOn validate_agrees)
open GeneralGeneratedDictionaryRun299 (Read)
open GeneralGeneratedDictionaryScope299 (Faithful)
open GeneralOrderedDictionaryCheck309 (validate)
open GeneralCommittedReadTrace309 (Trace)
open GeneralDeclarationExamples (roles)
open GeneralDictionaryReadback (Payload)

def withExtra : Read := fun i => if i = 19 then some ⟨777,[]⟩ else read i

theorem need_exact (fuel : Nat) : need read (fuel+2) 0 = [0,1,2] := by
  simp [need,read_root,read_low,read_high]

theorem agree (fuel : Nat) : AgreeOn (need read fuel 0) read withExtra := by
  intro i member
  have fresh : i ≠ 19 := by
    cases fuel with
    | zero => cases member
    | succ n =>
      cases n with
      | zero =>
        simp [need,read_root] at member
        subst i
        decide
      | succ n =>
        change i ∈ need read (n+2) 0 at member
        rw [need_exact] at member
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl|rfl|rfl <;> decide
  simp [withExtra,fresh]

theorem unchanged_at_root (fuel : Nat) (d : Payload) :
    validate withExtra fuel 0 d = validate read fuel 0 d :=
  (validate_agrees read withExtra fuel 0 (agree fuel) d).symm

theorem accepted_root_still_sound (fuel : Nat) (d : Payload)
    (pass : validate withExtra fuel 0 d = .ok ()) :
    ∀ m, Models after m →
      Trace registry after root m read decode 0 d ∧ (boundary roles).Evidence registry after m root d :=
  (GeneralSelectedReadScope309.checked_on_footprint ⟨rfl,checked⟩ reachable read withExtra decode
    certified_reader ⟨_,inhabited⟩ fuel 0 d (agree fuel) .root pass).2

theorem spare_accepted : validate withExtra 1 19 (.node 777 []) = .ok () := rfl

theorem extra_not_faithful : ¬ Faithful (b:=boundary roles) (r:=registry) (s:=after) withExtra decode := by
  intro bogus
  have impossible := bogus 19 ⟨777,[]⟩ (by rfl)
  have same := B4TargetV8.local_functional impossible (GeneralPositiveForkSelection309.actual_pick .parent)
  cases same

theorem cannot_infer_outside :
    ¬ (boundary roles).Evidence registry after GeneralNominalExamples.model (decode 19) (.node 777 []) := by
  intro wrong
  have impossible := GeneralPositiveForkPayload309.payload_exact .parent GeneralNominalExamples.model _ wrong
  cases impossible

end Yulang.GeneralPositiveForkScope309
