import Yulang.GeneralPositiveForkSettlement309
import Yulang.GeneralOrderedDictionaryCheck309

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24500
set_option maxHeartbeats 14000000
namespace Yulang.GeneralPositiveForkCheck309
open GeneralOrderedDictionaryCheck309 (Error validate exact)
open GeneralPositiveForkCompiler309 (read decode lookup row row_exact encode root_code_exact)
open GeneralPositiveForkNodes309 (links key)
open GeneralPositiveForkSource309 (compiled registry root)
open GeneralPositiveForkInstall309 (after inhabited)
open GeneralPositiveForkEvidence309 (payload)
open GeneralPositiveForkPayload309 (expected)
open GeneralDictionaryReadback (Payload)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralDeclarationExamples (roles)

theorem accepted (fuel : Nat) (d : Payload) :
    validate read fuel 0 d = .ok () ↔ 2 ≤ fuel ∧ d = payload :=
  (GeneralOrderedDictionaryCheck309.exact ..).trans (root_code_exact fuel d)

theorem accepts_all_models (fuel : Nat) (d : Payload) :
    validate read fuel 0 d = .ok () ↔ 2 ≤ fuel ∧
      ∀ m : Assignment, Models after m → (boundary roles).Evidence registry after m root d := by
  rw [accepted]
  constructor
  · rintro ⟨hf,rfl⟩
    exact ⟨hf,GeneralPositiveForkSettlement309.certified_via_commitment.2⟩
  · rintro ⟨hf,shape⟩
    exact ⟨hf,GeneralPositiveForkPayload309.payload_exact .parent _ _ (shape _ inhabited)⟩

theorem actual_compiler (fuel : Nat) (d : Payload) (pass : validate read fuel 0 d = .ok ()) :
    B4TargetV8.Classify (boundary roles) registry after root (.selected d) ∧
    ∀ m, Models after m →
      (boundary roles).Evidence registry after m root d :=
  GeneralPositiveForkCompiler309.all_fuel_sound fuel 0 d
    ((GeneralOrderedDictionaryCheck309.exact ..).mp pass)

theorem missing_source (fuel i : Nat) (outside : 3 ≤ i) (d : Payload) :
    validate read (fuel+1) i d = .error (.missing i) := by
  cases d
  match i with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | _+3 => rfl

theorem read_root : read 0 = some ⟨1,[1,2]⟩ := by
  change some (row .parent) = _
  rw [row_exact]
  rfl

theorem read_low : read 1 = some ⟨2,[]⟩ := by
  change some (row .low) = _
  rw [row_exact]
  rfl

theorem read_high : read 2 = some ⟨3,[]⟩ := by
  change some (row .high) = _
  rw [row_exact]
  rfl

theorem reversed_error :
    validate read 2 0 (.node 1 [.node 3 [],.node 2 []]) =
      .error (.child 0 0 (.wrongKey 1 2 3)) := by
  simp [validate,read_root,read_low,GeneralOrderedDictionaryCheck309.ordered]

theorem duplicate_error :
    validate read 2 0 (.node 1 [.node 2 [],.node 2 []]) =
      .error (.child 0 1 (.wrongKey 2 3 2)) := by
  simp [validate,read_root,read_low,read_high,GeneralOrderedDictionaryCheck309.ordered]

theorem truncated_error :
    validate read 2 0 (.node 1 [.node 2 []]) = .error (.wrongArity 0 2 1) := by
  simp [validate,read_root]

theorem short_fuel :
    validate read 1 0 payload = .error (.child 0 0 (.fuel 1)) := by
  simp [validate,read_root,GeneralOrderedDictionaryCheck309.ordered]

end Yulang.GeneralPositiveForkCheck309
