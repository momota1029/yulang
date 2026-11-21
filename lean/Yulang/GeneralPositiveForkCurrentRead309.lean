import Yulang.GeneralPositiveForkBefore309
import Yulang.GeneralPositiveForkAddresses309

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 15500000
namespace Yulang.GeneralPositiveForkCurrentRead309
open GeneralPositiveForkSource309 (initial compiled registry root)
open GeneralPositiveForkInstall309 (after raw_sites models)
open GeneralPositiveForkNodes309 (Node focus key links)
open GeneralPositiveForkMachine309 (all_reachable distinct)
open GeneralPositiveForkCompiler309 (lookup row row_exact read encode)
open GeneralPositiveForkCheck309 (read_root read_low read_high accepted)
open GeneralPositiveForkEvidence309 (payload)
open GeneralPositiveForkBefore309 (no_root_evidence)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralGeneratedDictionaryRun299 (Read run collect Entry)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralOrderedDictionaryCheck309 (validate)
open GeneralDeclarationExamples (roles)
open GeneralSourceDictionaries (Occurrence)

def recorded (s : State roles) (o : Occurrence roles) : Bool :=
  s.core.erased.current.sites.any fun site => site.occurrence.identity == o.identity

/-- Fixed fork frontend. Even if a parent report predicts a child, that
child's row is not supplied until its actual occurrence is registered. -/
def readAt (s : State roles) : Read := fun i => do
  let n ← lookup i
  if recorded s (focus n) then some (row n) else none

theorem initial_seen :
    recorded initial (focus .parent) = true ∧
    recorded initial (focus .low) = false ∧ recorded initial (focus .high) = false := by
  constructor
  · rfl
  · constructor <;> decide +kernel

theorem after_seen (n : Node) : recorded after (focus n) = true := by
  unfold recorded
  rw [raw_sites]
  cases n <;> decide +kernel

theorem initial_root : readAt initial 0 = some ⟨1,[1,2]⟩ := by
  have t : readAt initial 0 = read 0 := by
    change (if recorded initial (focus .parent) then some (row .parent) else none) = _
    rw [initial_seen.1]
    rfl
  exact t.trans read_root

theorem initial_low : readAt initial 1 = none := by
  change (if recorded initial (focus .low) then some (row .low) else none) = _
  rw [initial_seen.2.1]
  rfl

theorem initial_high : readAt initial 2 = none := by
  change (if recorded initial (focus .high) then some (row .high) else none) = _
  rw [initial_seen.2.2]
  rfl

theorem after_table : readAt after = read := by
  funext i
  cases hit : lookup i with
  | none => simp [readAt,GeneralPositiveForkCompiler309.read,hit]
  | some n => simp [readAt,GeneralPositiveForkCompiler309.read,hit,after_seen]

theorem initial_child_fails (fuel : Nat) : run (readAt initial) fuel 1 = none := by
  cases fuel <;> simp [run,initial_low]

theorem initial_compilation (fuel : Nat) : run (readAt initial) fuel 0 = none := by
  cases fuel with
  | zero => rfl
  | succ n =>
    simp [run,initial_root,collect,initial_child_fails]

theorem initial_error :
    validate (readAt initial) 2 0 payload = .error (.child 0 0 (.missing 1)) := by
  simp [validate,initial_root,initial_low,GeneralOrderedDictionaryCheck309.ordered]

theorem actual_exact (s : State roles) (reached : B4Target.Steps (Step compiled root) initial s)
    (m : Assignment) (valid : Models s m) (fuel : Nat) (d : Payload) :
    validate (readAt s) fuel 0 d = .ok () ↔ 2 ≤ fuel ∧
      (boundary roles).Evidence registry s m root d := by
  rcases all_reachable s reached with rfl|rfl
  · rw [GeneralOrderedDictionaryCheck309.exact,initial_compilation]
    constructor
    · intro h; cases h
    · intro h; exact False.elim (no_root_evidence m d h.2)
  · rw [after_table,accepted]
    exact and_congr_right (fun _ => (GeneralPositiveForkPayload309.iff_expected .parent m valid d).symm)

theorem one_install_unlocks (m : Assignment) (valid : Models initial m) :
    (∀ f d, validate (readAt initial) f 0 d ≠ .ok ()) ∧
    validate (readAt after) 2 0 payload = .ok () ∧
    (boundary roles).Evidence registry after m root payload := by
  refine ⟨?_,?_,GeneralPositiveForkEvidence309.root_evidence m ((models _).mpr valid)⟩
  · intro f d bad
    have h := (GeneralOrderedDictionaryCheck309.exact ..).mp bad
    rw [initial_compilation] at h
    cases h
  · rw [after_table]
    exact (accepted 2 payload).mpr ⟨by decide,rfl⟩

end Yulang.GeneralPositiveForkCurrentRead309
