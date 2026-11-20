import Yulang.GeneralObservedLadderLocal301
import Yulang.GeneralGeneratedFrontierReceipt299
import Yulang.GeneralGeneratedSelectedExact299
import Yulang.GeneralGeneratedDictionaryNodes299

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedLadderObserver301
open GeneralObservedLadderSource301 (snapshot)
open GeneralObservedLadderInitial301 (context)
open GeneralObservedLadderReport301
open GeneralObservedLadderRoute301 (focus)
open GeneralObservedLadderEvidence301 (final dictionary list_instance)
open GeneralNominalExamples (registry displayRoot intDisplay)
open GeneralDeclarationExamples (roles display)
open GeneralNominalRecursiveCandidates (report)
open GeneralNominalRecursiveInspection
open GeneralNominalUnaryCaptureFacts (captured)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open CommonRoleOutermostResolver (Frontier Dictionary)
open GeneralGeneratedFrontierReceipt299 (readRows translate)
open GeneralGeneratedDictionaryRun299 (Read Entry Closed Ranked)
open GeneralGeneratedDictionaryScope299 (Faithful)
open B4TargetV8 (Local Classify)

abbrev finish (r : Report s) : Bool := r.blocked.isEmpty && r.conflicts.isEmpty && r.arity.isEmpty

abbrev reject (r : Report s) : Bool := r.blocked.isEmpty && !r.conflicts.isEmpty && r.arity.isEmpty

/-- This is the inspector for the two Display alternatives in this family.
The next index comes from the actual unary capture; no raw Step is run here. -/
def lookup (n i : Nat) : Option (Frontier Nat) :=
  if bound : i ≤ n+1 then
    let cons := report (context n) display [point n i bound]
    let scalar := report (context n) intDisplay [point n i bound]
    if finish cons && reject scalar then
      match bindings (snapshot n) cons with
      | [(0,(lo,hi))] => if lo = hi then some (.selected display.id [lo]) else some .pending
      | _ => some .pending
    else if reject cons && finish scalar then some (.selected intDisplay.id [])
    else some .pending
  else none

def encode (n j : Nat) : Option Nat := if j ≤ n+1 then some j else none

def table (n : Nat) : Read := readRows (lookup n) (encode n)

theorem exact_list (n i : Nat) (bound : i ≤ n) :
    lookup n i = some (.selected 1 [i+1]) := by
  unfold lookup
  rw [dite_eq_left (show i ≤ n+1 by omega)]
  dsimp only
  rw [display_report n i bound,list_as_int n i bound]
  change (if i+1 = i+1 then some (Frontier.selected 1 [i+1]) else some (Frontier.pending : Frontier Nat)) = _
  simp

theorem exact_scalar (n : Nat) : lookup n (n+1) = some (.selected 3 []) := by
  unfold lookup
  rw [dite_eq_left (Nat.le_refl (n+1))]
  dsimp only
  rw [int_as_list,int_report]
  rfl

theorem absent (n i : Nat) (outside : n+1 < i) : lookup n i = none :=
  dite_eq_right (Nat.not_le_of_gt outside)

theorem observed (n i : Nat) (f : Frontier Nat) (found : lookup n i = some f) :
    Local (boundary roles) registry (final n).state (focus n i) (translate (focus n) f) := by
  by_cases inner : i ≤ n
  · rw [exact_list n i inner] at found
    cases Option.some.inj found
    exact GeneralObservedLadderLocal301.list_local n i inner
  by_cases last : i = n+1
  · subst i
    rw [exact_scalar] at found
    cases Option.some.inj found
    exact GeneralObservedLadderLocal301.leaf_local n
  rw [absent n i (by omega)] at found
  cases found

theorem roundtrip (n j i : Nat) (h : encode n j = some i) : focus n i = focus n j := by
  unfold encode at h
  split at h
  · cases Option.some.inj h
    rfl
  · cases h

theorem faithful (n : Nat) :
    Faithful (b:=boundary roles) (r:=registry) (s:=(final n).state) (table n) (focus n) :=
  GeneralGeneratedFrontierReceipt299.faithful _ _ _ _ (observed n) (roundtrip n)

theorem branch (n i : Nat) (inner : i ≤ n) : table n i = some ⟨1,[i+1]⟩ := by
  unfold table readRows GeneralGeneratedFrontierReceipt299.compile
  rw [exact_list n i inner]
  simp [GeneralGeneratedFrontierReceipt299.indices,encode,show i+1 ≤ n+1 by omega]

theorem leaf (n : Nat) : table n (n+1) = some ⟨3,[]⟩ := by
  unfold table readRows GeneralGeneratedFrontierReceipt299.compile
  rw [exact_scalar]
  rfl

theorem out_of_range (n i : Nat) (outside : n+1 < i) : table n i = none := by
  unfold table readRows GeneralGeneratedFrontierReceipt299.compile
  rw [absent n i outside]

theorem entries (n i : Nat) (e : Entry) (hit : table n i = some e) :
    (i ≤ n ∧ e = ⟨1,[i+1]⟩) ∨ (i = n+1 ∧ e = ⟨3,[]⟩) := by
  by_cases inner : i ≤ n
  · exact .inl ⟨inner,(Option.some.inj ((branch n i inner).symm.trans hit)).symm⟩
  by_cases last : i = n+1
  · subst i
    exact .inr ⟨rfl,(Option.some.inj ((leaf n).symm.trans hit)).symm⟩
  rw [out_of_range n i (by omega)] at hit
  cases hit

theorem closed (n : Nat) : Closed (table n) := by
  intro i row seen child hit
  rcases entries n i row seen with ⟨bound,rfl⟩|⟨_,rfl⟩
  · cases List.mem_singleton.mp hit
    by_cases inner : i+1 ≤ n
    · exact ⟨_,branch n (i+1) inner⟩
    · have last : i+1 = n+1 := by omega
      rw [last]
      exact ⟨_,leaf n⟩
  · cases hit

theorem rank (n : Nat) : Ranked (table n) (fun i => n+1-i) := by
  intro i row seen child hit
  rcases entries n i row seen with ⟨bound,rfl⟩|⟨_,rfl⟩
  · cases List.mem_singleton.mp hit
    change n+1-(i+1) < n+1-i
    omega
  · cases hit

theorem known (n : Nat) :
    GeneralGeneratedDictionaryRankCheck299.Known (table n) (List.range (n+2)) := by
  intro i row seen
  apply List.mem_range.mpr
  rcases entries n i row seen with ⟨inner,_⟩|⟨last,_⟩ <;> omega

theorem exact_on_present (n i : Nat) {row : Entry} (hit : table n i = some row)
    (d : Dictionary) :
    GeneralGeneratedDictionaryRun299.run (table n) (n+2) i = some d ↔
      Classify (boundary roles) registry (final n).state (focus n i) (.selected d) := by
  have eq := GeneralGeneratedSelectedExact299.bounded_exact (b:=boundary roles) (r:=registry) (s:=(final n).state)
    (table n) (focus n) (faithful n) (closed n) (List.range (n+2)) (known n) i hit d
  rwa [List.length_range] at eq

end Yulang.GeneralObservedLadderObserver301
