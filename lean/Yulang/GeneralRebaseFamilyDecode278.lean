import Yulang.GeneralNominalPairDecode278
import Yulang.GeneralDictionaryLooseFamilyNames240
import Yulang.GeneralDictionaryVersionLoopNames238

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
namespace Yulang.GeneralRebaseFamilyDecode278
open GeneralNominalIdentities (pair source encode)
open GeneralNominalAggregateVersion231 (slot key code)
open GeneralNominalPairDecode278 (unpairCandidate originCandidate origin_roundtrip splits)
attribute [local irreducible] unpairCandidate originCandidate

inductive Style where
  | version239 | loose240
  deriving DecidableEq, Repr

def Style.seed : Style → Nat
  | .version239 => 3
  | .loose240 => 4

def Style.cap : Style → Nat → Nat
  | .version239,x => x
  | .loose240,_ => 4

def Style.bind (kind : Style) (prior : Nat) : GeneralNominalAllocation.Bindings :=
  [(0,prior,kind.cap prior),(0,prior,kind.cap prior)]

inductive Lane where
  | lower | upper
  deriving DecidableEq, Repr

def Lane.purpose : Lane → Nat
  | .lower => 0
  | .upper => 1

def allocated (kind : Style) (lane : Lane) (prior : Nat) : Nat :=
  slot kind.seed 0 0 lane.purpose 0 (kind.bind prior)

theorem pred_lt (kind : Style) (lane : Lane) (prior : Nat) : prior < allocated kind lane prior :=
  (GeneralNominalVersionedDependency236.endpoints_below_slot kind.seed 0 0 lane.purpose 0
    (kind.bind prior) (by
      change (prior,kind.cap prior) ∈ [(prior,kind.cap prior),(prior,kind.cap prior)]
      exact List.mem_cons_self)).1

theorem above (kind : Style) (lane : Lane) (prior : Nat) : kind.seed < allocated kind lane prior :=
  GeneralNominalAggregateVersion231.above_seed ..

def versionPredecessor (tag : Nat) : Nat :=
  (unpairCandidate (unpairCandidate (tag-2)).1).1

theorem version_predecessor_exact (kind : Style) (prior : Nat) :
    versionPredecessor (GeneralNominalAggregateVersion231.version (kind.bind prior) 0) = prior := by
  have tag : GeneralNominalAggregateVersion231.version (kind.bind prior) 0 - 2 =
      pair (pair prior (kind.cap prior)) (code [(prior,kind.cap prior)]) := by
    change Nat.succ (Nat.succ (pair (pair prior (kind.cap prior)) _)) - 2 = _
    rfl
  unfold versionPredecessor
  rw [tag]
  simp only [splits]

def candidate (kind : Style) (name : Nat) : Lane × Nat :=
  let origin := originCandidate (name - (kind.seed+1))
  let lane := if origin.2.2.1 = 0 then Lane.lower else Lane.upper
  (lane,versionPredecessor origin.2.2.2.2)

theorem candidate_roundtrip (kind : Style) (lane : Lane) (prior : Nat) :
    candidate kind (allocated kind lane prior) = (lane,prior) := by
  let origin := key 0 0 lane.purpose 0 (kind.bind prior)
  have codePart : allocated kind lane prior - (kind.seed+1) = encode origin := by
    change kind.seed+1+encode origin-(kind.seed+1) = encode origin
    omega
  unfold candidate
  rw [codePart,origin_roundtrip]
  change ((if lane.purpose = 0 then Lane.lower else Lane.upper),
    versionPredecessor (GeneralNominalAggregateVersion231.version (kind.bind prior) 0)) = (lane,prior)
  rw [version_predecessor_exact]
  cases lane <;> rfl

def predecessor (kind : Style) (name : Nat) : Option (Lane × Nat) :=
  let parts := candidate kind name
  if allocated kind parts.1 parts.2 = name then some parts else none

theorem predecessor_exact (kind : Style) (name : Nat) (lane : Lane) (prior : Nat) :
    predecessor kind name = some (lane,prior) ↔ allocated kind lane prior = name := by
  constructor
  · intro found
    unfold predecessor at found
    dsimp only at found
    split at found
    · rename_i sound
      exact (congrArg (fun z : Lane × Nat => allocated kind z.1 z.2) (Option.some.inj found)).symm.trans sound
    · contradiction
  · rintro rfl
    unfold predecessor
    rw [candidate_roundtrip]
    exact ite_eq_left rfl

def lowerName (kind : Style) : Nat → Nat
  | 0 => 2
  | n+1 => allocated kind .lower (lowerName kind n)

def upperName (kind : Style) (n : Nat) : Nat := allocated kind .upper (lowerName kind n)

theorem version_lower (n : Nat) : lowerName .version239 n =
    GeneralDictionaryVersionLoopNames238.lower n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [lowerName,GeneralDictionaryVersionLoopNames238.lower,ih]; rfl

theorem loose_lower (n : Nat) : lowerName .loose240 n =
    GeneralDictionaryLooseFamilyNames240.lower n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [lowerName,GeneralDictionaryLooseFamilyNames240.lower,ih]; rfl

theorem version_upper (n : Nat) : upperName .version239 n =
    GeneralDictionaryVersionLoopNames238.upper n := by
  rw [upperName,version_lower]
  rfl

theorem loose_upper (n : Nat) : upperName .loose240 n =
    GeneralDictionaryLooseFamilyNames240.upper n := by
  rw [upperName,loose_lower]
  rfl

end Yulang.GeneralRebaseFamilyDecode278
