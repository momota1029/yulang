import Yulang.GeneralRebaseFamilyRank278
import Yulang.GeneralRebaseLooseRefreshLeaf278

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseFastLooseFill278
open GeneralRebaseFamilyDecode278 (Style Lane loose_lower loose_upper)
open GeneralRebaseFamilyRank278 (rank lower_exact upper_exact)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryFamilyRecognition258 (isLower isUpper lower_iff upper_iff)
open GeneralRebaseLooseRetained278 (Settled)

def lowerFlag (name : Nat) : Bool :=
  match rank .loose240 name with
  | some (.lower,_) => true
  | _ => false

def upperFlag (name : Nat) : Bool :=
  match rank .loose240 name with
  | some (.upper,_) => true
  | _ => false

theorem lower_true (name : Nat) :
    lowerFlag name = true ↔ ∃ n, GeneralDictionaryLooseFamilyNames240.lower (n+1) = name := by
  constructor
  · intro seen
    unfold lowerFlag at seen
    split at seen
    · rename_i n yes
      have equal := (lower_exact .loose240 name n).mp yes
      rw [loose_lower] at equal
      exact ⟨n,equal⟩
    · contradiction
  · rintro ⟨n,h⟩
    have found := (lower_exact .loose240 name n).mpr (by simpa only [loose_lower] using h)
    simp [lowerFlag,found]

theorem upper_true (name : Nat) :
    upperFlag name = true ↔ ∃ n, GeneralDictionaryLooseFamilyNames240.upper n = name := by
  constructor
  · intro seen
    unfold upperFlag at seen
    split at seen
    · rename_i n yes
      have equal := (upper_exact .loose240 name n).mp yes
      rw [loose_upper] at equal
      exact ⟨n,equal⟩
    · contradiction
  · rintro ⟨n,h⟩
    have found := (upper_exact .loose240 name n).mpr (by simpa only [loose_upper] using h)
    simp [upperFlag,found]

theorem flags (name : Nat) : lowerFlag name = isLower name ∧ upperFlag name = isUpper name := by
  exact ⟨Bool.eq_iff_iff.mpr ((lower_true name).trans (lower_iff name).symm),
    Bool.eq_iff_iff.mpr ((upper_true name).trans (upper_iff name).symm)⟩

def fill (m : Assignment) (name : Nat) :=
  match rank .loose240 name with
  | some (.lower,_) => ((m 2).1,(m name).2)
  | some (.upper,_) => ((m 4).1,(m name).2)
  | none => m name

theorem fill_exact (m : Assignment) : fill m = GeneralDictionaryUniformFill258.fill m := by
  funext name
  have flags := flags name
  unfold GeneralDictionaryUniformFill258.fill
  rw [← flags.1,← flags.2]
  unfold fill lowerFlag upperFlag
  cases move : rank .loose240 name with
  | none => rfl
  | some decoded =>
    rcases decoded with ⟨role,n⟩
    cases role <;> rfl

theorem retain_models (m : Assignment) (valid : Settled m)
    (t : GeneralRebaseRoundMicro278.Tick) :
    GeneralNominalVersionedJournal232.Models (GeneralRebaseLooseMicro278.raw t) (fill m) := by
  rw [fill_exact]
  exact GeneralRebaseLooseRetained278.micro_retained m valid t

theorem retain_evidence (m : Assignment) (valid : Settled m)
    (t : GeneralRebaseRoundMicro278.Tick) :
    GeneralNominalVersionedEvidence231.Evidence GeneralDictionaryLooseLoopSource240.registry
      (GeneralRebaseLooseMicro278.raw t).core (fill m) GeneralDictionaryLooseLoopSource240.root (.node 0 []) := by
  rw [fill_exact]
  exact GeneralRebaseLooseRefreshLeaf278.retained_all_leaves m valid t

end Yulang.GeneralRebaseFastLooseFill278
