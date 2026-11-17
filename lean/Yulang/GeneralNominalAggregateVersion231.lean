import Yulang.GeneralNominalAllocation

/-! I44: content-addressed observation versions for aggregate endpoint names.
This is an allocation-layer encoding, not a completed operational boundary. -/
namespace Yulang.GeneralNominalAggregateVersion231
open GeneralNominalIdentities
open GeneralNominalAllocation (Bindings occurrences origin)

def code : List GeneralSourceState.Interval → Nat
  | [] => 0
  | pair :: rest => Nat.succ (GeneralNominalIdentities.pair
      (GeneralNominalIdentities.pair pair.1 pair.2) (code rest))

theorem code_injective : Function.Injective code := by
  intro first
  induction first with
  | nil =>
    intro last equal
    cases last with
    | nil => rfl
    | cons => cases equal
  | cons head tail ih =>
    intro last equal
    cases last with
    | nil => cases equal
    | cons other rest =>
      have pairs : (pair head.1 head.2,code tail) = (pair other.1 other.2,code rest) :=
        pair_injective (Nat.succ.inj equal)
      have heads : head = other := pair_injective (congrArg Prod.fst pairs)
      have tails := ih (congrArg Prod.snd pairs)
      cases heads
      cases tails
      rfl

def version (bindings : Bindings) (name : Nat) : Nat :=
  Nat.succ (code (occurrences bindings name))

theorem version_eq_iff : version first name = version last name ↔
    occurrences first name = occurrences last name := by
  constructor
  · intro equal
    exact code_injective (Nat.succ.inj equal)
  · intro equal
    simp only [version,equal]

def key (root declaration purpose name : Nat) (bindings : Bindings) : Origin :=
  origin root declaration purpose name (version bindings name)

theorem key_eq_iff (root declaration purpose name : Nat) :
    key root declaration purpose name first = key root declaration purpose name last ↔
      occurrences first name = occurrences last name := by
  constructor
  · intro equal
    exact version_eq_iff.mp (congrArg (fun k : Origin => k.2.2.2.2) equal)
  · intro equal
    unfold key origin
    rw [version_eq_iff.mpr equal]

theorem not_legacy (root declaration purpose name : Nat) (bindings : Bindings)
    (r d p n : Nat) :
    key root declaration purpose name bindings ≠ origin r d p n 0 := by
  intro equal
  have impossible := congrArg (fun k : Origin => k.2.2.2.2) equal
  exact Nat.noConfusion impossible

def slot (seed root declaration purpose name : Nat) (bindings : Bindings) : Nat :=
  source seed (key root declaration purpose name bindings)

theorem slot_eq_iff (seed root declaration purpose name : Nat) :
    slot seed root declaration purpose name first = slot seed root declaration purpose name last ↔
      occurrences first name = occurrences last name :=
  (source_identity seed _ _).trans (key_eq_iff root declaration purpose name)

theorem above_seed (seed root declaration purpose name : Nat) (bindings : Bindings) :
    seed < slot seed root declaration purpose name bindings :=
  source_above_seed _ _

theorem not_legacy_slot (seed root declaration purpose name : Nat) (bindings : Bindings)
    (r d p n : Nat) :
    slot seed root declaration purpose name bindings ≠ source seed (origin r d p n 0) := by
  intro equal
  exact not_legacy root declaration purpose name bindings r d p n
    ((source_identity seed _ _).mp equal)

theorem distinct_purpose (seed root declaration first last name : Nat)
    (a b : Bindings) (different : first ≠ last) :
    slot seed root declaration first name a ≠ slot seed root declaration last name b := by
  intro equal
  have keys := (source_identity seed _ _).mp equal
  exact different (congrArg (fun k : Origin => k.2.2.1) keys)

end Yulang.GeneralNominalAggregateVersion231
