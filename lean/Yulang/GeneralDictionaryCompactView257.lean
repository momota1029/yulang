import Yulang.GeneralDictionaryOrdinaryCanonical257
import Yulang.GeneralNominalViewTypeMap255
import Yulang.GeneralNominalOrderedRawPublic256
namespace Yulang.GeneralDictionaryCompactView257
open Core.PresenceGeneration PresenceNormalForm
open GeneralNominalRebaseRawView243 (View compile)
open GeneralNominalCommonBridge (Assignment)
open GeneralPresenceIdempotentTree257 (reduce)
open GeneralDictionaryUpperHistory257 (history)
open GeneralPresenceOrderedSubstitution247 (mapping)
open GeneralPresenceOrderedBlock247 (solve)
open GeneralDictionaryLooseIterationBook240 (context atoms)
open CommonNominalFullCarrier

def expanded (n : Nat) : View := compile (context n).state (mapping (history n))
def normalized (n : Nat) : View := GeneralNominalViewTypeMap255.map reduce (expanded n)

def baseAtoms (n : Nat) : List (Atom Nat) :=
 ((context n).state.base.ordinary.map
   (GeneralNominalRebaseRawView243.atom (GeneralNominalRebaseRawView243.slot (context n).state.base (mapping (history n))))).map
     (GeneralNominalViewTypeMap255.ordinary reduce)

def compact (n : Nat) : View :=
 { normalized n with ordinary := baseAtoms n ++ GeneralDictionaryOrdinaryCanonical257.compact n }

theorem normalized_exact (n : Nat) (assignment : Assignment) :
 (normalized n).Models assignment ↔ (expanded n).Models assignment := by
 apply GeneralNominalViewTypeMap255.models_exact
 intro term _
 exact GeneralPresenceIdempotentTree257.equivalent term assignment

theorem ordinary_split (n : Nat) : (normalized n).ordinary =
 baseAtoms n ++ GeneralDictionaryOrdinaryFinite257.rewritten n := by
 change (((context n).state.base.ordinary.map _) ++ ((atoms n).map _)).map _ = _
 rw [List.map_append]
 apply congrArg (fun tail => baseAtoms n ++ tail)
 rw [List.map_map]
 apply List.map_congr_left
 intro value _
 cases value <;> rfl

theorem compact_exact (n : Nat) (assignment : Assignment) :
 (compact n).Models assignment ↔ (expanded n).Models assignment := by
 apply Iff.trans _ (normalized_exact n assignment)
 unfold View.Models
 apply and_congr _ Iff.rfl
 change All model assignment (baseAtoms n ++ GeneralDictionaryOrdinaryCanonical257.compact n) ↔
   All model assignment (normalized n).ordinary
 rw [ordinary_split,all_append,all_append]
 exact and_congr Iff.rfl (GeneralDictionaryOrdinaryCanonical257.exact n assignment)

theorem compact_solved (n : Nat) (assignment : Assignment) :
 (compact n).Models assignment ↔ GeneralNominalState.Models (context n).state
   (solve model (history n) assignment) :=
 (compact_exact n assignment).trans (GeneralNominalOrderedRawPublic256.compiled_solved ..)

theorem recovered (n : Nat) (assignment : Assignment)
 (valid : All model assignment (GeneralPresenceDefinitionRewrite244.block (history n))) :
 (compact n).Models assignment ↔ GeneralNominalState.Models (context n).state assignment :=
 (compact_exact n assignment).trans (GeneralNominalOrderedRawPublic256.recovered _ _ assignment valid)

def hidden (n : Nat) : List Nat := (history n).map Prod.fst

theorem public_models (n : Nat) (boundary : Assignment) :
 (∃ assignment, GeneralNominalRebasePublicModel242.PublicAgree (hidden n) assignment boundary ∧
   GeneralNominalState.Models (context n).state assignment) ↔
 (∃ assignment, GeneralNominalRebasePublicModel242.PublicAgree (hidden n) assignment boundary ∧
   (compact n).Models assignment) := by
 rw [GeneralNominalOrderedRawPublic256.public_models (context n).state (history n)
   (GeneralDictionaryUpperHistory257.block_in_source n) (hidden n)
   (fun e member => List.mem_map.mpr ⟨e,member,rfl⟩) boundary]
 apply exists_congr
 intro assignment
 exact and_congr Iff.rfl (compact_exact n assignment).symm

theorem hidden_above (n name : Nat) (member : name ∈ hidden n) : 4 < name := by
 obtain ⟨e,present,rfl⟩ := List.mem_map.mp member
 exact GeneralDictionaryUpperHistory257.targets_above n e present

theorem slot_count (n : Nat) : (compact n).slots = n+5 := rfl
end Yulang.GeneralDictionaryCompactView257
