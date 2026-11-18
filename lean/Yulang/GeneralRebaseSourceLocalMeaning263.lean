import Yulang.GeneralRebaseSourceLocalHeads263
import Yulang.GeneralRebaseSourceMeaning263
namespace Yulang.GeneralRebaseSourceLocalMeaning263
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceState (Output)
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseSourceRepresentatives263 (Path RegisteredAt)
open GeneralRebaseSourceLocalHeads263 (RepresentativeHeads)
open GeneralRebaseUniversalObserver263 (Current run)
open GeneralRebaseMultiSource263 (selected)

/-- Head-only support is restricted to finitely chosen representative snapshots
and the inspector image, not all possible alternate source futures. It remains
an explicit semantic premise, not a consequence of source checking. -/
def Context (base : Assignment → Prop) (registry : GeneralDeclarations.Registry)
 (root : GeneralSourceDictionaries.Occurrence roles) (start : State roles)
 (inhabited : ∃ owner plan, RegisteredAt registry root start owner plan)
 (owners : List Nat) {pool : List Output} (inspect : Current owners pool → State roles)
 (assignment : Assignment) : Prop :=
 base assignment ∧ RepresentativeHeads registry root start inhabited owners assignment ∧
 ∀ state, GeneralRebaseSourceCenters263.Heads (inspect state) assignment

/-- Nonempty source families have a fixed, source-derived fact interpretation.
Both interpretation and finite addresses precede the base and inspector choices.
The local head context contains no ClassEffects assumption. -/
theorem source_certificate (registry : GeneralDeclarations.Registry)
 (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
 (root : GeneralSourceDictionaries.Occurrence roles) (start : State roles)
 (source : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root start)
 (inhabited : ∃ owner plan, RegisteredAt registry root start owner plan) :
 ∃ owners : List Nat, ∃ pool : List Output, ∃ holds : Assignment → GeneralRebaseStep258.Fact → Prop,
 ∀ (base : Assignment → Prop) (inspect : Current owners pool → State roles),
 (∀ state, Path registry root start (inspect state)) →
 ∀ before after, run owners pool (fun state => (inspect state).core) (fun state => selected (inspect state)) before = .ok after →
 GeneralRebaseSourceMeaning263.Certificate owners pool holds
   (Context base registry root start inhabited owners inspect) inspect before after := by
 obtain ⟨owners,pool,bounds⟩ := GeneralRebaseMultiSource263.source_bounds registry root start source
 let representative := GeneralRebaseSourceRepresentatives263.representatives registry root start inhabited
 refine ⟨owners,pool,GeneralRebaseOwnerTable263.Holds owners representative,?_⟩
 intro base inspect reachable before after success
 apply GeneralRebaseUniversalTrace263.certificate (Context base registry root start inhabited owners inspect)
   owners pool representative (fun state => (inspect state).core) (fun state => selected (inspect state))
   (fun state => (bounds (inspect state) (reachable state)).1) _
   (fun state => (bounds (inspect state) (reachable state)).2) before after success
 intro state entry chosen assignment valid
 have listed := (bounds (inspect state) (reachable state)).1 entry chosen
 obtain ⟨plan,registered,rfl⟩ := List.mem_map.mp chosen
 exact GeneralRebaseSourceLocalHeads263.representative_compatible registry checked root start source inhabited
   owners (inspect state) (reachable state) plan registered listed assignment valid.2.1 (valid.2.2 state)

theorem global_implies_context (base : Assignment → Prop) (registry : GeneralDeclarations.Registry)
 (root : GeneralSourceDictionaries.Occurrence roles) (start : State roles)
 (inhabited : ∃ owner plan, RegisteredAt registry root start owner plan)
 (owners : List Nat) {pool : List Output} (inspect : Current owners pool → State roles)
 (reachable : ∀ state, Path registry root start (inspect state)) (assignment : Assignment)
 (valid : GeneralRebaseSourceMeaning263.Context base registry root start assignment) :
 Context base registry root start inhabited owners inspect assignment :=
 ⟨valid.1,GeneralRebaseSourceLocalHeads263.of_sourceHeads registry root start inhabited owners assignment valid.2,
   fun state => valid.2 _ (reachable state)⟩
end Yulang.GeneralRebaseSourceLocalMeaning263
