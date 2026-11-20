import Yulang.GeneralDepthTwoFinalSelection300
import Yulang.GeneralGeneratedSelectedExact299
import Yulang.GeneralGeneratedFrontierReceipt299
import Yulang.GeneralGeneratedDictionaryNodes299

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34000
set_option maxHeartbeats 14000000
namespace Yulang.GeneralDepthTwoObserved300
open GeneralGeneratedNestedSource299 (root)
open GeneralGeneratedNestedPredictions299 (middle terminal)
open GeneralDepthTwoSecondInstall300 (final)
open GeneralDepthTwoFinalNodes300
open GeneralDepthTwoFinalSelection300 (selected)
open GeneralNominalExamples (registry)
open GeneralDeclarationExamples (roles)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralGeneratedDictionaryRun299 (Read Entry run Closed)
open GeneralGeneratedDictionaryScope299 (Faithful)
open GeneralGeneratedDictionaryNodes299 (Nodes)
open GeneralGeneratedFrontierReceipt299
open CommonRoleOutermostResolver (Dictionary Child Frontier)
open B4TargetV8

def nodeAt : Nat → Option Node
  | 0 => some .outer
  | 1 => some .inner
  | 2 => some .leaf
  | _ => none

def encode : Node → Option Nat
  | .outer => some 0
  | .inner => some 1
  | .leaf => some 2

def decode (i : Nat) : Occurrence roles := demand ((nodeAt i).getD .outer)

def lookup (i : Nat) : Option (Frontier Node) :=
  (nodeAt i).map fun n => .selected (code n) (childNodes n)

def table : Read := readRows lookup encode

theorem roundtrip (n : Node) (i : Nat) (ok : encode n = some i) :
    decode i = demand n := by cases n <;> { cases Option.some.inj ok; rfl }

theorem observed (i : Nat) (f : Frontier Node) (hit : lookup i = some f) :
    Local (boundary roles) registry final (decode i) (translate demand f) := by
  cases i with
  | zero => cases Option.some.inj hit; exact selected .outer
  | succ i =>
    cases i with
    | zero => cases Option.some.inj hit; exact selected .inner
    | succ i =>
      cases i with
      | zero => cases Option.some.inj hit; exact selected .leaf
      | succ i => cases hit

theorem faithful : Faithful (b:=boundary roles) (r:=registry) (s:=final) table decode :=
  GeneralGeneratedFrontierReceipt299.faithful (b:=boundary roles) (r:=registry) (s:=final)
    lookup encode decode demand observed roundtrip

theorem entries (i : Nat) (e : Entry) (hit : table i = some e) :
    (i = 0 ∧ e = ⟨1,[1]⟩) ∨ (i = 1 ∧ e = ⟨1,[2]⟩) ∨ (i = 2 ∧ e = ⟨3,[]⟩) := by
  cases i with
  | zero => exact .inl ⟨rfl,(Option.some.inj hit).symm⟩
  | succ i =>
    cases i with
    | zero => exact .inr (.inl ⟨rfl,(Option.some.inj hit).symm⟩)
    | succ i =>
      cases i with
      | zero => exact .inr (.inr ⟨rfl,(Option.some.inj hit).symm⟩)
      | succ i => cases hit

theorem known : GeneralGeneratedDictionaryRankCheck299.Known table [0,1,2] := by
  intro i e hit
  rcases entries i e hit with ⟨rfl,_⟩|⟨rfl,_⟩|⟨rfl,_⟩ <;> simp

theorem closed : Closed table := by
  intro i e hit c member
  rcases entries i e hit with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · cases List.mem_singleton.mp member; exact ⟨_,rfl⟩
  · cases List.mem_singleton.mp member; exact ⟨_,rfl⟩
  · cases member

theorem nodes : Nodes (boundary roles) registry final table decode := by
  intro i row hit m valid ds childProofs
  rcases entries i row hit with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact GeneralNominalVersionedEvidence231.evidence_node
      (GeneralDepthTwoFinalParents300.root_instance m valid) childProofs
  · exact GeneralNominalVersionedEvidence231.evidence_node
      (GeneralDepthTwoFinalParents300.middle_instance m valid) childProofs
  · exact GeneralNominalVersionedEvidence231.evidence_node
      (GeneralDepthTwoEvidence300.terminal_instance m valid) childProofs

theorem computed : run table 3 0 = some (.node 1 [.node 1 [.node 3 []]]) := rfl

theorem exact_on_actual (i : Nat) (e : Entry) (hit : table i = some e) (d : Dictionary) :
    run table 3 i = some d ↔ Classify (boundary roles) registry final (decode i) (.selected d) :=
  GeneralGeneratedSelectedExact299.bounded_exact (b:=boundary roles) (r:=registry) (s:=final)
    table decode faithful closed [0,1,2] known i hit d

theorem real_terminal_graph : Acc (Child (Local (boundary roles) registry final)) root :=
  GeneralGeneratedSemanticAcc299.semantic_accessible (b:=boundary roles) (r:=registry) (s:=final)
    table decode faithful 3 0 _ computed

theorem readback (m : Assignment) (valid : Models final m) :
    (boundary roles).Evidence registry final m root (.node 1 [.node 1 [.node 3 []]]) :=
  GeneralGeneratedDictionaryNodes299.same_model (b:=boundary roles) (r:=registry) (s:=final)
    table decode nodes m valid 3 0 _ computed

end Yulang.GeneralDepthTwoObserved300
