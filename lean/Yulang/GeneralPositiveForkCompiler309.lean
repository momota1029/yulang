import Yulang.GeneralPositiveForkSelection309
import Yulang.GeneralGeneratedDictionaryNodes299
import Yulang.GeneralNominalVersionedMixedResolver236

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 17000000
namespace Yulang.GeneralPositiveForkCompiler309
open GeneralPositiveForkSource309 (compiled registry checked root)
open GeneralPositiveForkInstall309 (after reachable inhabited)
open GeneralPositiveForkNodes309
open GeneralPositiveForkEvidence309 (payload)
open GeneralPositiveForkPayload309 (expected)
open GeneralPositiveForkSelection309 (actual_pick)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedEvidence231 (Instance evidence_node)
open GeneralGeneratedDictionaryRun299 (Entry Read run)
open GeneralGeneratedDictionaryScope299 (Faithful)
open GeneralGeneratedDictionaryNodes299 (Nodes)
open GeneralNominalVersionedFrame231 (children)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCommonBridge (Assignment)
open CommonRoleOutermostResolver (All₂ Dictionary Tree classification)

def encode : Node → Nat | .parent => 0 | .low => 1 | .high => 2
def lookup : Nat → Option Node | 0 => some .parent | 1 => some .low | 2 => some .high | _ => none
abbrev decode (i : Nat) : Occurrence roles := focus ((lookup i).getD .parent)

def identify (o : Occurrence roles) : Nat :=
  if o.identity = (focus .parent).identity then 0
  else if o.identity = (focus .low).identity then 1 else 2

theorem exact_identity (n : Node) : identify (focus n) = encode n := by
  cases n <;> decide +kernel

theorem decode_encode (n : Node) : decode (encode n) = focus n := by cases n <;> rfl

def row (n : Node) : Entry :=
  ⟨(plan n).packet.declaration.id,(children (plan n).packet).map identify⟩

def read : Read := fun i => (lookup i).map row

theorem row_exact (n : Node) : row n = ⟨key n,(links n).map encode⟩ := by
  unfold row
  rw [child_list]
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro q _
  exact exact_identity q

theorem lookup_row (i : Nat) (e : Entry) (h : read i = some e) :
    ∃ n, i = encode n ∧ e = row n := by
  match i with
  | 0 => exact ⟨.parent,rfl,(Option.some.inj h).symm⟩
  | 1 => exact ⟨.low,rfl,(Option.some.inj h).symm⟩
  | 2 => exact ⟨.high,rfl,(Option.some.inj h).symm⟩
  | _+3 => cases h

theorem projected_children (n : Node) : (row n).children.map decode = (links n).map focus := by
  rw [row_exact]
  simp only [List.map_map]
  apply List.map_congr_left
  intro q _
  exact decode_encode q

theorem faithful : Faithful (b:=boundary roles) (r:=registry) (s:=after) read decode := by
  intro i e seen
  obtain ⟨n,rfl,rfl⟩ := lookup_row i e seen
  rw [decode_encode,projected_children]
  exact actual_pick n

theorem certificate (n : Node) (m : Assignment) (valid : Models after m) :
    Instance compiled after.core m (focus n) (key n) ((links n).map focus) := by
  cases n
  · exact ⟨_,GeneralPositiveForkEvidence309.parent_certificate m valid⟩
  · exact ⟨_,GeneralPositiveForkEvidence309.leaf_certificate .low m valid⟩
  · exact ⟨_,GeneralPositiveForkEvidence309.leaf_certificate .high m valid⟩

theorem nodes : Nodes (boundary roles) registry after read decode := by
  intro i e seen m valid ds support
  obtain ⟨n,rfl,rfl⟩ := lookup_row i e seen
  rw [decode_encode,projected_children] at *
  exact evidence_node (certificate n m valid) support

theorem all_fuel_sound (n i : Nat) (d : Dictionary) (validRun : run read n i = some d) :
    B4TargetV8.Classify (boundary roles) registry after (decode i) (.selected d) ∧
    ∀ m, Models after m → (boundary roles).Evidence registry after m (decode i) d :=
  ⟨GeneralGeneratedDictionaryScope299.classifies _ _ faithful _ _ _ validRun,
    fun m valid => GeneralGeneratedDictionaryNodes299.same_model _ _ nodes m valid _ _ _ validRun⟩

theorem root_computed : run read 2 0 = some payload := by
  simp [run,read,lookup,row_exact,links,key,GeneralGeneratedDictionaryRun299.collect,encode]
  rfl

theorem root_code_exact (n : Nat) (d : Dictionary) :
    run read n 0 = some d ↔ 2 ≤ n ∧ d = payload := by
  cases n with
  | zero => simp [run]
  | succ n => cases n with
    | zero => simp [run,read,lookup,row_exact,links,GeneralGeneratedDictionaryRun299.collect,encode]
    | succ n =>
      simp [run,read,lookup,row_exact,links,key,GeneralGeneratedDictionaryRun299.collect,encode,eq_comm]
      rfl

theorem exact_root_tree :
    GeneralNominalVersionedMixedResolver236.tree ⟨rfl,checked⟩ reachable root =
      .selected 1 [.selected 2 [],.selected 3 []] :=
  (GeneralNominalVersionedMixedResolver236.tree_exact ⟨rfl,checked⟩ reachable root _).mpr
    (.selected (actual_pick .parent)
      (.cons (.selected (actual_pick .low) .nil) (.cons (.selected (actual_pick .high) .nil) .nil)))

theorem source_evidenceAt : B4SkeletonV8.EvidenceAt (boundary roles) registry after root := by
  intro m valid f k cs ds appeared _ _ selected below
  have finite : ∃ n, f = focus n := by
    rcases appeared with rfl|child
    · exact ⟨.parent,rfl⟩
    · exact generated_nodes _ child
  obtain ⟨n,rfl⟩ := finite
  have exact := B4TargetV8.local_functional selected (actual_pick n)
  cases exact
  exact evidence_node (certificate n m valid) below

theorem nonvacuous :
    B4SkeletonV8.EvidenceAt (boundary roles) registry after root ∧
    ∃ m, Models after m ∧
      All₂ ((boundary roles).Evidence registry after m) [focus .low,focus .high] [.node 2 [],.node 3 []] ∧
      (boundary roles).Evidence registry after m root payload :=
  ⟨source_evidenceAt,_,inhabited,
    .cons (GeneralPositiveForkEvidence309.leaf_evidence .low _ inhabited)
      (.cons (GeneralPositiveForkEvidence309.leaf_evidence .high _ inhabited) .nil),
    GeneralPositiveForkEvidence309.root_evidence _ inhabited⟩

end Yulang.GeneralPositiveForkCompiler309
