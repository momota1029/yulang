import Yulang.GeneralGeneratedMixedCurrentNodes299
import Yulang.GeneralRebasePackedNodeCompose298
import Yulang.GeneralRebaseGeneratedCurrent298

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 9500000
namespace Yulang.GeneralGeneratedDisplayTable299
open GeneralNominalExamples (registry model displayRoot displayChild)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (Models State)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseCompiledDisplay277 (after)
open GeneralGeneratedDictionaryRun299
open GeneralGeneratedDictionaryScope299
open GeneralGeneratedDictionaryNodes299 (Nodes)
open B4TargetV8

def table : Read
  | 0 => some ⟨1,[1]⟩
  | 1 => some ⟨3,[]⟩
  | _ => none

def decode : Nat → GeneralSourceDictionaries.Occurrence roles
  | 1 => displayChild
  | _ => displayRoot

def rank : Nat → Nat
  | 0 => 1
  | _ => 0

theorem rows (x : Nat) (row : Entry) (hit : table x = some row) :
    (x = 0 ∧ row = ⟨1,[1]⟩) ∨ (x = 1 ∧ row = ⟨3,[]⟩) := by
  cases x with
  | zero => exact .inl ⟨rfl,(Option.some.inj hit).symm⟩
  | succ x =>
    cases x with
    | zero => exact .inr ⟨rfl,(Option.some.inj hit).symm⟩
    | succ x => cases hit

theorem ranked : Ranked table rank := by
  intro x row hit c member
  rcases rows x row hit with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · cases List.mem_singleton.mp member
    decide
  · cases member

theorem closed : Closed table := by
  intro x row hit c member
  rcases rows x row hit with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · cases List.mem_singleton.mp member
    exact ⟨_,rfl⟩
  · cases member

theorem faithful : Faithful (b:=boundary roles) (r:=registry) (s:=after) table decode := by
  intro x row hit
  rcases rows x row hit with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact GeneralRebaseCompiledSelection277.picked_parent
  · exact GeneralRebaseCompiledSelection277.picked_child

theorem in_scope : InScope (boundary roles) registry after displayRoot table decode := by
  intro x row hit
  rcases rows x row hit with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨.inl rfl,GeneralRebaseCompiledStable277.stable_parent⟩
  · exact ⟨.inr GeneralRebasePackedNonleaf298.actual_generated.2,GeneralRebaseCompiledStable277.stable_child⟩

theorem nodes : Nodes (boundary roles) registry after table decode := by
  intro x row hit m held ds childEvidence
  rcases rows x row hit with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact GeneralRebaseCompiledEvidenceAt277.evidenceAt m held displayRoot 1 [displayChild] ds
      (.inl rfl) GeneralRebaseCompiledStable277.stable_parent
      (by intro d q; cases List.mem_singleton.mp q; exact GeneralRebaseCompiledStable277.stable_child)
      GeneralRebaseCompiledSelection277.picked_parent childEvidence
  · exact GeneralNominalVersionedMixedStableEvidence235.selected_node
      GeneralRebaseCompiledStable277.stable_child
      GeneralRebaseGeneratedCurrent298.installable_but_committed.1 rfl
      (GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp GeneralRebaseCompiledSelection277.picked_child)
      held childEvidence

theorem computed_child : run table 1 1 = some (.node 3 []) := rfl

theorem computed_root : run table 2 0 = some (.node 1 [.node 3 []]) := rfl

theorem insufficient : run table 1 0 = none := rfl

theorem actual_result :
    Reachable (boundary roles) registry displayRoot after ∧
    Classify (boundary roles) registry after displayRoot (.selected (.node 1 [.node 3 []])) ∧
    ∀ m, Models after m → (boundary roles).Evidence registry after m displayRoot (.node 1 [.node 3 []]) :=
  ⟨GeneralRebaseCompiledInstall277.reachable,classifies _ _ faithful _ _ _ computed_root,
    fun m h => GeneralGeneratedDictionaryNodes299.same_model _ _ nodes m h _ _ _ computed_root⟩

end Yulang.GeneralGeneratedDisplayTable299
