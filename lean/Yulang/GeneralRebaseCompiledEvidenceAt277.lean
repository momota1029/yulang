import Yulang.GeneralRebaseCompiledStable277

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 9800000
namespace Yulang.GeneralRebaseCompiledEvidenceAt277
open GeneralNominalExamples (registry displayRoot displayChild model)
open GeneralDeclarationExamples (roles)
open GeneralRebaseCompiledDisplay277 (after)
open GeneralRebaseCompiledInstall277 (edges_eq reachable)
open GeneralRebaseCompiledEndpoint277 (generates_only)
open GeneralRebaseCompiledSelection277 (picked_parent picked_child)
open GeneralRebaseCompiledEvidence277 (parent_instance child_evidence real_nonleaf)
open GeneralRebaseCompiledStable277 (stable_parent stable_child)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedJournal232 (Models)

theorem evidenceAt : B4SkeletonV8.EvidenceAt (boundary roles) registry after displayRoot := by
 intro m models focus key children dictionaries reaches _stable _childStable selected supplied
 have scope : focus = displayRoot ∨ focus = displayChild := reaches.elim Or.inl generates_only
 rcases scope with rfl|rfl
 · have same := B4TargetV8.local_functional selected picked_parent
   cases same
   exact GeneralNominalVersionedEvidence231.evidence_node (parent_instance m models) supplied
 · have same := B4TargetV8.local_functional selected picked_child
   cases same
   cases supplied
   exact child_evidence m models

theorem generatedChildren :
 ∀ focus key children, GeneralNominalSaturationState.Generated after.core.erased.current displayRoot focus →
   Local registry after focus (.selected key children) →
   ∀ child ∈ children, GeneralNominalSaturationState.Generated after.core.erased.current displayRoot child := by
 intro focus key children reached picked child within
 rcases generates_only reached with rfl|rfl
 · cases B4TargetV8.local_functional picked picked_parent
   cases List.mem_singleton.mp within
   exact .child .root (by rw [edges_eq,GeneralRebaseDisplayFrame276.actual_edges]; exact List.mem_singleton_self _)
 · cases B4TargetV8.local_functional picked picked_child
   cases within

theorem regression :
 B4TargetV8.Reachable (boundary roles) registry displayRoot after ∧
 (boundary roles).Stable registry after displayRoot ∧ (boundary roles).Stable registry after displayChild ∧
 Local registry after displayRoot (.selected 1 [displayChild]) ∧
 Local registry after displayChild (.selected 3 []) ∧
 B4SkeletonV8.EvidenceAt (boundary roles) registry after displayRoot ∧
 ∀ m, Models after m → (boundary roles).Evidence registry after m displayRoot (.node 1 [.node 3 []]) :=
 ⟨reachable,stable_parent,stable_child,picked_parent,picked_child,
   evidenceAt,real_nonleaf⟩

end Yulang.GeneralRebaseCompiledEvidenceAt277
