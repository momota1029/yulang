import Yulang.GeneralDictionarySemanticCollapse
import Yulang.GeneralDictionaryCaptureSemanticCollapse

/-! Connect actual depth-two reinspection to the existing merge allocator.
Repeated point-valued leaf observations can have different source identities.
Their semantic equality follows from old ProjectionModels, not an endpoint-ID
hypothesis. The old private propagation and current base Models then suffice
for singleton allocation and its semantic endpoints. -/
namespace Yulang.GeneralDictionarySemanticCollapseAllocation
open GeneralDictionarySemanticCollapse GeneralNominalReobservationSteps
open GeneralNominalRecursiveInspection GeneralNominalAllocation
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {state : GeneralNominalSaturationState.State roles}
variable {revision : Revision state}

abbrev firstPair (s : Shape revision) : GeneralSourceState.Interval :=
 (state.context.state.base.source s.first.1,state.context.state.base.source s.first.2)
abbrev lastPair (s : Shape revision) : GeneralSourceState.Interval :=
 (state.context.state.base.source s.last.1,state.context.state.base.source s.last.2)

theorem point_leaf_equivalent (s : Shape revision)
    (model : GeneralNominalCommonBridge.Assignment)
    (old : ProjectionModels state.context.state
      (inspect state.context.state (query s) (s.root,s.root) none) model)
    (firstPoint : s.first.1 = s.first.2) (lastPoint : s.last.1 = s.last.2) :
    Equivalent (model (firstPair s).1).1 (model (lastPair s).1).1 ∧
    Equivalent (model (firstPair s).2).1 (model (lastPair s).2).1 := by
  rw [before_exact] at old
  obtain ⟨actual,seen⟩ := (old.1 (leaf s,s.first) (by simp [beforeReport])).1
  have f := (old.1 (leaf s,s.first) (by simp [beforeReport])).2 actual seen
  have l := (old.1 (leaf s,s.last) (by simp [beforeReport])).2 actual seen
  change GeneralNominalCaptureMerges.Fits model (firstPair s) actual at f
  change GeneralNominalCaptureMerges.Fits model (lastPair s) actual at l
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · exact subtype_trans f.1 (by simpa only [lastPair, ← lastPoint] using l.2)
  · exact subtype_trans l.1 (by simpa only [firstPair, ← firstPoint] using f.2)
  · exact subtype_trans (by simpa only [firstPair, firstPoint] using f.1) l.2
  · exact subtype_trans (by simpa only [lastPair, lastPoint] using l.1) f.2

theorem current_propagation (s : Shape revision) (registry : GeneralDeclarations.Registry)
    (invocation : Nat) (declaration : GeneralDeclarations.Declaration)
    (model : GeneralNominalCommonBridge.Assignment)
    (names : declaration.inputNames = [s.binder])
    (old : GeneralNominalState.Models (propagate state.context.state registry invocation declaration
      (bindings state.context.state (inspect state.context.state (query s) (s.root,s.root) none))) model)
    (current : GeneralNominalState.Models revision.snapshot model) :
    GeneralNominalState.Models (propagate revision.snapshot registry invocation declaration
      (bindings revision.snapshot (inspect revision.snapshot (query s) (s.root,s.root) none))) model := by
  rw [bindings_before] at old
  rw [bindings_after]
  exact GeneralDictionaryCaptureSemanticCollapse.propagation state.context.state revision.snapshot registry
    invocation declaration s.binder (firstPair s) (lastPair s) model names old current

theorem capture_endpoints (s : Shape revision) (registry : GeneralDeclarations.Registry)
    (invocation : Nat) (declaration : GeneralDeclarations.Declaration)
    (model : GeneralNominalCommonBridge.Assignment)
    (declared : s.binder ∈ declaration.inputNames)
    (old : ProjectionModels state.context.state
      (inspect state.context.state (query s) (s.root,s.root) none) model)
    (firstPoint : s.first.1 = s.first.2) (lastPoint : s.last.1 = s.last.2)
    (propagated : GeneralNominalState.Models (propagate state.context.state registry invocation declaration
      (bindings state.context.state (inspect state.context.state (query s) (s.root,s.root) none))) model) :
    let before := capture state.context.state registry invocation declaration.id
      (bindings state.context.state (inspect state.context.state (query s) (s.root,s.root) none))
    let after := capture revision.snapshot registry invocation declaration.id
      (bindings revision.snapshot (inspect revision.snapshot (query s) (s.root,s.root) none))
    Equivalent (model (before.inputs s.binder).1).1 (model (after.inputs s.binder).1).1 ∧
    Equivalent (model (before.inputs s.binder).2).1 (model (after.inputs s.binder).2).1 := by
  have equal := point_leaf_equivalent s model old firstPoint lastPoint
  dsimp only
  rw [bindings_before,bindings_after]
  rw [bindings_before] at propagated
  have result := GeneralDictionaryCaptureSemanticCollapse.endpoints state.context.state registry invocation
    declaration s.binder (firstPair s) (lastPair s) model declared propagated equal.1 equal.2
  simpa [capture,occurrences,firstPair,lastPair] using result
end Yulang.GeneralDictionarySemanticCollapseAllocation
