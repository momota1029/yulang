import Yulang.GeneralNominalVersionedPool231
import Yulang.GeneralDictionaryOrdinaryTransport

/-! Fixed-observation revisit laws for I44 allocation. Appending ordinary
constraints/reservations/ownership does not change inspection bindings, hence
cannot manufacture a fresh content version. Repeated propagation is model-
idempotent, not syntactically idempotent. No Refresh/Reobserve transport,
operational saturation or termination theorem is claimed. -/
namespace Yulang.GeneralNominalVersionedRevisit231
open GeneralDeclarations
open GeneralNominalRecursiveInspection (bindings)
open GeneralNominalRecursiveCandidates (report)
open GeneralNominalVersionedAllocation231
open GeneralNominalAllocation (Bindings)

abbrev propagatedContext (context : GeneralNominalCandidates.Context) (registry : Registry)
    (root : Nat) (declaration : Declaration) (captured : Bindings) : GeneralNominalCandidates.Context :=
  ⟨propagate context.state registry root declaration captured,context.interpretation⟩

theorem bindings_propagate (context : GeneralNominalCandidates.Context) (registry : Registry)
    (root : Nat) (declaration : Declaration) (captured : Bindings) (inspected : Declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) :
    bindings (propagatedContext context registry root declaration captured).state
      (report (propagatedContext context registry root declaration captured) inspected bounds) =
      bindings context.state (report context inspected bounds) := by
  change bindings (GeneralDictionaryOrdinaryTransport.extendState context.state
    (reserved context.state registry root captured)
    (GeneralNominalAllocation.cross captured ++ merges context.state registry root declaration captured)
    (keys registry root captured))
    (report (GeneralDictionaryOrdinaryTransport.extend context
      (reserved context.state registry root captured)
      (GeneralNominalAllocation.cross captured ++ merges context.state registry root declaration captured)
      (keys registry root captured)) inspected bounds) = _
  rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended,
    GeneralDictionaryOrdinaryTransport.bindings_report]

theorem reinspected_keys (context : GeneralNominalCandidates.Context) (registry : Registry)
    (root : Nat) (declaration : Declaration) (captured : Bindings) (inspected : Declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) :
    keys registry root (bindings (propagatedContext context registry root declaration captured).state
      (report (propagatedContext context registry root declaration captured) inspected bounds)) =
    keys registry root (bindings context.state (report context inspected bounds)) := by
  rw [bindings_propagate]

theorem reinspected_version (context : GeneralNominalCandidates.Context) (registry : Registry)
    (root : Nat) (declaration : Declaration) (captured : Bindings) (inspected : Declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) (name : Nat) :
    GeneralNominalAggregateVersion231.version
      (bindings (propagatedContext context registry root declaration captured).state
        (report (propagatedContext context registry root declaration captured) inspected bounds)) name =
    GeneralNominalAggregateVersion231.version (bindings context.state (report context inspected bounds)) name := by
  rw [bindings_propagate]

theorem capture_propagate (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
    (declaration : Declaration) (captured next : Bindings) (key : Nat) :
    capture (propagate state registry root declaration captured) registry root key next =
      capture state registry root key next := rfl

theorem merges_propagate (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
    (declaration inspected : Declaration) (captured next : Bindings) :
    merges (propagate state registry root declaration captured) registry root inspected next =
      merges state registry root inspected next := rfl

theorem reserved_propagate (state : GeneralNominalState.State) (registry : Registry) (root : Nat)
    (declaration : Declaration) (captured next : Bindings) :
    reserved (propagate state registry root declaration captured) registry root next =
      reserved state registry root next := rfl

theorem reinspected_reserved (context : GeneralNominalCandidates.Context) (registry : Registry)
    (root : Nat) (declaration : Declaration) (captured : Bindings) (inspected : Declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) :
    reserved (propagatedContext context registry root declaration captured).state registry root
      (bindings (propagatedContext context registry root declaration captured).state
        (report (propagatedContext context registry root declaration captured) inspected bounds)) =
    reserved context.state registry root (bindings context.state (report context inspected bounds)) := by
  rw [bindings_propagate]
  rfl

/-- Repeating the same bindings adds duplicate bookkeeping/equations only.
This equality of model predicates does not claim an operational fixed point. -/
theorem propagate_models_idempotent (state : GeneralNominalState.State) (registry : Registry)
    (root : Nat) (declaration : Declaration) (captured : Bindings)
    (model : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalState.Models
      (propagate (propagate state registry root declaration captured) registry root declaration captured) model ↔
    GeneralNominalState.Models (propagate state registry root declaration captured) model := by
  rw [propagate_models,propagate_models,merges_propagate]
  exact ⟨fun held => held.1,fun held => ⟨held,held.2⟩⟩

/-- Once this exact version has been reserved, the ownership guard accepts
its revisit. This does not authorize another version or an unrelated key. -/
theorem fresh_revisit (state : GeneralNominalState.State) (registry : Registry)
    (root : Nat) (declaration : Declaration) (captured : Bindings) :
    Fresh (propagate state registry root declaration captured) registry root captured := by
  intro key member _
  exact new_allocated member

end Yulang.GeneralNominalVersionedRevisit231
