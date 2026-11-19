import Yulang.GeneralRebaseCompiledExecutor277
import Yulang.GeneralRebaseFreshSupport277

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 9900000
namespace Yulang.GeneralRebaseCompiledObservables277
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalExamples (registry state displayRoot displayChild)
open GeneralDeclarationExamples (roles)
open GeneralRebaseCompiledDisplay277 (compiled after parent)
open GeneralRebaseFreshSupport277 (oldKey original_key compiled_no_key)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralRebaseDisplayExecutor276 (Phase)
open GeneralNominalIdentities (source source_identity)
open GeneralNominalVersionedInstallation231 (allocated reserved)

noncomputable abbrev direct := GeneralRebaseDisplayFrame276.after

theorem registry_ne : compiled ≠ registry := by
  intro same
  exact compiled_no_key (same.symm ▸ original_key)

theorem legacy_core_ne : after.core ≠ direct.core := by
  intro same
  have related := congrArg (fun core : GeneralNominalCenteredSteps.State roles =>
    core.erased.current.packets.map (fun pkt => pkt.registry)) same
  change [compiled] = [registry] at related
  exact registry_ne (List.cons.inj related).1

theorem state_ne : after ≠ direct := fun same =>
  legacy_core_ne (congrArg (fun s : State roles => s.core) same)

theorem old_reserved : source (state true).seed oldKey ∈
    direct.core.erased.current.context.state.reserved := by
  change source (state true).seed oldKey ∈ reserved GeneralNominalNonleafPlan193.packet
  exact List.mem_map.mpr ⟨oldKey,(by
    change oldKey ∈ GeneralNominalVersionedAllocation231.keys registry displayRoot.identity GeneralNominalNonleafPlan193.packet.bindings
    exact (by decide +kernel)),rfl⟩

theorem compiled_reserved_absent : source (state true).seed oldKey ∉
    after.core.erased.current.context.state.reserved := by
  intro owned
  change source (state true).seed oldKey ∈ reserved parent.packet at owned
  obtain ⟨key,present,eq⟩ := List.mem_map.mp owned
  have same := (source_identity (state true).seed key oldKey).mp eq
  subst key
  have bad : oldKey ∉ allocated parent.packet := by decide +kernel
  exact bad present

theorem obs_same :
  after.core.erased.current.context.state.base = direct.core.erased.current.context.state.base ∧
  after.core.erased.current.context.state.view = direct.core.erased.current.context.state.view ∧
  after.core.erased.current.context.state.nominals = direct.core.erased.current.context.state.nominals ∧
  after.core.erased.current.context.state.ordinary = direct.core.erased.current.context.state.ordinary :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem public_ports_same :
  after.core.erased.current.sites = direct.core.erased.current.sites ∧
  after.core.sites = direct.core.sites ∧
  after.core.erased.current.edges = direct.core.erased.current.edges ∧
  ∀ m, Models after m ↔ Models direct m :=
  ⟨GeneralRebaseCompiledInstall277.raw_sites_eq,GeneralRebaseCompiledInstall277.center_sites_eq,
    GeneralRebaseCompiledInstall277.edges_eq,GeneralRebaseCompiledInstall277.direct_models⟩

end Yulang.GeneralRebaseCompiledObservables277
