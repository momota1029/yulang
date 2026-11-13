import Yulang.GeneralNominalActualTraceSupport

/-! Literal occurrence templates are finite once installing parent identities
and source endpoints are finite. The root demand is only an identity carrier
for the child emitter; its arguments are never used by that emitter. -/
namespace Yulang.GeneralNominalOccurrenceEnumeration
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalActualInspectionSteps
open GeneralNominalInvocationAncestry GeneralNominalActualTraceSupport

theorem children_identity (state : GeneralNominalState.State) (registry : Registry)
    (first last : Occurrence roles) (same : first.identity = last.identity)
    (declaration : Declaration) (checked : DeclarationChecked constructors roles declaration)
    (bindings : GeneralNominalAllocation.Bindings) :
    GeneralNominalAllocation.children state registry first declaration checked bindings =
      GeneralNominalAllocation.children state registry last declaration checked bindings := by
  simp only [GeneralNominalAllocation.children,GeneralDictionaryEmissionPlans.children,same]

def templates (registry : Registry) (context : GeneralNominalCandidates.Context)
    (checked : ∀ declaration ∈ registry.declarations, DeclarationChecked registry.constructors roles declaration)
    (root : Occurrence roles) (parents sources : List Nat) : List (Occurrence roles) :=
  root :: parents.flatMap fun identity => registry.declarations.attach.flatMap fun declaration =>
    (GeneralNominalReportEnumeration.reports sources
      (GeneralNominalInspection.queries context.state context.interpretation declaration.val)
      (roles declaration.val.role).arity).flatMap fun data =>
        GeneralNominalAllocation.children context.state registry {root with identity := identity}
          declaration.val (checked declaration.val declaration.property) data.bindings

theorem child_enumerated (context : GeneralNominalCandidates.Context) (packet : Packet roles)
    (checked : ∀ declaration ∈ packet.registry.declarations, DeclarationChecked packet.registry.constructors roles declaration)
    (root : Occurrence roles) (parent : packet.site.occurrence.identity ∈ parents)
    (visible : packet.declaration ∈ packet.registry.declarations)
    (role : packet.declaration.role = packet.site.occurrence.demand.role)
    (located : GeneralNominalRecursiveCandidates.arguments packet.context packet.site.occurrence = some packet.bounds)
    (supported : ∀ slot, packet.context.state.base.source slot ∈ sources)
    (seed : context.state.seed = packet.context.state.seed)
    (constructors : context.state.constructors = packet.context.state.constructors)
    (interpretation : context.interpretation = packet.context.interpretation)
    (child : Occurrence roles) (member : child ∈ packet.children) :
    child ∈ templates packet.registry context checked root parents sources := by
  have report := GeneralNominalReportEnumeration.report_enumerated packet.context packet.declaration packet.bounds supported
  have length : packet.bounds.length = (roles packet.declaration.role).arity := by
    have length := GeneralNominalPacketCodes.locate_length packet.context.state.base
      (List.ofFn packet.site.occurrence.demand.arguments) packet.bounds located
    simpa only [List.length_ofFn,role] using length
  have queries : GeneralNominalInspection.queries context.state context.interpretation packet.declaration =
      GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration := by
    simp only [GeneralNominalInspection.queries,constructors,interpretation]
  rw [length,← queries] at report
  apply List.mem_cons_of_mem
  apply List.mem_flatMap.mpr
  refine ⟨packet.site.occurrence.identity,parent,List.mem_flatMap.mpr
    ⟨⟨packet.declaration,visible⟩,List.mem_attach ..,List.mem_flatMap.mpr ⟨_,report,?_⟩⟩⟩
  rw [GeneralNominalReportErasure.bindings_exact]
  rw [children_identity context.state packet.registry {root with identity := packet.site.occurrence.identity}
    packet.site.occurrence rfl]
  unfold GeneralNominalAllocation.children
  rw [GeneralNominalPacketCodes.frame_seed context.state packet.context.state seed]
  exact member

theorem checkedFor (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles)) :
    ∀ declaration ∈ registry.declarations, DeclarationChecked registry.constructors roles declaration :=
  fun declaration member => source.roles_agree ▸ checked.2 declaration member

def basis (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles)) (limit : Nat) :=
  templates registry context (checkedFor checked source) root
    (frontier registry context.state.seed root.identity limit) (pool registry context root limit)

theorem sites_enumerated (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ site ∈ state.current.sites, site.occurrence ∈ basis checked source limit := by
  induction path with
  | refl =>
    intro site member
    cases List.mem_singleton.mp member
    exact List.mem_cons_self
  | @tail before after path step ih =>
    have formed := formed_trace (.initial context source) path
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action =>
      cases action with
      | enqueue linked absent =>
        obtain ⟨site,member,same⟩ := GeneralNominalSharedSteps.generated_registered (formed_shared formed) generated
        exact False.elim (absent site member same)
      | refresh | equate | reobserve => exact ih
    | merge => exact ih
    | install packet support enabled novel guard =>
      have parent := installed_parents_finite bound path generated enabled novel guard
      have config := configuration_trace path
      rw [← enabled.1.2.1] at config
      have listed : ∀ slot, packet.context.state.base.source slot ∈ pool registry context root limit := by
        rw [enabled.1.2.1]
        exact slot_pool source bound path
      have registrySame := enabled.1.1
      have visible : packet.declaration ∈ packet.registry.declarations := by
        simpa only [registrySame] using enabled.1.2.2.2.1
      have packetChecked : ∀ declaration ∈ packet.registry.declarations,
          DeclarationChecked packet.registry.constructors roles declaration := by
        rw [registrySame]; exact checkedFor checked source
      intro site member
      change site ∈ before.current.sites ++ packet.children.map (GeneralNominalSharedEmission.childSite packet) at member
      rcases List.mem_append.mp member with old | added
      · exact ih site old
      · obtain ⟨child,present,rfl⟩ := List.mem_map.mp added
        have result := child_enumerated context packet packetChecked root parent visible
          enabled.1.2.2.2.2.1 enabled.1.2.2.2.2.2.1 listed config.1.symm config.2.1.symm config.2.2.symm child present
        simpa only [basis,registrySame,GeneralNominalSharedEmission.childSite] using result

end Yulang.GeneralNominalOccurrenceEnumeration
