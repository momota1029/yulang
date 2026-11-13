import Yulang.GeneralNominalReportEnumeration
import Yulang.GeneralNominalSharedBudget

/-! A snapshot-free code for exact semantic deltas and literal child edges.
The source seed and interpretation are supplied once by the initial context. -/
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralNominalPacketCodes
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalReportErasure GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)

structure Code (registry : Registry) (roles : Roles.RoleDecls) where
  parent : Occurrence roles
  declaration : Declaration
  checked : DeclarationChecked registry.constructors roles declaration
  data : Data

def encode (packet : Packet roles) : Code packet.registry roles :=
  ⟨packet.site.occurrence,packet.declaration,packet.checked,
    erase packet.context.state (GeneralNominalPacketSupport.report packet)⟩

def capture (context : GeneralNominalCandidates.Context) (code : Code registry roles) :=
  GeneralNominalAllocation.capture context.state registry code.parent.identity code.declaration.id code.data.bindings

def schema (context : GeneralNominalCandidates.Context) (code : Code registry roles) :=
  GeneralNominalMaterialization.generated context.state context.interpretation
    (GeneralNominalMaterialization.requests context.state registry code.parent code.declaration code.checked code.data.bindings)

def delta (context : GeneralNominalCandidates.Context) (code : Code registry roles) (model : Assignment) : Prop :=
  (GeneralNominalAllocation.Compatible code.data.bindings model ∧
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges context.state registry code.parent.identity code.declaration code.data.bindings) ∧
    PresenceNormalForm.All CommonNominalFullCarrier.model model code.data.selfChecks) ∧
  code.data.Projections model ∧ code.data.Materialized code.declaration (capture context code) (schema context code) model

def signature (context : GeneralNominalCandidates.Context) (code : Code registry roles) : GeneralNominalSharedBudget.Signature roles :=
  ⟨code.parent,GeneralNominalAllocation.children context.state registry code.parent code.declaration code.checked code.data.bindings,
    delta context code⟩

theorem capture_seed (first last : GeneralNominalState.State) (same : first.seed = last.seed)
    (registry : Registry) (parent key : Nat) (bindings : GeneralNominalAllocation.Bindings) :
    GeneralNominalAllocation.capture first registry parent key bindings =
      GeneralNominalAllocation.capture last registry parent key bindings := by
  simp only [GeneralNominalAllocation.capture,GeneralNominalAllocation.source,same]

theorem allocation_seed (first last : GeneralNominalState.State) (same : first.seed = last.seed)
    (registry : Registry) (parent key : Nat) :
    GeneralNominalAllocation.allocation (roles := roles) first registry parent key =
      GeneralNominalAllocation.allocation last registry parent key := by
  funext clause
  simp only [GeneralNominalAllocation.allocation,GeneralNominalAllocation.source,same]

theorem frame_seed (first last : GeneralNominalState.State) (same : first.seed = last.seed)
    (registry : Registry) (parent : Nat) (bindings : GeneralNominalAllocation.Bindings) :
    GeneralNominalAllocation.frame (roles := roles) first registry parent bindings =
      GeneralNominalAllocation.frame last registry parent bindings := by
  simp only [GeneralNominalAllocation.frame,capture_seed first last same,allocation_seed first last same,
    GeneralNominalAllocation.source,same]

theorem merges_seed (first last : GeneralNominalState.State) (same : first.seed = last.seed)
    (registry : Registry) (parent : Nat) (declaration : Declaration) (bindings : GeneralNominalAllocation.Bindings) :
    GeneralNominalAllocation.merges first registry parent declaration bindings =
      GeneralNominalAllocation.merges last registry parent declaration bindings := by
  simp only [GeneralNominalAllocation.merges,capture_seed first last same]

theorem requests_seed (first last : GeneralNominalState.State) (same : first.seed = last.seed)
    (registry : Registry) (parent : Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration) (bindings : GeneralNominalAllocation.Bindings) :
    GeneralNominalMaterialization.requests first registry parent declaration checked bindings =
      GeneralNominalMaterialization.requests last registry parent declaration checked bindings := by
  simp only [GeneralNominalMaterialization.requests,capture_seed first last same,allocation_seed first last same]

theorem encode_represents (context : GeneralNominalCandidates.Context) (packet : Packet roles)
    (seed : context.state.seed = packet.context.state.seed)
    (constructors : context.state.constructors = packet.context.state.constructors)
    (interpretation : context.interpretation = packet.context.interpretation) :
    GeneralNominalSharedBudget.Represents (signature context (encode packet)) packet := by
  have bindings : (encode packet).data.bindings = packet.bindings := bindings_exact _ _
  refine ⟨rfl,?_,?_⟩
  · change GeneralNominalAllocation.children context.state packet.registry packet.site.occurrence
        packet.declaration packet.checked (encode packet).data.bindings = packet.children
    rw [bindings]
    unfold GeneralNominalAllocation.children Packet.children
    rw [frame_seed context.state packet.context.state seed]
    rfl
  · intro model
    rw [packet_delta_exact]
    change delta context (encode packet) model ↔ _
    unfold delta capture schema
    rw [bindings,merges_seed context.state packet.context.state seed,
      capture_seed context.state packet.context.state seed,
      requests_seed context.state packet.context.state seed]
    simp only [GeneralNominalMaterialization.generated,constructors,interpretation]
    simp only [encode]
    rw [checks_exact]
    rfl

def codes (context : GeneralNominalCandidates.Context) (registry : Registry)
    (checked : ∀ declaration ∈ registry.declarations, DeclarationChecked registry.constructors roles declaration)
    (parents : List (Occurrence roles)) (sources : List Nat) : List (Code registry roles) :=
  parents.flatMap fun parent => registry.declarations.attach.flatMap fun declaration =>
    (GeneralNominalReportEnumeration.reports sources
      (GeneralNominalInspection.queries context.state context.interpretation declaration.val)
      (roles parent.demand.role).arity).map fun data =>
        ⟨parent,declaration.val,checked declaration.val declaration.property,data⟩

theorem locate_length (base : GeneralSourceState.State) (inputs : List GeneralSourceState.Interval)
    (bounds : List (Fin base.slots × Fin base.slots))
    (located : GeneralCandidateBoundaryParts.locate base inputs = some bounds) : bounds.length = inputs.length := by
  unfold GeneralCandidateBoundaryParts.locate at located
  have general {α β : Type} (f : α → Option β) (xs : List α) (ys : List β)
      (found : xs.mapM f = some ys) : ys.length = xs.length := by
    induction xs generalizing ys with
    | nil => simp at found; subst ys; rfl
    | cons head tail ih =>
      cases first : f head <;> simp only [List.mapM_cons,first,Option.bind_none,Option.bind_some] at found
      · cases found
      · cases rest : tail.mapM f <;> simp only [rest,Option.map_none,Option.map_some] at found
        · cases found
        · cases Option.some.inj found
          exact congrArg Nat.succ (ih _ rest)
  exact general _ inputs bounds located

theorem encoded_member (context : GeneralNominalCandidates.Context) (packet : Packet roles)
    (checked : ∀ declaration ∈ packet.registry.declarations, DeclarationChecked packet.registry.constructors roles declaration)
    (parent : packet.site.occurrence ∈ parents) (visible : packet.declaration ∈ packet.registry.declarations)
    (located : GeneralNominalRecursiveCandidates.arguments packet.context packet.site.occurrence = some packet.bounds)
    (supported : ∀ slot, packet.context.state.base.source slot ∈ sources)
    (constructors : context.state.constructors = packet.context.state.constructors)
    (interpretation : context.interpretation = packet.context.interpretation) :
    encode packet ∈ codes context packet.registry checked parents sources := by
  have report := GeneralNominalReportEnumeration.report_enumerated packet.context packet.declaration packet.bounds supported
  have length : packet.bounds.length = (roles packet.site.occurrence.demand.role).arity := by
    have length := locate_length packet.context.state.base (List.ofFn packet.site.occurrence.demand.arguments) packet.bounds located
    simpa only [List.length_ofFn] using length
  have queries : GeneralNominalInspection.queries context.state context.interpretation packet.declaration =
      GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration := by
    simp only [GeneralNominalInspection.queries,constructors,interpretation]
  rw [length,← queries] at report
  exact List.mem_flatMap.mpr ⟨packet.site.occurrence,parent,List.mem_flatMap.mpr
    ⟨⟨packet.declaration,visible⟩,List.mem_attach ..,List.mem_map.mpr ⟨_,report,rfl⟩⟩⟩

end Yulang.GeneralNominalPacketCodes
