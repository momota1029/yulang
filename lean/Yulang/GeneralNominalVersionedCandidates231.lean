import Yulang.GeneralNominalVersionedPlans231
import Yulang.GeneralNominalCenteredHeadCandidates

/-! I44 candidate layer using versioned aggregate names consistently in
private propagation, freshness and child emission. Output requests are still
erased before head matching. This is not yet a complete successor boundary,
and no termination, twelve-law package or EvidenceNode result is asserted. -/
namespace Yulang.GeneralNominalVersionedCandidates231
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalRecursiveInspection
open GeneralNominalRecursiveCandidates (Context arguments report Metadata)

variable {roles : Roles.RoleDecls}

abbrev inputs := @GeneralNominalCenteredHeadCandidates.inputs

def privateState (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (bounds : List (GeneralNominalInspection.Bounds context.state)) : GeneralNominalState.State :=
  GeneralNominalState.extend
    (GeneralNominalVersionedAllocation231.propagate context.state registry root.identity declaration
      (bindings context.state (report context declaration bounds))) []
    (selfChecks context.state (report context declaration bounds))

def children (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) : List (Occurrence roles) :=
  GeneralNominalVersionedFrame231.children
    ⟨registry,context,GeneralNominalDemandMerging.pointSite (inputs root),declaration,checked,bounds⟩

def HeadModels (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (bounds : List (GeneralNominalInspection.Bounds context.state))
    (model : GeneralNominalCommonBridge.Assignment) : Prop :=
  GeneralNominalState.Models (privateState registry context (inputs root) declaration bounds) model ∧
    ProjectionModels context.state (report context declaration bounds) model

def Prepared (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) : Prop :=
  Metadata registry context ∧ GeneralNominalState.Linked context.state (inputs root).demand ∧
    ∃ bounds, arguments context (inputs root) = some bounds ∧
      GeneralNominalVersionedAllocation231.Fresh context.state registry root.identity
        (bindings context.state (report context declaration bounds)) ∧ Finished (report context declaration bounds) ∧
      ∃ model, HeadModels registry context root declaration bounds model

def Survivor (registry : Registry) (context : Context) (root : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles)) : Prop :=
  ¬ GeneralNominalState.RootPending context.state (inputs root).demand ∧
    ∃ declaration ∈ registry.declarations, ∃ checked : DeclarationChecked registry.constructors roles declaration,
      declaration.id = key ∧ declaration.role = root.demand.role ∧
      ∃ bounds, arguments context (inputs root) = some bounds ∧ Prepared registry context root declaration ∧
        children = GeneralNominalVersionedCandidates231.children registry context root declaration checked bounds

def Failed (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) : Prop :=
  Metadata registry context ∧
    ∃ bounds, arguments context (inputs root) = some bounds ∧
      GeneralNominalVersionedAllocation231.Fresh context.state registry root.identity
        (bindings context.state (report context declaration bounds)) ∧
      (report context declaration bounds).blocked = [] ∧ (report context declaration bounds).arity = [] ∧
      ((report context declaration bounds).conflicts ≠ [] ∨
        ¬ ∃ model, HeadModels registry context root declaration bounds model)

def InspectionPending (registry : Registry) (context : Context) (root : Occurrence roles) : Prop :=
  ¬ GeneralNominalState.RootPending context.state (inputs root).demand ∧
    ∃ declaration ∈ registry.declarations, declaration.role = root.demand.role ∧
      ¬ Failed registry context root declaration ∧ ¬ Prepared registry context root declaration

def Unique (registry : Registry) (context : Context) (root : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles)) : Prop :=
  Survivor registry context root key children ∧
    ∀ other cs, Survivor registry context root other cs → other = key ∧ cs = children

theorem inputs_idempotent (root : Occurrence roles) : inputs (inputs root) = inputs root := rfl

theorem prepared_ignores_outputs {first last : Occurrence roles} (same : inputs first = inputs last) :
    Prepared registry context first declaration ↔ Prepared registry context last declaration := by
  have identity := congrArg (fun root : Occurrence roles => root.identity) same
  simp only [Prepared,same,show first.identity = last.identity from identity,HeadModels]

theorem failed_ignores_outputs {first last : Occurrence roles} (same : inputs first = inputs last) :
    Failed registry context first declaration ↔ Failed registry context last declaration := by
  have identity := congrArg (fun root : Occurrence roles => root.identity) same
  simp only [Failed,same,show first.identity = last.identity from identity,HeadModels]

theorem survivor_ignores_outputs (first last : Occurrence roles) (same : inputs first = inputs last) :
    Survivor registry context first key kids ↔ Survivor registry context last key kids := by
  have role := congrArg (fun root : Occurrence roles => root.demand.role) same
  simp only [Survivor,same,show first.demand.role = last.demand.role from role,
    prepared_ignores_outputs same,children]

theorem survivor_children_functional (checked : Checked registry)
    (one : Survivor registry context root key first) (two : Survivor registry context root key last) : first = last := by
  obtain ⟨_,a,av,ac,ak,_,ab,al,_,ae⟩ := one
  obtain ⟨_,b,bv,bc,bk,_,bb,bl,_,be⟩ := two
  have equal := GeneralDictionaryEmissionPlans.declaration_key_unique registry checked a b av bv (ak.trans bk.symm)
  subst b
  have same := Option.some.inj (al.symm.trans bl)
  subst bb
  exact ae.trans be.symm

theorem unique_excludes_two (unique : Unique registry context root key kids)
    (one : Survivor registry context root a xs) (two : Survivor registry context root b ys)
    (different : a ≠ b) : False :=
  different ((unique.2 a xs one).1.trans (unique.2 b ys two).1.symm)

theorem private_packet_eq (packet : GeneralNominalSaturationState.Packet roles) :
    privateState packet.registry packet.context (inputs packet.site.occurrence) packet.declaration packet.bounds =
      GeneralNominalVersionedPlans231.privateState packet := rfl

theorem headModels_packet_iff (packet : GeneralNominalSaturationState.Packet roles) (model) :
    HeadModels packet.registry packet.context packet.site.occurrence packet.declaration packet.bounds model ↔
      GeneralNominalVersionedPlans231.HeadModels packet model := Iff.rfl

theorem private_models_iff (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (bounds : List (GeneralNominalInspection.Bounds context.state)) (model) :
    GeneralNominalState.Models (privateState registry context root declaration bounds) model ↔
      GeneralNominalState.Models context.state model ∧
      GeneralNominalAllocation.Compatible (bindings context.state (report context declaration bounds)) model ∧
      PresenceNormalForm.All CommonNominalFullCarrier.model model
        (GeneralNominalVersionedAllocation231.merges context.state registry root.identity declaration
          (bindings context.state (report context declaration bounds))) ∧
      PresenceNormalForm.All CommonNominalFullCarrier.model model
        (selfChecks context.state (report context declaration bounds)) := by
  unfold privateState
  rw [GeneralNominalState.extend_models,GeneralNominalVersionedAllocation231.propagate_models]
  simp only [and_assoc]

theorem private_seed (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (bounds : List (GeneralNominalInspection.Bounds context.state)) :
    (privateState registry context root declaration bounds).seed = context.state.seed := rfl

theorem inspectionPending_ignores_outputs (first last : Occurrence roles) (same : inputs first = inputs last) :
    InspectionPending registry context first ↔ InspectionPending registry context last := by
  have role := congrArg (fun root : Occurrence roles => root.demand.role) same
  simp only [InspectionPending,same,show first.demand.role = last.demand.role from role,
    prepared_ignores_outputs same,failed_ignores_outputs same]

theorem unique_ignores_outputs (first last : Occurrence roles) (same : inputs first = inputs last) :
    Unique registry context first key kids ↔ Unique registry context last key kids := by
  simp only [Unique,survivor_ignores_outputs first last same]

theorem children_identities (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) :
    (children registry context root declaration checked bounds).map Occurrence.identity =
      (GeneralNominalAllocation.children context.state registry (inputs root) declaration checked
        (bindings context.state (report context declaration bounds))).map Occurrence.identity :=
  GeneralNominalVersionedFrame231.children_identity_eq _

theorem children_roles (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (bounds : List (GeneralNominalInspection.Bounds context.state)) :
    (children registry context root declaration checked bounds).map (fun child => child.demand.role) =
      (GeneralNominalAllocation.children context.state registry (inputs root) declaration checked
        (bindings context.state (report context declaration bounds))).map (fun child => child.demand.role) :=
  GeneralNominalVersionedFrame231.children_role_eq _

end Yulang.GeneralNominalVersionedCandidates231
