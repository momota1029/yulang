import Yulang.GeneralRebasePrivateEvidence282

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebasePrivateStore282
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralRebaseMixedOwnedTrace277 (raw)
open GeneralRebasePrivateJournal282 (Hidden AgreeOutside)
open GeneralRebasePrivateKey282 (port)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralDictionaryReadback (Payload)
open GeneralNominalSaturationState (Packet)
open GeneralRebaseAggregateLift281 (sourceView)
open GeneralRebaseTermAggregate281 (writes)
open GeneralRebaseTermCopy281 (Write Unique Respects Copy lookup_present)
open GeneralRebasePortProjection280 (Project)
open GeneralNominalCenteredFrame179 (Agree)

def Public (seed : Nat) (names : List Nat) : Prop := ∀ id ∈ names, ¬ Hidden seed id

def Private (seed : Nat) (definition : List Write) : Prop :=
  ∀ row ∈ definition, Hidden seed row.1

theorem copy_outside (privateTargets : Private seed defs) (m : Assignment) :
    AgreeOutside seed m (Copy defs m) := by
  intro id shared
  unfold Copy
  cases h : GeneralRebaseTermCopy281.lookup defs id with
  | none => rfl
  | some term => exact False.elim (shared (privateTargets _ (lookup_present h)))

theorem row_unchanged (defs : List Write) (m : Assignment) (id : Nat) :
    (Copy defs m id).2 = (m id).2 := by
  unfold Copy
  cases GeneralRebaseTermCopy281.lookup defs id <;> rfl

theorem copy_model (privateTargets : Private seed defs) (covered : Public seed names) (m : Assignment) :
    Agree names m (Copy defs m) :=
  fun id listed => copy_outside privateTargets m id (covered id listed)

theorem copy_law (privateTargets : Private seed defs) (unique : Unique defs)
    (support : GeneralRebaseTermCopy281.Reads names defs) (covered : Public seed names) (m : Assignment) :
    Respects defs (Copy defs m) := by
  intro row used
  have expression := GeneralNominalCenteredModelExtension.type_eval_same row.2
    (fun id seen => copy_model privateTargets covered m id (support row used seen))
  rw [← expression]
  have hit := GeneralRebaseTermCopy281.lookup_exact unique used
  change CommonNominalFullCarrier.Equivalent (Copy defs m row.1).1 _
  unfold Copy
  rw [hit]
  exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

def Joint (state : State roles) (r : Registry) (root : Occurrence roles) (payload : Payload)
    (model : Assignment) : Prop :=
  Models state model ∧ GeneralNominalVersionedEvidence231.Evidence r state.core model root payload

theorem joint_iff {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}
    (reach : Reachable registry root state) {other : Registry} {focus : Occurrence roles} {payload : Payload}
    {m patched : Assignment} (same : AgreeOutside (raw state).seed m patched) :
    Joint state other focus payload m ↔ Joint state other focus payload patched :=
  and_congr (GeneralRebasePrivateJournal282.models_iff reach same)
    (GeneralRebasePrivateEvidence282.evidence_iff reach other same focus payload)

theorem projection {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}
    (reach : Reachable registry root state) (r : Registry) (focus : Occurrence roles) (payload : Payload)
    (privateTargets : Private (raw state).seed defs) (unique : Unique defs)
    (reads : GeneralRebaseTermCopy281.Reads names defs)
    (covered : Public (raw state).seed names) (shared : Public (raw state).seed observed)
    (outer : Assignment) :
    Project observed (fun m => Joint state r focus payload m ∧ Respects defs m) outer ↔
      Project observed (Joint state r focus payload) outer := by
  constructor
  · rintro ⟨m,same,valid,_⟩
    exact ⟨m,same,valid⟩
  · rintro ⟨m,same,valid⟩
    exact ⟨Copy defs m,fun id listed => (copy_model privateTargets shared m id listed).symm.trans (same id listed),
      (joint_iff reach (copy_outside privateTargets m)).mp valid,copy_law privateTargets unique reads covered m⟩

theorem packet_targets (p : Packet roles) : Private p.context.state.seed (writes p true) := by
  intro row listed
  obtain ⟨⟨binder,upper⟩,_,rfl⟩ := List.mem_map.mp listed
  exact ⟨p.site.occurrence.identity,p.declaration.id,⟨binder,upper,0⟩,rfl⟩

theorem raw_public {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}
    (reach : Reachable registry root state) : Public (raw state).seed (GeneralNominalState.sources (raw state)) := by
  intro id member
  rintro ⟨owner,decl,tag,rfl⟩
  exact GeneralRebaseFixedOrigin281.fixed_absent owner decl tag reach member

theorem packet_projection {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
    {state contextState : State roles} (reach : Reachable registry root state)
    (contextReach : Reachable registry root contextState)
    (seed : (raw contextState).seed = (raw state).seed) (p : Packet roles)
    (ctx : p.context.state = raw contextState) (r : Registry) (focus : Occurrence roles) (payload : Payload)
    (shared : Public (raw state).seed observed) (outer : Assignment) :
    Project observed (fun m => Joint state r focus payload m ∧ Respects (writes p true) m) outer ↔
      Project observed (Joint state r focus payload) outer := by
  have same := (congrArg GeneralNominalState.State.seed ctx).trans seed
  apply projection reach r focus payload (same ▸ packet_targets p)
    (GeneralRebaseTermAggregate281.unique p true) (GeneralRebaseTermAggregate281.reads p true) ?_ shared outer
  unfold sourceView
  rw [ctx,← seed]
  exact raw_public contextReach

end Yulang.GeneralRebasePrivateStore282
