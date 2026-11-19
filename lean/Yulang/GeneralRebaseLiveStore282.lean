import Yulang.GeneralRebaseLiveOwner282

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseLiveStore282
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedJournal232 (State)
open GeneralRebasePhaseKeys281 (owner)
open GeneralRebaseLiveOwner282 (newest newest_subset newest_unique same_seed)
open GeneralRebaseHistoryOrder282 (decode)
open GeneralRebaseHistorySupport282 (packet_context decode_agrees)
open GeneralRebaseWholeJournal282 (View Observable preserved_projection)
open GeneralRebaseWholeStore282 (store store_private store_unique expression_exact view_agrees)
open GeneralRebaseMixedOwnedTrace277 (raw)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralNominalIdentities (Origin source_identity)
open GeneralRebasePrivateKey282 (port)
open GeneralRebasePrivateStore282 (Public Private Joint copy_outside copy_model)
open GeneralRebaseAggregateTags281 (Tag fixedOrigin)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseTermCopy281 (Write Copy Unique Respects lookup_exact)
open GeneralRebaseTermAggregate281 (writes keys)
open GeneralRebasePortProjection280 (Project)
open GeneralDeclarations GeneralSourceDictionaries
open GeneralDictionaryReadback (Payload)
open CommonNominalFullCarrier (Equivalent model subtype_refl)

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

def live (state : State roles) : List Write := (newest state.plans).flatMap (fun p => store state p.packet)

theorem row_origin (state : State roles) (p : Plan roles) (w : Write) (found : w ∈ store state p.packet) :
    ∃ key ∈ keys p.packet, w.1 = port p.packet.context.state.seed (owner p).1 (owner p).2
      ⟨key.1,key.2,0⟩ := by
  obtain ⟨original,member,rfl⟩ := List.mem_map.mp found
  obtain ⟨key,declared,rfl⟩ := List.mem_map.mp member
  exact ⟨key,declared,rfl⟩

theorem owner_injective_on_port (seed : Nat) (a b : Nat × Nat) (first last : Tag)
    (eq : port seed a.1 a.2 first = port seed b.1 b.2 last) : a = b := by
  have collision := (source_identity _ _ _).mp eq
  exact Prod.ext (congrArg (fun k : Origin => k.1) collision)
    (congrArg (fun k : Origin => k.2.1) collision)

theorem live_private (reach : Reachable registry root state) : Private (raw state).seed (live state) := by
  intro row listed
  obtain ⟨p,ownerLatest,found⟩ := List.mem_flatMap.mp listed
  exact (same_seed reach ownerLatest) ▸ store_private state p.packet row found

theorem live_unique (reach : Reachable registry root state) : Unique (live state) := by
  intro x left y right eq
  obtain ⟨p,latestA,first⟩ := List.mem_flatMap.mp left
  obtain ⟨q,latestB,last⟩ := List.mem_flatMap.mp right
  obtain ⟨k,_,a⟩ := row_origin state p x first
  obtain ⟨l,_,b⟩ := row_origin state q y last
  have sameTarget := eq
  rw [a,b,same_seed reach latestA,same_seed reach latestB] at eq
  have same := newest_unique latestA latestB (owner_injective_on_port _ _ _ _ _ eq)
  subst q
  exact store_unique state p.packet x first y last sameTarget

theorem copy_live (reach : Reachable registry root state) (m : Assignment) : Respects (live state) (Copy (live state) m) := by
  have agree := decode_agrees reach (copy_outside (live_private reach) m)
  intro row used
  obtain ⟨p,latest,found⟩ := List.mem_flatMap.mp used
  obtain ⟨original,covered,rfl⟩ := List.mem_map.mp found
  obtain ⟨prior,path,context,seed⟩ := packet_context reach p (newest_subset _ latest)
  have reads : GeneralNominalState.typeSources original.2 ⊆ GeneralNominalState.sources p.packet.context.state :=
    GeneralRebaseTermAggregate281.reads p.packet true original covered
  have term := GeneralNominalCenteredModelExtension.type_eval_same original.2 (fun id appears => by
    apply agree
    rw [← seed]
    exact GeneralRebasePrivateStore282.raw_public path id (context ▸ reads appears))
  change Equivalent (Copy (live state) m original.1).1 _
  rw [expression_exact,← term]
  have hit := lookup_exact (live_unique reach) used
  change GeneralRebaseTermCopy281.lookup (live state) original.1 =
    some (original.2.subst (GeneralPresenceOrderedSubstitution247.mapping (GeneralRebaseHistoryOrder282.history state))) at hit
  unfold Copy
  rw [hit]
  change Equivalent ((original.2.subst _).eval model m) (original.2.eval model (decode state m))
  rw [expression_exact]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem projection (reach : Reachable registry root state) (r : Registry) (focus : Occurrence roles)
    (data : Payload) (named : Observable state names) (publicNames : Public (raw state).seed names) (m : Assignment) :
    Project names (fun v => View state r focus data v ∧ Respects (live state) v) m ↔
      Project names (Joint state r focus data) m := by
  apply Iff.trans ?_ (preserved_projection reach r focus data named m)
  constructor
  · rintro ⟨v,eq,held,_⟩
    exact ⟨v,eq,held⟩
  · rintro ⟨v,eq,held⟩
    have unchanged := copy_outside (live_private reach) v
    exact ⟨Copy (live state) v,fun id seen => (unchanged id (publicNames id seen)).symm.trans (eq id seen),
      (view_agrees reach r focus data unchanged).mp held,copy_live reach v⟩

end Yulang.GeneralRebaseLiveStore282
