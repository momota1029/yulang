import Yulang.GeneralRebaseWholeJournal282
import Yulang.GeneralPresenceOrderedExpansion249

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseWholeStore282
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralRebaseMixedOwnedTrace277 (raw)
open GeneralRebaseHistoryOrder282 (history decode ordered)
open GeneralRebaseHistorySupport282 (decode_agrees)
open GeneralRebaseWholeJournal282 (View Observable exact_view preserved_projection)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebasePrivateStore282 (Joint Public Private copy_outside copy_model packet_targets joint_iff)
open GeneralRebaseTermAggregate281 (writes)
open GeneralRebaseTermCopy281 (Write Respects Copy Unique lookup_exact)
open GeneralRebasePortProjection280 (Project)
open GeneralPresenceOrderedSubstitution247 (mapping)
open GeneralNominalSaturationState (Packet)
open GeneralDictionaryReadback (Payload)
open GeneralPresenceDefinitionRewrite244 (transform)
open GeneralNominalOrderedRaw248 (read_mapping)
open Core.PresenceGeneration (TyTerm)
open CommonNominalFullCarrier (model Equivalent subtype_refl)

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
  {state contextState : State roles}

def store (state : State roles) (p : Packet roles) : List Write :=
  transform (mapping (history state)) (writes p true)

theorem store_private (state : State roles) (p : Packet roles) :
    Private p.context.state.seed (store state p) := by
  intro row used
  obtain ⟨original,old,rfl⟩ := List.mem_map.mp used
  exact packet_targets p original old

theorem store_unique (state : State roles) (p : Packet roles) : Unique (store state p) := by
  intro a aa b bb same
  obtain ⟨old,one,rfl⟩ := List.mem_map.mp aa
  obtain ⟨fresh,two,rfl⟩ := List.mem_map.mp bb
  change old.1 = fresh.1 at same
  change old.2.subst _ = fresh.2.subst _
  rw [GeneralRebaseTermAggregate281.unique p true old one fresh two same]

theorem expression_exact (state : State roles) (base : Assignment) (term : TyTerm Nat) :
    (term.subst (mapping (history state))).eval model base = term.eval model (decode state base) := by
  rw [TyTerm.eval_subst]
  exact congrArg (term.eval model) (read_mapping (history state) base)

theorem store_rhs_closed (state : State roles) (p : Packet roles) (row : Write) (listed : row ∈ store state p) :
    Observable state (GeneralPresenceUsedSupport245.typedReads row.2) := by
  obtain ⟨original,_,rfl⟩ := List.mem_map.mp listed
  exact GeneralPresenceOrderedExpansion249.type_rewrite_closed (history state) (ordered state).2.2 original.2

theorem view_agrees (reach : Reachable registry root state) (r : Registry) (focus : Occurrence roles)
    (data : Payload) {before after : Assignment}
    (same : GeneralRebasePrivateJournal282.AgreeOutside (raw state).seed before after) :
    View state r focus data before ↔ View state r focus data after :=
  (exact_view reach r focus data before).trans ((joint_iff reach (decode_agrees reach same)).trans
    (exact_view reach r focus data after).symm)

theorem copy_exact (reach : Reachable registry root state)
    (contextReach : Reachable registry root contextState)
    (seed : (raw contextState).seed = (raw state).seed) (p : Packet roles)
    (same : p.context.state = raw contextState) (m : Assignment) :
    Respects (store state p) (Copy (store state p) m) := by
  have target : Private (raw state).seed (store state p) :=
    ((congrArg GeneralNominalState.State.seed same).trans seed) ▸ store_private state p
  have agree := decode_agrees reach (copy_outside target m)
  intro row used
  obtain ⟨prior,covered,rfl⟩ := List.mem_map.mp used
  have orig : GeneralNominalState.typeSources prior.2 ⊆ GeneralNominalState.sources p.context.state :=
    GeneralRebaseTermAggregate281.reads p true prior covered
  have equal := GeneralNominalCenteredModelExtension.type_eval_same prior.2 (fun n appeared => by
    apply agree
    rw [← seed]
    apply GeneralRebasePrivateStore282.raw_public contextReach n
    exact same ▸ orig appeared)
  change Equivalent (Copy (store state p) m prior.1).1
    ((prior.2.subst (mapping (history state))).eval model (Copy (store state p) m))
  rw [expression_exact,← equal]
  have hit := lookup_exact (store_unique state p) used
  change GeneralRebaseTermCopy281.lookup (store state p) prior.1 =
    some (prior.2.subst (mapping (history state))) at hit
  unfold Copy
  rw [hit]
  change Equivalent ((prior.2.subst (mapping (history state))).eval model m) (prior.2.eval model (decode state m))
  rw [expression_exact]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem projection (reach : Reachable registry root state) (contextReach : Reachable registry root contextState)
    (seed : (raw contextState).seed = (raw state).seed) (p : Packet roles)
    (same : p.context.state = raw contextState) (r : Registry) (focus : Occurrence roles) (data : Payload)
    (outsideHistory : Observable state names) (outsideFixed : Public (raw state).seed names)
    (outer : Assignment) :
    Project names (fun m => View state r focus data m ∧ Respects (store state p) m) outer ↔
      Project names (Joint state r focus data) outer := by
  apply Iff.trans ?_ (preserved_projection reach r focus data outsideHistory outer)
  constructor
  · rintro ⟨m,eq,good,_⟩
    exact ⟨m,eq,good⟩
  · rintro ⟨m,eq,good⟩
    have target : Private (raw state).seed (store state p) :=
      ((congrArg GeneralNominalState.State.seed same).trans seed) ▸ store_private state p
    refine ⟨Copy (store state p) m,fun id listed => ((copy_model target outsideFixed m id listed).symm).trans (eq id listed),
      (view_agrees reach r focus data (copy_outside target m)).mp good,?_⟩
    exact copy_exact reach contextReach seed p same m

end Yulang.GeneralRebaseWholeStore282
