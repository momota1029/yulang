import Yulang.GeneralRebaseHistoryOrder282

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseHistorySupport282
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralRebaseMixedOwnedTrace277 (raw)
open GeneralRebasePrivateJournal282 (Hidden AgreeOutside effect_context)
open GeneralRebasePrivateKey282 (port versioned_distinct)
open GeneralRebasePrivateTrace282 (historical)
open GeneralRebasePrivateStore282 (Public raw_public)
open GeneralRebaseHistoryOrder282 (history member_exact decode)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralNominalVersionedMixedSeedLedger237 (entries)
open GeneralNominalVersionedAggregateRealization236 (member_iff)
open GeneralNominalCommonBridge (Assignment)
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralPresenceOrderedBlock247 (put solve)
open CommonNominalFullCarrier (model)
open GeneralNominalState (sources typeSources)

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

theorem packet_context (reach : Reachable registry root state) (q : Plan roles) (listed : q ∈ state.plans) :
    ∃ prior, Reachable registry root prior ∧ q.packet.context.state = raw prior ∧ (raw prior).seed = (raw state).seed := by
  obtain ⟨e,found,rfl⟩ := (historical reach).1 q listed
  obtain ⟨prior,path,snap,_,seed⟩ := effect_context reach found
  refine ⟨prior,path,?_,seed⟩
  exact congrArg GeneralNominalCandidates.Context.state (e.frame.context_eq.trans
    (congrArg (fun s : GeneralNominalCenteredSteps.State roles => s.erased.current.context) snap))

theorem packet_reads {q : Plan roles} {entry : Entry Nat} (used : entry ∈ packetEntries q.packet) :
    typeSources entry.2 ⊆ sources q.packet.context.state := by
  obtain ⟨name,_,_,rfl | rfl⟩ := (member_iff ..).mp used
  all_goals
    have ep := GeneralNominalAllocationSupport.report_endpoints q.packet.context.state (GeneralNominalPacketSupport.report q.packet)
    have bound := GeneralNominalAllocationSupport.occurrences_endpoints ep name
  · exact GeneralNominalAllocationSupport.lower_sources _ bound
  · exact GeneralNominalAllocationSupport.upper_sources _ bound

theorem entry_reads (reach : Reachable registry root state) (entry : Entry Nat) (listed : entry ∈ history state) :
    Public (raw state).seed (typeSources entry.2) := by
  obtain ⟨q,used,origin⟩ := List.mem_flatMap.mp ((member_exact reach entry).mp listed)
  obtain ⟨prior,path,ctx,seed⟩ := packet_context reach q used
  have reads : typeSources entry.2 ⊆ sources q.packet.context.state := packet_reads origin
  rw [ctx] at reads
  rw [← seed]
  exact fun n member => raw_public path n (reads member)

theorem entry_target (reach : Reachable registry root state) (entry : Entry Nat) (listed : entry ∈ history state) :
    ¬ Hidden (raw state).seed entry.1 := by
  obtain ⟨q,used,origin⟩ := List.mem_flatMap.mp ((member_exact reach entry).mp listed)
  obtain ⟨prior,path,ctx,seed⟩ := packet_context reach q used
  have same := (congrArg GeneralNominalState.State.seed ctx).trans seed
  rw [← same]
  obtain ⟨name,_,_,rfl | rfl⟩ := (member_iff ..).mp origin
  · rintro ⟨owner,d,tag,hit⟩
    exact versioned_distinct q.packet owner d tag 0 name hit.symm
  · rintro ⟨owner,d,tag,hit⟩
    exact versioned_distinct q.packet owner d tag 1 name hit.symm

theorem solve_agrees (seed : Nat) (defs : List (Entry Nat))
    (reads : ∀ e ∈ defs, Public seed (typeSources e.2)) {first last : Assignment}
    (same : AgreeOutside seed first last) :
    AgreeOutside seed (solve model defs first) (solve model defs last) := by
  induction defs generalizing first last with
  | nil => exact same
  | cons head tail ih =>
    apply ih (fun row member => reads row (List.mem_cons_of_mem _ member))
    intro id outside
    change put model first head.1 (head.2.eval model first) id =
      put model last head.1 (head.2.eval model last) id
    have eq := GeneralNominalCenteredModelExtension.type_eval_same head.2
      (fun n found => same n (reads head List.mem_cons_self n found))
    simp only [put,eq,same id outside]

theorem decode_agrees (reach : Reachable registry root state) {first last : Assignment}
    (same : AgreeOutside (raw state).seed first last) :
    AgreeOutside (raw state).seed (decode state first) (decode state last) :=
  solve_agrees _ _ (entry_reads reach) same

end Yulang.GeneralRebaseHistorySupport282
