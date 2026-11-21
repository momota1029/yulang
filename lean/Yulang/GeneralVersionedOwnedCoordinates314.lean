import Yulang.GeneralVersionedUnseenBinder313
import Yulang.GeneralVersionedCompiledFirstInstall313

set_option backward.isDefEq.respectTransparency false
/-! Pure source/owner decomposition of the actual versioned capture and
where allocator, independent of satisfiability and installed effects. -/
namespace Yulang.GeneralVersionedOwnedCoordinates314
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalSaturationState (Packet)
open GeneralNominalVersionedFrame231 (binder capture childSite emittedCenter frame)
open GeneralNominalAllocation (occurrences)
open GeneralNominalIdentities (Origin source)
open GeneralVersionedUnseenOwnerCenters313 (OldCenter binder_origin)
open GeneralNominalCenteredFrame179 (siteSources)

abbrev Owned (p : Packet roles) (n : Nat) : Prop :=
  n ∈ GeneralNominalState.sources p.context.state ∨
    ∃ k : Origin, k.1 = p.site.occurrence.identity ∧ source p.context.state.seed k = n

theorem input_endpoints (p : Packet roles) (name : Nat) :
    Owned p ((capture p).inputs name).1 ∧ Owned p ((capture p).inputs name).2 := by
  have singleton (interval : GeneralSourceState.Interval)
      (exactPair : occurrences p.bindings name = [interval]) : Owned p interval.1 ∧ Owned p interval.2 := by
    have within : interval ∈ occurrences p.bindings name := exactPair ▸ List.mem_singleton_self _
    have ep := GeneralNominalAllocationSupport.occurrences_endpoints
      (GeneralNominalAllocationSupport.report_endpoints p.context.state (GeneralNominalPacketSupport.report p))
      name interval within
    exact ⟨.inl ep.1,.inl ep.2⟩
  have added (mode : Nat) : Owned p (GeneralNominalAggregateVersion231.slot p.context.state.seed
      p.site.occurrence.identity p.declaration.id mode name p.bindings) :=
    .inr ⟨_,rfl,rfl⟩
  unfold capture frame GeneralNominalVersionedAllocation231.capture
  cases here : occurrences p.bindings name with
  | nil => simpa only [here] using And.intro (added 0) (added 1)
  | cons a as =>
    cases as with
    | nil => simpa only [here] using singleton a here
    | cons b bs => simpa only [here] using And.intro (added 0) (added 1)

theorem output (p : Packet roles) (name : Nat) : Owned p ((capture p).outputs name) :=
  .inr ⟨_,rfl,rfl⟩

theorem variable_read (p : Plan roles) (mode : GeneralNominalMaterialization.Mode) (name : Nat) :
    Owned p.packet (GeneralNominalVersionedExpressionFrame236.variableSource p mode name) := by
  unfold GeneralNominalVersionedExpressionFrame236.variableSource
  split
  · exact binder_origin p name
  · cases mode
    · exact (input_endpoints p.packet name).1
    · exact (input_endpoints p.packet name).2
    · exact binder_origin p name

theorem where_endpoints (p : Plan roles) (clause : Clause) (sig : clause.Signature roles)
    (i : Fin (roles clause.role).arity) :
    Owned p.packet ((childSite p clause sig).occurrence.demand.arguments i).1 ∧
    Owned p.packet ((childSite p clause sig).occurrence.demand.arguments i).2 := by
  change let pat := clause.arguments[i.val]'(by rw [sig.1]; exact i.isLt)
    let bounds := GeneralDeclarationDemands.inputInterval (capture p.packet)
      (((frame p.packet).allocation p.packet.declaration.id clause).arguments i) pat
    Owned p.packet bounds.1 ∧ Owned p.packet bounds.2
  dsimp only
  unfold GeneralDeclarationDemands.inputInterval
  split
  · exact input_endpoints p.packet _
  · exact ⟨.inr ⟨_,rfl,rfl⟩,.inr ⟨_,rfl,rfl⟩⟩

theorem child_footprint (p : Plan roles) (clause : Clause) (sig : clause.Signature roles) :
    ∀ n ∈ siteSources (childSite p clause sig), Owned p.packet n := by
  intro n h
  obtain ⟨row,present,within⟩ := List.mem_flatten.mp h
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp present
  simp only [List.mem_cons,List.not_mem_nil,or_false] at within
  rcases within with rfl|rfl|rfl
  · exact (where_endpoints p clause sig i).1
  · exact (where_endpoints p clause sig i).2
  · exact GeneralVersionedUnseenOwnerCenters313.emitted_origin p clause sig i

theorem equation_reads (p : Plan roles) (e : GeneralNominalCenteredHeadMatSchemas.Equation) :
    ∀ n ∈ GeneralVersionedJointWrites312.inputNames p e, Owned p.packet n := by
  intro n h
  obtain ⟨entry,_,rfl⟩ := List.mem_map.mp h
  exact variable_read p entry.1 entry.2

theorem where_target (p : Plan roles) (eq : GeneralNominalCenteredHeadMatSchemas.Equation)
    (found : eq ∈ GeneralVersionedRootWrites312.inner p) :
    Owned p.packet eq.target := by
  rcases GeneralVersionedComputedRows313.classifies p eq found with taut|cell|computed
  · exact equation_reads p eq _ (GeneralVersionedFirstInternal313.taut_reads p eq taut)
  · obtain ⟨c,_,pos,kind,_,_,_,_,hit,_⟩ := cell
    rw [hit]
    exact .inr ⟨_,rfl,rfl⟩
  · obtain ⟨_,_,rule,_,_,_,hit,_⟩ := computed
    rw [hit]
    exact .inr ⟨_,rfl,rfl⟩

end Yulang.GeneralVersionedOwnedCoordinates314
