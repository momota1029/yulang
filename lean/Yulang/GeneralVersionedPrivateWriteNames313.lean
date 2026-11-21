import Yulang.GeneralVersionedFirstGroundHead313
import Yulang.GeneralVersionedSelectedJointWrites312

set_option backward.isDefEq.respectTransparency false
/-! Protected head/RHS leaves cannot be private compound write targets in
the first-install fragment. The distinction is by actual allocation tag. -/
namespace Yulang.GeneralVersionedPrivateWriteNames313
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalSaturationState (Packet)
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralVersionedTraceDomain313 (seed)
open GeneralVersionedBeforeFirstInstall313 (source_small source_slot_clean center_small)
open GeneralVersionedFirstHead313 (names raw_small origins_small)
open GeneralNominalVersionedFrame231 (binder capture)
open GeneralNominalAllocation (occurrences origin)
open GeneralNominalIdentities (source source_identity source_above_seed)
open GeneralNominalCenteredModelExtension (originSource)

def Safe (p : Plan roles) (n : Nat) : Prop :=
  n ≤ p.packet.context.state.seed ∨
    ∃ k : GeneralNominalIdentities.Origin, source p.packet.context.state.seed k = n ∧
      (k.2.2.1 = 0 ∨ k.2.2.1 = 1 ∨ k.2.2.1 = 2 ∨ k.2.2.1 = 8)

theorem tag (p : Plan roles) (owner key kind pos column : Nat)
    (allowed : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 8) :
    Safe p (source p.packet.context.state.seed (origin owner key kind pos column)) :=
  .inr ⟨_,rfl,allowed⟩

theorem transfer_small {s : State roles} {p : Plan roles} {n : Nat}
    (frame : Frame registry s.core focus key p) (small : n ≤ seed s) : Safe p n :=
  .inl (by rw [frame.context_eq]; exact small)

theorem endpoints {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (empty : s.plans = [])
    (frame : Frame (Compiled registry) s.core focus key p) (name : Nat) :
    Safe p ((capture p.packet).inputs name).1 ∧ Safe p ((capture p.packet).inputs name).2 := by
  have singleton (bounds : GeneralSourceState.Interval) (single : occurrences p.packet.bindings name = [bounds]) :
      Safe p bounds.1 ∧ Safe p bounds.2 := by
    have within : bounds ∈ occurrences p.packet.bindings name := single ▸ List.mem_singleton_self _
    have eps := GeneralNominalAllocationSupport.occurrences_endpoints
      (GeneralNominalAllocationSupport.report_endpoints p.packet.context.state (GeneralNominalPacketSupport.report p.packet))
      name bounds within
    exact ⟨transfer_small frame (raw_small actual empty frame eps.1),
      transfer_small frame (raw_small actual empty frame eps.2)⟩
  have allocated :
      Safe p (GeneralNominalAggregateVersion231.slot p.packet.context.state.seed p.packet.site.occurrence.identity
        p.packet.declaration.id 0 name p.packet.bindings) ∧
      Safe p (GeneralNominalAggregateVersion231.slot p.packet.context.state.seed p.packet.site.occurrence.identity
        p.packet.declaration.id 1 name p.packet.bindings) :=
    ⟨tag p _ _ _ _ _ (.inl rfl),tag p _ _ _ _ _ (.inr (.inl rfl))⟩
  unfold capture GeneralNominalVersionedFrame231.frame GeneralNominalVersionedAllocation231.capture
  cases semantic : occurrences p.packet.bindings name with
  | nil => simpa only [semantic] using allocated
  | cons first rest =>
    cases rest with
    | nil => simpa only [semantic] using singleton first semantic
    | cons b tail => simpa only [semantic] using allocated

theorem output (p : Plan roles) (name : Nat) : Safe p ((capture p.packet).outputs name) :=
  tag p _ _ _ _ _ (Or.inr (Or.inr (Or.inl rfl)))

theorem binder_name {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (empty : s.plans = [])
    (frame : Frame (Compiled registry) s.core focus key p) (name : Nat) :
    Safe p (binder p name) := by
  unfold binder
  split
  · exact output p name
  · split
    · exact (endpoints actual empty frame name).1
    · exact tag p _ _ _ _ _ (Or.inr (Or.inr (Or.inr rfl)))

theorem rhs_read {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (empty : s.plans = [])
    (frame : Frame (Compiled registry) s.core focus key p) (mode : GeneralNominalMaterialization.Mode) (name : Nat) :
    Safe p (GeneralNominalVersionedExpressionFrame236.variableSource p mode name) := by
  unfold GeneralNominalVersionedExpressionFrame236.variableSource
  split
  · exact binder_name actual empty frame name
  · cases mode
    · exact (endpoints actual empty frame name).1
    · exact (endpoints actual empty frame name).2
    · exact binder_name actual empty frame name

theorem head_atom {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (empty : s.plans = [])
    (frame : Frame (Compiled registry) s.core focus key p) (atom : PresenceNormalForm.Atom Nat)
    (member : atom ∈ GeneralNominalVersionedInstallation231.atoms p.packet) :
    ∀ n ∈ GeneralNominalState.atomSources atom, Safe p n := by
  have old : ∀ n ∈ GeneralNominalState.sources p.packet.context.state, Safe p n :=
    fun _ h => transfer_small frame (raw_small actual empty frame h)
  have available := GeneralNominalAllocationSupport.report_endpoints p.packet.context.state (GeneralNominalPacketSupport.report p.packet)
  rcases List.mem_append.mp member with computed|checks
  · rcases List.mem_append.mp computed with cross|merge
    · exact fun _ h => old _ (GeneralNominalAllocationSupport.cross_sources available atom cross h)
    · rw [GeneralNominalVersionedAggregateEntries236.atoms_eq] at merge
      obtain ⟨entry,existsEntry,which⟩ := List.mem_flatMap.mp merge
      have atomDisj : ∀ n ∈ GeneralNominalState.atomSources atom, n = entry.1 ∨ n ∈ GeneralNominalState.typeSources entry.2 := by
        intro n h
        have found := GeneralNominalAllocationSupport.equation_sources entry.1 entry.2
          (pool := entry.1 :: GeneralNominalState.typeSources entry.2)
          (by simp) (fun _ h => List.mem_cons_of_mem _ h) atom which h
        exact List.mem_cons.mp found
      obtain ⟨name,_,_,lower|upper⟩ := (GeneralNominalVersionedAggregateRealization236.member_iff ..).mp existsEntry
      · intro n h
        rcases atomDisj n h with same|fromRhs
        · rw [same,lower]
          exact tag p _ _ _ _ _ (.inl rfl)
        · rw [lower] at fromRhs
          exact old _ (GeneralNominalAllocationSupport.lower_sources _
            (GeneralNominalAllocationSupport.occurrences_endpoints available name) fromRhs)
      · intro n h
        rcases atomDisj n h with same|fromRhs
        · rw [same,upper]
          exact tag p _ _ _ _ _ (.inr (.inl rfl))
        · rw [upper] at fromRhs
          exact old _ (GeneralNominalAllocationSupport.upper_sources _
            (GeneralNominalAllocationSupport.occurrences_endpoints available name) fromRhs)
  · exact fun _ h => old _ (GeneralNominalAllocationSupport.checks_sources _ _ (fun _ hx => hx) atom checks h)

theorem head_read {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (empty : s.plans = [])
    (frame : Frame (Compiled registry) s.core focus key p) :
    ∀ n ∈ GeneralNominalVersionedResidualFrame237.headSources p.packet, Safe p n := by
  intro n present
  rcases List.mem_append.mp present with a|b
  · obtain ⟨atom,ha,within⟩ := List.mem_flatMap.mp a
    exact head_atom actual empty frame atom ha n within
  · exact transfer_small frame (raw_small actual empty frame (GeneralVersionedRawReportDomain313.raw_membership _ b))

theorem excludes (p : Plan roles) (pos col kind : Nat)
    (forbidden : kind ≠ 0 ∧ kind ≠ 1 ∧ kind ≠ 2 ∧ kind ≠ 8) :
    ¬ Safe p (fresh p.packet.context.state.seed p.packet.site.occurrence.identity p.packet.declaration.id kind pos col) := by
  intro member
  rcases member with small|⟨k,equal,good⟩
  · exact Nat.not_lt_of_ge small (source_above_seed _ _)
  · have fields := (source_identity p.packet.context.state.seed _ _).mp equal
    have which := congrArg (fun o : GeneralNominalIdentities.Origin => o.2.2.1) fields
    change k.2.2.1 = kind at which
    rw [which] at good
    rcases good with h|h|h|h
    · exact forbidden.1 h
    · exact forbidden.2.1 h
    · exact forbidden.2.2.1 h
    · exact forbidden.2.2.2 h


def ActualSafe (p : Plan roles) (n : Nat) : Prop :=
  n ≤ p.packet.context.state.seed ∨
    ∃ k : GeneralNominalIdentities.Origin, source p.packet.context.state.seed k = n ∧
      (k.2.2.1 = 2 ∨ k.2.2.1 = 8) ∧ k.2.2.2.2 = 0

theorem actual_to_safe {p : Plan roles} {n : Nat} (h : ActualSafe p n) : Safe p n := by
  rcases h with small|⟨o,eq,kind,_⟩
  · exact .inl small
  · exact .inr ⟨o,eq,.inr (.inr kind)⟩

theorem actual_binder {s : State roles} {p : Plan roles}
    (actual : Reachable registry root s) (empty : s.plans = [])
    (frame : Frame (Compiled registry) s.core focus key p) (name : Nat) :
    ActualSafe p (binder p name) := by
  have privateSafe : ActualSafe p (fresh p.packet.context.state.seed p.packet.site.occurrence.identity
      p.packet.declaration.id 8 name 0) := .inr ⟨_,rfl,.inr rfl,rfl⟩
  have differing := GeneralNominalAggregateVersion231.distinct_purpose p.packet.context.state.seed
    p.packet.site.occurrence.identity p.packet.declaration.id 0 1 name p.packet.bindings p.packet.bindings ((by decide) : (0:Nat) ≠ 1)
  unfold binder
  split
  · exact .inr ⟨_,rfl,.inl rfl,rfl⟩
  · unfold capture GeneralNominalVersionedFrame231.frame GeneralNominalVersionedAllocation231.capture
    cases found : occurrences p.packet.bindings name with
    | nil => simpa only [found,differing,ite_false] using privateSafe
    | cons first rest =>
      cases rest with
      | nil =>
        simp only [found]
        split
        · have inOccurrences : first ∈ occurrences p.packet.bindings name := found ▸ List.mem_singleton_self _
          have raw := (GeneralNominalAllocationSupport.occurrences_endpoints
            (GeneralNominalAllocationSupport.report_endpoints p.packet.context.state (GeneralNominalPacketSupport.report p.packet))
            name first inOccurrences).1
          exact .inl (by rw [frame.context_eq]; exact raw_small actual empty frame raw)
        · exact privateSafe
      | cons b tail => simpa only [found,differing,ite_false] using privateSafe

theorem aggregate_not_actual (p : Plan roles) (kind name : Nat) :
    ¬ ActualSafe p (GeneralNominalAggregateVersion231.slot p.packet.context.state.seed p.packet.site.occurrence.identity
      p.packet.declaration.id kind name p.packet.bindings) := by
  intro found
  rcases found with small|⟨k,equal,_,version⟩
  · exact Nat.not_lt_of_ge small (GeneralNominalAggregateVersion231.above_seed ..)
  · have eq := (source_identity p.packet.context.state.seed _ _).mp equal
    have pos := congrArg (fun o : GeneralNominalIdentities.Origin => o.2.2.2.2) eq
    change k.2.2.2.2 = Nat.succ _ at pos
    omega

end Yulang.GeneralVersionedPrivateWriteNames313
