import Yulang.GeneralDictionaryInstallationOrigin

/-! Reverse provenance of actual generated-child edges in source-formed support
states. Selection alone is not substituted for an installation or an edge. -/
namespace Yulang.GeneralDictionaryEdgeOrigin
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps
variable {roles : Roles.RoleDecls}

/-- Every stored direct edge has an actual recorded emitting packet. Certified
refresh/reobservation preserve this, despite changing current child syntax. -/
theorem edge_packet (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state) :
    ∀ first last, (first,last) ∈ state.current.edges →
      ∃ packet ∈ state.current.packets,
        packet.site.occurrence = first ∧ last ∈ packet.children := by
  induction formed with
  | initial context source => intro first last member; cases member
  | @update before after formed update ih =>
    obtain ⟨focus,generated,action⟩ := update
    intro first last member
    have retain : ∀ a b, (a,b) ∈ before.current.edges →
        ∃ packet ∈ after.current.packets, packet.site.occurrence = a ∧ b ∈ packet.children := by
      intro a b old
      obtain ⟨packet,present,same,child⟩ := ih a b old
      exact ⟨packet,GeneralDictionaryInstallationOrigin.step_packets ⟨focus,generated,action⟩ present,same,child⟩
    cases action with
    | administrative _ _ admin => cases admin <;> exact retain first last member
    | merge => exact retain first last member
    | install installed support enabled novel guard =>
      rcases List.mem_append.mp member with old | added
      · exact retain first last old
      · obtain ⟨child,present,equal⟩ := List.mem_map.mp added
        have same := Prod.mk.inj equal
        exact ⟨installed,List.mem_cons_self,same.1,same.2 ▸ present⟩

/-- If no packet was ever installed at an occurrence, no outgoing historical
child edge exists there, regardless of current survivor emission. -/
theorem no_packet_no_edge (registry : Registry) (root focus : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state)
    (missing : ¬ ∃ packet ∈ state.current.packets, packet.site.occurrence = focus) :
    ∀ child, (focus,child) ∉ state.current.edges := by
  intro child edge
  obtain ⟨packet,member,same,_⟩ := edge_packet registry root state formed focus child edge
  exact missing ⟨packet,member,same⟩

/-- Nonterminal committed packets need not themselves be recorded, but their
edges force SOME recorded packet at precisely the same occurrence. -/
theorem committed_nonterminal_origin (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state)
    (packet : Packet roles) (committed : GeneralNominalFeedbackSteps.Committed state.current packet)
    (nonterminal : packet.children ≠ []) :
    ∃ old ∈ state.current.packets, old.site.occurrence = packet.site.occurrence := by
  cases children : packet.children with
  | nil => exact False.elim (nonterminal children)
  | cons child rest =>
    obtain ⟨old,member,same,_⟩ := edge_packet registry root state formed _ child
      (committed.2 child (by rw [children]; simp))
    exact ⟨old,member,same⟩

/-- Joint is explicit: it closes current installation; reverse edge provenance
then discharges the same-occurrence historical packet condition. -/
theorem selected_nonterminal_packet (registry : Registry) (root focus : Occurrence roles)
    (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state)
    (key : Nat) (children : List (Occurrence roles))
    (stable : Stable registry state focus)
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (joint : GeneralNominalJointCandidates.Joint registry state.current focus key)
    (nonterminal : children ≠ []) :
    ∃ packet ∈ state.current.packets, packet.site.occurrence = focus := by
  have formed := GeneralNominalSupportBoundary.reachable_formed registry state root reachable
  have exactState := formed_exact formed
  have closed : ∀ site ∈ state.current.sites, site.occurrence = focus →
      GeneralNominalFeedbackSteps.MergesClosed state.current site := by
    intro site member same other present inputs
    exact GeneralDictionarySupportEvidence.stable_merges_of_exact registry state focus exactState stable
      site other member present (same ▸ Generated.root) inputs
  obtain ⟨packet,reg,context,same,id,kids,enabled,committed⟩ :=
    GeneralDictionarySupportEvidence.stable_joint_packet registry state focus key children stable selected joint closed
  obtain ⟨old,member,occurrence⟩ := committed_nonterminal_origin registry root state formed packet committed
    (kids ▸ nonterminal)
  exact ⟨old,member,occurrence.trans same⟩

/-- Exact extensional description of the direct edge relation by the journal.
Multiplicity and edge ordering are not identified by this theorem. -/
theorem edge_iff_packet (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state)
    (first last : Occurrence roles) :
    (first,last) ∈ state.current.edges ↔
      ∃ packet ∈ state.current.packets, packet.site.occurrence = first ∧ last ∈ packet.children := by
  constructor
  · exact edge_packet registry root state formed first last
  · rintro ⟨packet,member,same,child⟩
    have edge := (GeneralDictionarySupportJournal.recorded_committed registry root state formed packet member).2 last child
    simpa only [same] using edge

/-- A genuinely unrecorded nonterminal stable selection cannot be explained by
Joint. This isolates the missing obligation rather than silently deriving it. -/
theorem unrecorded_nonterminal_not_joint (registry : Registry) (root focus : Occurrence roles)
    (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state)
    (key : Nat) (children : List (Occurrence roles))
    (stable : Stable registry state focus)
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (nonterminal : children ≠ [])
    (missing : ¬ ∃ packet ∈ state.current.packets, packet.site.occurrence = focus) :
    ¬ GeneralNominalJointCandidates.Joint registry state.current focus key :=
  fun joint => missing (selected_nonterminal_packet registry root focus state reachable key children
    stable selected joint nonterminal)

end Yulang.GeneralDictionaryEdgeOrigin
