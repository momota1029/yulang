import Yulang.GeneralVersionedEssentialAggregates313

set_option backward.isDefEq.respectTransparency false
/-! A protected aggregate can be justified by an actual historical entry
or by its equation in the current assignment. Raw reservation is not either
proof. This is enough for the real prior-choice branch and preserves Models. -/
namespace Yulang.GeneralVersionedSemanticEntryChoice313
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedCandidates231 (Prepared)
open GeneralNominalVersionedPlans231 (HeadModels)
open GeneralNominalVersionedModelSupport237 (Support)
open GeneralVersionedProtectedPeer312 (Raw)
open GeneralVersionedHistoricalTransport312 (atFocus)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralNominalSaturationState (Packet Alias)
open GeneralNominalCommonBridge (Assignment)
open GeneralVersionedPeerChoice311 (reads)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralVersionedSemanticPeer312 (protectedPool)
open GeneralVersionedEssentialAggregates313 (Active Historical protected_iff)
open GeneralVersionedEssentialSupport313 (trim trimmed)

abbrev Entry := GeneralNominalFiniteEquationRealization236.Entry

def EquationAt (m : Assignment) (entry : Entry) : Prop :=
  PresenceNormalForm.All CommonNominalFullCarrier.model m (GeneralNominalAllocation.equations entry.1 entry.2)

def ProtectedEquations (s : State roles) (p : Packet roles) (m : Assignment) : Prop :=
  ∀ entry ∈ packetEntries p, Active s p entry.1 → EquationAt m entry

def Certificates (s : State roles) (p : Packet roles) (m : Assignment) : Prop :=
  ∀ entry ∈ packetEntries p, Active s p entry.1 → Historical s entry.1 ∨ EquationAt m entry

theorem sound {s : State roles} {p : Packet roles} {m : Assignment}
    (actual : B4TargetV8.Reachable (boundary roles) registry root s)
    (current : p.context = s.core.erased.current.context)
    (valid : Models s m) (certs : Certificates s p m) : ProtectedEquations s p m := by
  intro entry present active
  rcases certs entry present active with fromHistory|direct
  · have found : GeneralNominalVersionedMixedSeedLedger237.IdCovered [entry.1] s p := by
      intro other listed same
      have eq := List.mem_singleton.mp same
      exact eq.symm ▸ fromHistory
    exact GeneralNominalVersionedAggregateLedger236.protected_equations
      (GeneralNominalVersionedMixedSeedLedger237.covered
        (GeneralNominalVersionedMixedSeedLedger237.reachable actual) current found)
      valid entry present (List.mem_singleton_self _)
  · exact direct

theorem complete {s : State roles} {p : Packet roles} {m : Assignment}
    (current : p.context = s.core.erased.current.context)
    (valid : Models s m) (raw : Raw p m)
    (need : ProtectedEquations s p m) :
    ∃ n, Models s n ∧ HeadModels p n := by
  have support := GeneralNominalVersionedModelSupport237.current s
  exact ⟨_,GeneralVersionedSemanticPeer312.full_head current (trimmed support) valid raw
    (fun entry found inside => need entry found ((protected_iff support).mp inside))⟩

def Coverage (registry : Registry) (s : State roles) (focus : Occurrence roles) (decl : Declaration) (m : Assignment) : Prop :=
  ∀ checked bounds, reads s.core.erased.current.context focus = some bounds →
    Certificates s (atFocus s registry focus decl checked bounds) m

theorem prepared {s : State roles} {root focus : Occurrence roles} {prior : Packet roles} {m : Assignment}
    (checked : (boundary roles).Checked registry)
    (actual : B4TargetV8.Reachable (boundary roles) registry root s)
    (selected : Local registry s focus (.selected key children))
    (valid : Models s m)
    (stored : prior ∈ s.core.erased.current.packets)
    (alias : Alias s.core.erased.current focus.identity prior.site.occurrence.identity)
    (coverage : Coverage registry s focus prior.declaration m) :
    Prepared (Compiled registry) s.core.erased.current.context focus prior.declaration := by
  rcases GeneralNominalVersionedMixedChoice236.historical_prepared_or_failed checked actual selected stored alias with ready|failed
  · exact ready
  obtain ⟨metadata,bounds,located,fresh,blocked,arity,_⟩ := failed
  have compiled := GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked
  have verify (decl : Declaration) (shown : decl ∈ (Compiled registry).declarations) :
      DeclarationChecked (Compiled registry).constructors roles decl :=
    Eq.mp (congrArg (fun rs => DeclarationChecked (Compiled registry).constructors rs decl) compiled.1)
      (compiled.2.2 decl shown)
  have verified := verify prior.declaration (GeneralNominalVersionedMixedChoiceHistory236.visible actual stored)
  let p := atFocus s registry focus prior.declaration verified bounds
  obtain ⟨current,frame,_⟩ := GeneralNominalVersionedMixedSelectedFrame235.source_frame actual selected
  let now : Plan roles := ⟨p,current.input,current.input_exact.trans frame.occurrence_eq⟩
  obtain ⟨historical,member,same⟩ := GeneralNominalVersionedMixedChoiceHistory236.packet_plan actual stored
  have linked : Alias s.core.erased.current now.packet.site.occurrence.identity historical.packet.site.occurrence.identity := by
    rw [same]
    exact alias
  have meaning := GeneralVersionedAliasReport312.from_alias checked actual historical now member frame.center_recorded
    rfl located linked (congrArg Packet.declaration same).symm m valid
  obtain ⟨next,_,head⟩ := complete (p := p) rfl valid meaning.2 (sound actual rfl valid (coverage verified bounds located))
  exact ⟨metadata,frame.prepared.2.1,bounds,located,fresh,⟨blocked,meaning.1,arity⟩,next,
    (GeneralNominalVersionedCandidates231.headModels_packet_iff p next).mpr head⟩

theorem choice {s : State roles} {root : Occurrence roles} {p : Packet roles} {m : Assignment}
    (checked : (boundary roles).Checked registry)
    (actual : B4TargetV8.Reachable (boundary roles) registry root s)
    (selected : Local registry s p.site.occurrence (.selected p.declaration.id children))
    (valid : Models s m)
    (certify : ∀ prior ∈ s.core.erased.current.packets,
      Alias s.core.erased.current p.site.occurrence.identity prior.site.occurrence.identity →
      Coverage registry s p.site.occurrence prior.declaration m) :
    GeneralNominalCycleSteps.ChoiceCompatible s.core.erased.current p := by
  apply (GeneralNominalVersionedMixedChoice236.choice_iff_prepared checked actual selected).mpr
  intro prior stored alias
  exact prepared checked actual selected valid stored alias (certify prior stored alias)

end Yulang.GeneralVersionedSemanticEntryChoice313
