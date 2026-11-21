import Yulang.GeneralVersionedAggregateClassNow314

set_option backward.isDefEq.respectTransparency false
/-! For any actual selected frame, the remaining same-assignment obligation
is precisely revisited non-tautological internal rows whose targets are
protected. Free rows have checked coherence regardless of history. -/
namespace Yulang.GeneralVersionedRemainingWrites314
open GeneralNominalCenters GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedEvidence231 (Frame Evidence)
open GeneralNominalVersionedTraceSupport237 (Reachable)
open GeneralNominalVersionedJournalFrame236 (sources)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedMixedMaterialization237 (Residual)
open GeneralNominalVersionedPlans231 (HeadModels SchemaHolds variables)
open GeneralNominalCommonBridge (Assignment)
open GeneralVersionedRootWrites312 (inner internalRows)
open GeneralVersionedJointWrites312 (protect)
open GeneralVersionedCompoundRows313 (Cell Taut coherent_address)
open GeneralVersionedComputedRows313 (OutputCell classifies addresses_disjoint)
open GeneralVersionedFirstComputed313 (proper_keys)
open GeneralFiniteTypedWrites312 (reflexive)
open GeneralNominalSaturationState (Packet Alias)

def ReusedRows (s : State roles) (e : Effect roles) : Prop :=
  ∀ m, Models s m → HeadModels e.plan.packet m → SchemaHolds e.plan e.plan.headSchema m → e.Live s.core m →
    ∀ q ∈ inner e.plan, q.target ∈ protect s e (sources s) →
      (Cell e.plan q ∨ OutputCell e.plan q) → q.Holds (variables e.plan m) m

def ForeignChoice (s : State roles) (p : Packet roles) : Prop :=
  ∀ q ∈ s.core.erased.current.packets,
    Alias s.core.erased.current p.site.occurrence.identity q.site.occurrence.identity →
    q.site.occurrence.identity ≠ p.site.occurrence.identity → q.declaration.id = p.declaration.id

theorem choice {s : State roles} {p : Packet roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (pick : Local registry s p.site.occurrence (.selected p.declaration.id kids)) (valid : Models s m) :
    GeneralNominalCycleSteps.ChoiceCompatible s.core.erased.current p ↔ ForeignChoice s p := by
  constructor
  · exact fun h q present alias _ => (h q present alias).symm
  · intro foreign q present alias
    by_cases owner : q.site.occurrence.identity = p.site.occurrence.identity
    · exact (GeneralVersionedSameOwnerChoice314.key_eq checked actual pick valid present owner).symm
    · exact (foreign q present alias owner).symm

theorem internal {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked registry)
    (frame : Frame (Compiled registry) s.core focus key e.plan)
    (reused : ReusedRows s e) :
    GeneralVersionedSelectedJointWrites312.InternalReady s e (sources s) := by
  intro m valid head schema live
  have outputs := proper_keys e.plan (GeneralVersionedCompiledFirstInstall313.key_coherence checked.2 frame.visible) m
  constructor
  · intro a aMem b bMem same free
    obtain ⟨one,ho,rfl⟩ := List.mem_map.mp aMem
    obtain ⟨two,ht,rfl⟩ := List.mem_map.mp bMem
    have fromOne := (classifies e.plan _ ho).resolve_left
      (fun taut => free (GeneralVersionedNewOwnerInstall314.taut_protected ho taut))
    have fromTwo := (classifies e.plan _ ht).resolve_left
      (fun taut => free (same.symm ▸ GeneralVersionedNewOwnerInstall314.taut_protected ht taut))
    rcases fromOne with first|first <;> rcases fromTwo with last|last
    · rw [coherent_address first last same]
      exact reflexive _
    · exact False.elim (addresses_disjoint first last same)
    · exact False.elim (addresses_disjoint last first same.symm)
    · exact outputs _ _ first last same
  · intro row member guarded
    obtain ⟨q,found,rfl⟩ := List.mem_map.mp member
    rcases classifies e.plan q found with taut|cell|computed
    · exact taut m
    · exact reused m valid head schema live q found guarded (.inl cell)
    · exact reused m valid head schema live q found guarded (.inr computed)

theorem joint {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (pick : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id kids))
    (registryEq : e.registry = Compiled registry) (snapshot : e.snapshot = s.core)
    (inhabited : ∃ m, Models s m) (reused : ReusedRows s e) :
    ∃ m, Residual s e m := by
  have frame : Frame (Compiled registry) s.core e.plan.packet.site.occurrence e.plan.packet.declaration.id e.plan :=
    registryEq ▸ snapshot ▸ e.frame
  obtain ⟨m,valid⟩ := inhabited
  exact GeneralVersionedSelectedJointWrites312.joint_from_internal checked actual pick registryEq snapshot
    (GeneralNominalVersionedModelSupport237.current s) (GeneralNominalVersionedTraceSiteSupport237.current s)
    (GeneralVersionedAggregateClassNow314.ledger checked actual pick frame valid)
    (GeneralVersionedHistoricalHead314.head checked actual pick frame ⟨m,valid⟩)
    (internal checked frame reused)

theorem installable {s : State roles} {e : Effect roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (pick : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id kids))
    (registryEq : e.registry = Compiled registry) (snapshot : e.snapshot = s.core)
    (inhabited : ∃ m, Models s m) (foreign : ForeignChoice s e.plan.packet)
    (reused : ReusedRows s e) :
    GeneralNominalVersionedMixedKernel234.Installable (Compiled registry) s e := by
  obtain ⟨m,valid⟩ := inhabited
  exact (GeneralNominalVersionedMixedMaterialization237.source_installable_iff checked actual pick registryEq snapshot).mpr
    ⟨(choice checked actual pick valid).mpr foreign,joint checked actual pick registryEq snapshot ⟨m,valid⟩ reused⟩

theorem node_and_edges {s : State roles} {root focus : Occurrence roles}
    (checked : (boundary roles).Checked registry) (actual : Reachable registry root s)
    (pick : Local registry s focus (.selected key kids))
    (stable : (boundary roles).Stable registry s focus)
    (reached : focus = root ∨ GeneralNominalSaturationState.Generated s.core.erased.current root focus)
    (valid : Models s m)
    (ordered : CommonRoleOutermostResolver.All₂ (Evidence (Compiled registry) s.core m) kids dictionaries)
    (justify : ∀ e : Effect roles, e.registry = Compiled registry → e.snapshot = s.core →
      e.plan.packet.site.occurrence = focus → e.plan.packet.declaration.id = key →
      ForeignChoice s e.plan.packet ∧ ReusedRows s e) :
    Evidence (Compiled registry) s.core m focus (.node key dictionaries) ∧
      ∀ child ∈ kids, GeneralNominalSaturationState.Generated s.core.erased.current root child := by
  obtain ⟨e,g,snapshot,o,k,c⟩ := GeneralNominalVersionedMixedSelectedEffect235.source_effect checked actual pick
  have exactPick : Local registry s e.plan.packet.site.occurrence (.selected e.plan.packet.declaration.id kids) := by
    rw [o,k]
    exact pick
  obtain ⟨foreign,reused⟩ := justify e g snapshot o k
  have enabled := installable checked actual exactPick g snapshot ⟨m,valid⟩ foreign reused
  have mixed := GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp pick
  exact ⟨GeneralNominalVersionedMixedStableEvidence235.selected_node stable enabled o mixed valid ordered,
    fun _ h => GeneralNominalVersionedMixedStableEvidence235.selected_generated_children stable enabled o mixed reached h⟩

end Yulang.GeneralVersionedRemainingWrites314
