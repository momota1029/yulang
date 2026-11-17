import Yulang.GeneralNominalVersionedDiagnostic232
import Yulang.GeneralDictionaryVersionedRawAcyclic232
import Yulang.GeneralDictionaryVersionedInstallClosed232
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-! Concrete local-only V8 diagnostic prerequisites. The diagnostic boundary
has false Initial/Step fields: these facts are not a complete operational
successor boundary or a solver termination theorem. -/
namespace Yulang.GeneralDictionaryVersionedSelectionFacts232
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryUpper230Step GeneralDictionaryUpper230Selected
open GeneralDictionaryVersionedInstalled232
open GeneralNominalVersionedCandidates231
open GeneralNominalVersionedJournal232
open GeneralNominalCenters

noncomputable abbrev context := installed.core.erased.current.context

theorem prepared : Prepared registry context root declaration :=
  GeneralDictionaryVersionedEvidence232.frame.prepared

theorem known : ¬ GeneralNominalState.RootPending context.state (inputs root).demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨(0 : Fin 6),rfl,Or.inr ⟨_,rfl⟩⟩

theorem children_empty : children registry context root declaration declaration_checked [((0 : Fin 6),(0 : Fin 6))] = [] := by
  unfold children GeneralNominalVersionedFrame231.children GeneralDictionaryEmissionPlans.children
    GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  rfl

theorem survivor : Survivor registry context root declaration.id [] :=
  ⟨known,declaration,List.mem_singleton_self _,declaration_checked,rfl,rfl,[((0 : Fin 6),(0 : Fin 6))],rfl,prepared,children_empty.symm⟩

theorem unique : Unique registry context root declaration.id [] := by
  refine ⟨survivor,?_⟩
  intro key kids found
  have copy := found
  obtain ⟨_,d,visible,_,identity,_⟩ := found
  cases List.mem_singleton.mp visible
  have same : key = declaration.id := identity.symm
  subst key
  exact ⟨rfl,survivor_children_functional checked copy survivor⟩

theorem administrative_ready : GeneralNominalVersionedDiagnostic232.AdministrativeReady installed root := by
  constructor
  · refine ⟨rootSite snapshot.seed root,?_,rfl⟩
    rw [GeneralDictionaryVersionedInstallClosed232.centers]
    exact List.mem_singleton_self _
  · intro first one _ last two _
    rw [GeneralDictionaryVersionedInstallClosed232.centers] at one two
    cases List.mem_singleton.mp one
    cases List.mem_singleton.mp two
    exact .refl _

theorem safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) registry installed root := by
  refine ⟨known,?_,?_,?_⟩
  · rintro (raw | semantic)
    · obtain ⟨_,_,_,slot,_,cycle⟩ := raw
      exact GeneralDictionaryVersionedRawAcyclic232.no_raw_recurs slot cycle
    · exact GeneralDictionaryVersionedAcyclic232.no_root_cycle root semantic
  · rintro (raw | semantic)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := raw
      exact GeneralDictionaryVersionedRawAcyclic232.no_raw_recurs visited.1 cycle
    · exact GeneralDictionaryVersionedAcyclic232.no_candidate_cycle registry root semantic
  · rintro (⟨_,d,visible,_,_,unprepared⟩ | unready)
    · cases List.mem_singleton.mp visible
      exact unprepared prepared
    · exact unready administrative_ready

end Yulang.GeneralDictionaryVersionedSelectionFacts232
