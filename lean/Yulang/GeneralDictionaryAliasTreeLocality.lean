import Yulang.GeneralDictionaryAliasRecordedLocality
import Yulang.GeneralDictionaryTreeLeaf
import Yulang.GeneralDictionaryAliasMixedLocality
import Yulang.GeneralDictionaryScalarLeaf

/-! Recorded aliases and arbitrary finite binary tree leaves of the chosen declaration
share a single model. Arbitrary HasLeaf would not relate keys across aliases;
this condition checks the actual chosen declaration's syntax instead. -/
namespace Yulang.GeneralDictionaryAliasTreeLocality
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps GeneralNominalJointCandidates
variable {roles : Roles.RoleDecls}

/-- Structural leaf data for this declaration, not an independently chosen key. -/
def Leaf (context : GeneralNominalCandidates.Context) (focus : Occurrence roles) (declaration : Declaration) : Prop :=
  Nonempty (GeneralDictionaryTreeLeaf.TreeLeafShape context focus declaration) ∨
  Nonempty (GeneralDictionaryScalarLeaf.ScalarLeafShape context focus declaration)

def Covered (registry : Registry) (state : Tracked roles) (focus : Occurrence roles) (chosen : Declaration) : Prop :=
  ∀ site, Related state.current focus site →
    ((∃ packet ∈ state.current.packets, packet.site.occurrence = site.occurrence) ∨
      Leaf state.current.context site.occurrence chosen) ∧
    ∃ key children, GeneralNominalSupportBoundary.Local registry state site.occurrence (.selected key children)

/-- Leaf syntax supplies an Instance in the unchanged current assignment.
The selected survivor is used only for common readiness, linkage and freshness. -/
theorem leaf_branch (registry : Registry) (state : Tracked roles) (focus : Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (leaf : Leaf state.current.context focus declaration)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    BranchAt registry state.current focus declaration.id model := by
  have survivor : GeneralNominalRecursiveCandidates.Survivor registry state.current.context focus key children := by
    cases selected with | selected _ unique => exact unique.1
  have metadata : GeneralNominalRecursiveCandidates.Metadata registry state.current.context := by
    obtain ⟨_,_,_,_,_,_,_,_,prepared,_⟩ := survivor
    exact prepared.1
  have rule : GeneralDictionaryRecursiveEvidence.Instance registry state.current.context model focus declaration.id [] := by
    rcases leaf with spine | scalar
    · obtain ⟨shape⟩ := spine
      exact GeneralDictionaryTreeLeaf.instance_of_shape state.current.context registry focus declaration visible checked shape metadata model valid.1
    · obtain ⟨shape⟩ := scalar
      exact GeneralDictionaryScalarLeaf.instance_of_shape state.current.context registry focus declaration visible checked shape metadata model valid.1
  exact GeneralNominalStructuralSelectedGraph.branchAt_of_instance registry state.current focus declaration.id []
    (GeneralDictionaryOrdinarySelectedReplay.survivor_of_instance registry state.current.context focus key children
      survivor model declaration.id [] rule) model rule

theorem covered_of_recorded (registry : Registry) (state : Tracked roles) (focus : Occurrence roles)
    (chosen : Declaration) (covered : GeneralDictionaryAliasRecordedLocality.Covered registry state focus) :
    Covered registry state focus chosen := by
  intro site related
  have here := covered site related
  exact ⟨Or.inl here.1,here.2⟩

/-- Every related site obtains its own branch, with old-packet replay or a
structural derivation for the actual chosen declaration. Occurrence equality,
output equality, and independently selected key equality are not inputs. -/
theorem covered_joint (registry : Registry) (root focus : Occurrence roles) (state : Tracked roles)
    (formed : SourceFormed registry root state)
    (growth : ∀ packet ∈ state.current.packets,
      GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context)
    (coherent : GeneralDictionarySupportChoices.Coherent state.current)
    (packet : Packet roles) (member : packet ∈ state.current.packets) (same : packet.site.occurrence = focus)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (covered : Covered registry state focus packet.declaration)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Joint registry state.current focus key := by
  have replay := GeneralDictionaryOrdinarySelectedReplay.selected_replay registry root focus state formed
    packet member (growth packet member) same key children selected model valid
  have survivor : GeneralNominalRecursiveCandidates.Survivor registry state.current.context focus key children := by
    cases selected with | selected _ unique => exact unique.1
  have atRoot := GeneralNominalStructuralSelectedGraph.branchAt_of_instance registry state.current focus key children
    survivor model replay.2.2
  refine ⟨?_,model,valid,atRoot,?_⟩
  · intro other present alias
    exact (GeneralDictionarySupportChoices.recorded_class_key state.current coherent focus packet member
      (congrArg Occurrence.identity same) other present alias).trans replay.1
  · intro site related
    obtain ⟨source,localKey,localChildren,localSelected⟩ := covered site related
    rcases source with ⟨other,present,located⟩ | leaf
    · have localReplay := GeneralDictionaryOrdinarySelectedReplay.selected_replay registry root site.occurrence state formed
        other present (growth other present) located localKey localChildren localSelected model valid
      have alias : Alias state.current packet.site.occurrence.identity other.site.occurrence.identity := by
        rw [same,located]; exact related.2
      have keys : localKey = key := localReplay.1.symm.trans
        ((coherent packet member other present alias).symm.trans replay.1)
      have localSurvivor : GeneralNominalRecursiveCandidates.Survivor registry state.current.context site.occurrence localKey localChildren := by
        cases localSelected with | selected _ unique => exact unique.1
      rw [← keys]
      exact GeneralNominalStructuralSelectedGraph.branchAt_of_instance registry state.current site.occurrence localKey localChildren
        localSurvivor model localReplay.2.2
    · have reg := GeneralDictionarySupportJournal.packet_registry registry root state formed packet member
      have checkPacket : DeclarationChecked registry.constructors roles packet.declaration := by
        rw [← reg]; exact packet.checked
      have visiblePacket : packet.declaration ∈ registry.declarations := by
        obtain ⟨before,support,_,_,enabled,_,_,_⟩ :=
          GeneralDictionaryInstallationOrigin.packet_origin registry root state formed packet member
        exact enabled.1.2.2.2.1
      rw [← replay.1]
      exact leaf_branch registry state site.occurrence packet.declaration visiblePacket checkPacket leaf
        localKey localChildren localSelected model valid

theorem early_ordinary_joint (registry : Registry) (root focus : Occurrence roles)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (state : Tracked roles)
    (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (schedule : GeneralDictionaryEarlyMergeChoices.Scheduled registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets) (same : packet.site.occurrence = focus)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (covered : Covered registry state focus packet.declaration)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Joint registry state.current focus key :=
  covered_joint registry root focus state
    (GeneralDictionarySupportOrdinaryExecution.steps_formed (.initial context source) path)
    (GeneralDictionarySupportOrdinaryExecution.initial_packets_extension registry root context state path)
    (GeneralDictionaryEarlyMergeChoices.scheduled_coherent registry root state schedule)
    packet member same key children selected covered model valid
/-- Previously certified mixed alias coverage remains valid. -/
theorem covered_of_mixed (registry : Registry) (state : Tracked roles) (focus : Occurrence roles)
    (chosen : Declaration) (covered : GeneralDictionaryAliasMixedLocality.Covered registry state focus chosen) :
    Covered registry state focus chosen := by
  intro site related
  obtain ⟨source,selected⟩ := covered site related
  refine ⟨?_,selected⟩
  rcases source with recorded | spine | scalar
  · exact Or.inl recorded
  · obtain ⟨shape⟩ := spine
    exact Or.inr (Or.inl ⟨GeneralDictionaryTreeLeaf.ofSpineShape _ _ _ shape⟩)
  · exact Or.inr (Or.inr scalar)
end Yulang.GeneralDictionaryAliasTreeLocality
