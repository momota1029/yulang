import Yulang.GeneralDictionarySupportOrdinaryExecution

/-! Recursive dictionary evidence for structurally journal-covered focuses.
Coverage is explicit and is not inferred from unrestricted support stability. -/
namespace Yulang.GeneralDictionaryCoveredEvidence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps GeneralNominalSupportBoundary
open GeneralDictionaryRecursiveEvidence CommonRoleOutermostResolver
variable {roles : Roles.RoleDecls}

/-- The journal contains a packet for each actually generated selected focus whose stored
observation context differs only by ordinary constraint growth. The selected key,
children, current branch validity and Evidence are not coverage premises. -/
def Covered (registry : Registry) (state : Tracked roles) (root : Occurrence roles) : Prop :=
  ∀ focus, Generated state.current root focus → ∀ key children,
    GeneralNominalSupportBoundary.Local registry state focus (.selected key children) →
    ∃ packet ∈ state.current.packets,
      GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context ∧
      packet.site.occurrence = focus

theorem classify_node_parts {v : B4Target.Vocabulary} (b : B4Target.SourceBoundary v)
    (registry : v.Registry) (state : v.State) (focus : v.Demand)
    (key : Nat) (dictionaries : List Dictionary)
    (derived : B4TargetV3.Classify b registry state focus (.selected (.node key dictionaries))) :
    ∃ children, B4Target.SafeKnown b registry state focus ∧
      B4Target.Unique b registry state focus key children ∧
      All₂ (fun child dictionary => B4TargetV3.Classify b registry state child (.selected dictionary)) children dictionaries := by
  cases derived with
  | selected safe unique children => exact ⟨_,safe,unique,children⟩

mutual
  theorem dictionary_evidence (registry : Registry) (root : Occurrence roles)
      (state : Tracked roles) (formed : SourceFormed registry root state)
      (covered : Covered registry state root) (model : GeneralNominalCommonBridge.Assignment)
      (valid : Models state.current model) (dictionary : GeneralDictionaryReadback.Payload)
      (focus : Occurrence roles) (reached : Generated state.current root focus)
      (derived : B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry state focus (.selected dictionary)) :
      Evidence registry state.current.context model focus dictionary := by
    cases dictionary with
    | node key dictionaries =>
      obtain ⟨childrenList,safe,unique,children⟩ := classify_node_parts (v := GeneralNominalSupportBoundary.vocabulary roles) (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry state focus key dictionaries derived
      have selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key _) :=
        (local_correspondence registry state focus _).mp (B4TargetV3.Local.selected safe unique)
      obtain ⟨packet,member,growth,same⟩ := covered focus reached key childrenList selected
      have generated := (GeneralDictionaryOrdinarySelectedReplay.selected_generated registry root focus
        state formed packet member growth same key _ selected model valid).2
      exact GeneralDictionaryOrdinarySelectedReplay.selected_evidence registry root focus state formed
        packet member growth same key _ selected model valid dictionaries
        (dictionaries_evidence registry root state formed covered model valid _ _ generated children)
  termination_by sizeOf dictionary

  theorem dictionaries_evidence (registry : Registry) (root : Occurrence roles)
      (state : Tracked roles) (formed : SourceFormed registry root state)
      (covered : Covered registry state root) (model : GeneralNominalCommonBridge.Assignment)
      (valid : Models state.current model) (dictionaries : List GeneralDictionaryReadback.Payload)
      (demands : List (Occurrence roles))
      (reached : ∀ focus ∈ demands, Generated state.current root focus)
      (derived : All₂ (fun focus dictionary =>
        B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry state focus (.selected dictionary)) demands dictionaries) :
      All₂ (Evidence registry state.current.context model) demands dictionaries := by
    cases derived with
    | nil => exact .nil
    | cons first rest =>
      exact .cons (dictionary_evidence registry root state formed covered model valid _ _
        (reached _ (by simp)) first)
        (dictionaries_evidence registry root state formed covered model valid _ _
          (fun focus member => reached focus (by simp [member])) rest)
  termination_by sizeOf dictionaries
end

/-- Full finite selected dictionary at an actual initial-source-reachable state.
No bound on dictionary depth and no terminal-declaration restriction is used. -/
theorem reachable_dictionary_evidence (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state)
    (covered : Covered registry state root) (model : GeneralNominalCommonBridge.Assignment)
    (valid : Models state.current model) (dictionary : GeneralDictionaryReadback.Payload)
    (derived : B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry state root (.selected dictionary)) :
    Evidence registry state.current.context model root dictionary :=
  dictionary_evidence registry root state (reachable_formed registry state root reachable)
    covered model valid dictionary root .root derived
/-- On a real ordinary-only initial-source trace, context coverage is derived
from the updates. Only packet occurrence coverage remains structural. -/
theorem ordinary_dictionary_evidence (registry : Registry) (root : Occurrence roles)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (state : Tracked roles)
    (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (coverage : ∀ focus, Generated state.current root focus → ∀ key children,
      GeneralNominalSupportBoundary.Local registry state focus (.selected key children) →
      ∃ packet ∈ state.current.packets, packet.site.occurrence = focus)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (dictionary : GeneralDictionaryReadback.Payload)
    (derived : B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
      registry state root (.selected dictionary)) :
    Evidence registry state.current.context model root dictionary := by
  apply dictionary_evidence registry root state
    (GeneralDictionarySupportOrdinaryExecution.steps_formed (.initial context source) path)
    ?_ model valid dictionary root .root derived
  intro focus reached key children selected
  obtain ⟨packet,member,same⟩ := coverage focus reached key children selected
  exact ⟨packet,member,GeneralDictionarySupportOrdinaryExecution.initial_packets_extension
    registry root context state path packet member,same⟩
end Yulang.GeneralDictionaryCoveredEvidence
