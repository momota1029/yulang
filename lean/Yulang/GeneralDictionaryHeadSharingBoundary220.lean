import Yulang.B4TargetV8
import Yulang.GeneralDictionaryHeadSharingConflict220

namespace Yulang.GeneralDictionaryHeadSharingBoundary220
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalCenteredHeadMatStepJournal (State)
variable {roles : Roles.RoleDecls}

def boundary (roles : Roles.RoleDecls) :
    B4TargetV8.SourceBoundary (GeneralNominalCenteredHeadMatStepLocal.vocabulary roles) :=
  { GeneralDictionaryDefaultBoundary208.boundary roles with
    SharingConflict := GeneralDictionaryHeadSharingConflict220.Conflict }

abbrev Local (value : Registry) (state : State roles) := B4TargetV8.Local (boundary roles) value state
abbrev Step (value : Registry) := GeneralDictionaryDefaultBoundary208.Step (roles := roles) value
abbrev Stable (value : Registry) := GeneralDictionaryDefaultBoundary208.Stable (roles := roles) value

theorem selected_iff : Local value state focus (.selected key children) ↔
    GeneralDictionaryDefaultBoundary208.Local value state focus (.selected key children) ∧
      ¬ GeneralDictionaryHeadSharingConflict220.Conflict value state focus := B4TargetV8.selected_iff

theorem whereAccessible (value : Registry) (state : State roles) (root : Occurrence roles) :
    Acc (Child (Local value state)) root := by
  have prior := GeneralDictionaryDefaultBoundary208.whereAccessible value state root
  induction prior with
  | intro root _ ih => exact .intro root (fun child edge => ih child (B4TargetV8.child_prior edge))

theorem conflict_unique (bad : GeneralDictionaryHeadSharingConflict220.Conflict value state focus) :
    ∃ key children, B4TargetV8.Unique (boundary roles) value state focus key children := by
  obtain ⟨key,children,unique,_⟩ := bad
  exact ⟨key,children,unique⟩

theorem conflict_rejected (bad : GeneralDictionaryHeadSharingConflict220.Conflict value state focus) :
    Local value state focus .rejected := by
  obtain ⟨key,children,unique⟩ := conflict_unique bad
  exact B4TargetV8.sharing_unique_rejected bad unique

theorem conflict_not_selected (bad : GeneralDictionaryHeadSharingConflict220.Conflict value state focus) :
    ¬ Local value state focus (.selected key children) := fun given => (selected_iff.mp given).2 bad

theorem conflict_not_pending (bad : GeneralDictionaryHeadSharingConflict220.Conflict value state focus) :
    ¬ Local value state focus .pending := B4TargetV8.conflict_not_pending bad

theorem local_total (checked : (boundary roles).Checked value) (state : State roles) (focus : Occurrence roles) :
    ∃ frontier, Local value state focus frontier := by
  classical
  by_cases bad : GeneralDictionaryHeadSharingConflict220.Conflict value state focus
  · exact ⟨.rejected,conflict_rejected bad⟩
  · obtain ⟨frontier,chosen⟩ := GeneralDictionaryDefaultBoundary208.local_total checked state focus
    exact ⟨frontier,.ordinary bad chosen⟩

theorem stepModels (step : Step value root before after) (valid : (boundary roles).Models after model) :
    (boundary roles).Models before model := GeneralDictionaryDefaultBoundary208.stepModels step valid

theorem closure (halted : ∀ after, ¬ Step value root state after) :
    Stable value state root ∧ ∀ child, (boundary roles).Generated value state root child → Stable value state child :=
  GeneralDictionaryDefaultBoundary208.closure halted

theorem initialReorders (order : (boundary roles).Reorders first last)
    (initial : (boundary roles).Initial first root state) : (boundary roles).Initial last root state :=
  GeneralDictionaryDefaultBoundary208.initialReorders order initial

theorem dictionaryRefl (dictionary : Dictionary) : (boundary roles).DictionaryEquivalent dictionary dictionary := rfl

end Yulang.GeneralDictionaryHeadSharingBoundary220
