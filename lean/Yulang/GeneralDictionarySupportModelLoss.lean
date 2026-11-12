import Yulang.GeneralDictionaryVariableJournalMerge
import Yulang.GeneralNominalSupportSteps

/-! Localization of a possible loss of every journal model along actual support
steps. This does not assert that such loss occurs, nor that all reachable states
are inhabited. Installability supplies a witness for its own result; certified
administrative updates preserve the model set. Only a merge can be the first
step from an inhabited journal to an empty one. -/
namespace Yulang.GeneralDictionarySupportModelLoss
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalDemandMerging (Site outputAtoms)
variable {roles : Roles.RoleDecls}

/-- Existence is distinguished from universal preservation of each assignment. -/
def Inhabited (state : Tracked roles) : Prop := ∃ model, Models state.current model

theorem installation_inhabited (registry : Registry) (state : Tracked roles)
    (packet : Packet roles) (support : List (Occurrence roles))
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet) :
    Inhabited (GeneralNominalSupportSteps.install state packet support) := by
  obtain ⟨_,same,_,_,_,_,_,_,_,_,⟨model,valid,holds⟩,_⟩ := enabled.1
  exact ⟨model,(GeneralNominalFeedbackSites.install_models _ packet _ same model).mpr ⟨valid,holds⟩⟩

/-- Exact shape of any individual model-destroying update. No Checked, Stable,
Joint or target Evidence hypothesis is introduced. -/
theorem loss_is_merge {registry : Registry} {before after : Tracked roles}
    {focus : Occurrence roles} (update : At registry before focus after)
    (present : Inhabited before) (absent : ¬ Inhabited after) :
    ∃ first last : Site roles, ∃ support : List (Occurrence roles),
      after = GeneralNominalSupportSteps.merge before first last support ∧
      (∀ model, Models before.current model →
        ¬ PresenceNormalForm.All CommonNominalFullCarrier.model model (outputAtoms first last)) := by
  cases update with
  | administrative focus current update =>
    obtain ⟨model,valid⟩ := present
    exact False.elim (absent ⟨model,(administrative_models update model).mpr valid⟩)
  | install packet support enabled _ _ =>
    exact False.elim (absent (installation_inhabited registry before packet support enabled))
  | merge first last support _ _ _ _ _ =>
    refine ⟨first,last,support,rfl,?_⟩
    intro model valid outputs
    exact absent ⟨model,(merge_models before.current first last model).mpr ⟨valid,outputs⟩⟩

/-- A finite real trace from inhabited to empty contains a model-destroying
merge, with actual prefix, step and suffix witnesses. This is a diagnostic
necessary condition, not a reachable counterexample or a progress theorem. -/
theorem trace_loss_has_merge {registry : Registry} {root : Occurrence roles}
    {start finish : Tracked roles}
    (path : B4Target.Steps (Step registry root) start finish)
    (present : Inhabited start) (absent : ¬ Inhabited finish) :
    ∃ before after : Tracked roles,
      B4Target.Steps (Step registry root) start before ∧
      Step registry root before after ∧
      B4Target.Steps (Step registry root) after finish ∧
      Inhabited before ∧ ¬ Inhabited after ∧
      ∃ first last : Site roles, ∃ support : List (Occurrence roles),
        after = GeneralNominalSupportSteps.merge before first last support ∧
        ∀ model, Models before.current model →
          ¬ PresenceNormalForm.All CommonNominalFullCarrier.model model (outputAtoms first last) := by
  classical
  induction path with
  | refl => exact False.elim (absent present)
  | @tail middle finish previous step ih =>
    by_cases middlePresent : Inhabited middle
    · exact ⟨middle,finish,previous,step,.refl,middlePresent,absent,
        loss_is_merge step.choose_spec.2 middlePresent absent⟩
    · obtain ⟨before,after,one,two,three,old,new,shape⟩ := ih middlePresent
      exact ⟨before,after,one,two,.tail three step,old,new,shape⟩

/-- A historical packet whose repeated-variable materialization covers both
sites prevents a merge from destroying any preexisting assignment. -/
theorem covered_merge_inhabited (state : Tracked roles) (first last : Site roles)
    (support : List (Occurrence roles)) (packet : Packet roles)
    (recorded : packet ∈ state.current.packets) (names : Nat → Nat)
    (left : GeneralDictionaryVariableJournalMerge.Requests packet first names)
    (right : GeneralDictionaryVariableJournalMerge.Requests packet last names)
    (present : Inhabited state) :
    Inhabited (GeneralNominalSupportSteps.merge state first last support) := by
  obtain ⟨model,valid⟩ := present
  exact ⟨model,(merge_models state.current first last model).mpr ⟨valid,
    GeneralDictionaryVariableJournalMerge.outputs_from_packet state.current first last packet
      recorded names left right model valid⟩⟩

/-- At a genuinely model-destroying merge, no single recorded packet can
cover both sites by the same actual-output binder map. This excludes the
semantic materialization case already proved, not all legal merge steps. -/
theorem loss_has_no_cover (state : Tracked roles) (first last : Site roles)
    (support : List (Occurrence roles)) (present : Inhabited state)
    (absent : ¬ Inhabited (GeneralNominalSupportSteps.merge state first last support)) :
    ¬ ∃ packet ∈ state.current.packets, ∃ names : Nat → Nat,
      GeneralDictionaryVariableJournalMerge.Requests packet first names ∧
      GeneralDictionaryVariableJournalMerge.Requests packet last names := by
  rintro ⟨packet,recorded,names,left,right⟩
  exact absent (covered_merge_inhabited state first last support packet recorded names left right present)

end Yulang.GeneralDictionarySupportModelLoss
