import Yulang.GeneralDictionaryAgreedRefiningTrace174

/-! Full recursive dictionary evidence after actual ordinary/refining histories.
The independent Classify antecedent remains. No child Evidence or historical
Extension is assumed. General actual executions need not belong to this
fixed-carrier/view subrelation, so this is not general B4 completion. -/
namespace Yulang.GeneralDictionaryAgreedCompletion175
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionaryRecursiveEvidence
open GeneralNominalActualAgreedLocal
open GeneralNominalActualAgreedBoundary (boundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
open GeneralDictionaryAgreedRefiningTrace174
variable {roles : Roles.RoleDecls} {defer : Bool} {gap : GapPredicate roles}
variable {registry : Registry} {state : Tracked roles} {root focus : Occurrence roles}

/-- Snapshot consumer of the derived journal invariant. This semantic premise
is not an action guard; the public trace theorem below produces it. -/
theorem selected_instance_of_recorded
    (recorded : RecordedCurrent registry state)
    (policy : defer = true ∨ ¬ gap registry state focus)
    (stable : (boundary defer gap).Stable registry state focus)
    (selected : Local defer gap registry state focus (.selected key children))
    (model : Assignment) (valid : Models state.current model) :
    Instance registry state.current.context model focus key children := by
  obtain ⟨packet,same,keySame,childrenSame,enabled | ⟨_,member,_⟩⟩ :=
    selected_available policy selected
  · obtain ⟨enabled,support,guard⟩ := enabled
    have stablePacket : GeneralNominalActualBoundary.Stable registry state packet.site.occurrence :=
      same.symm ▸ stable
    have result := GeneralDictionaryActualStable173.stable_instance packet support
      stablePacket enabled guard model valid
    simpa only [same,keySame,childrenSame] using result
  · have result := recorded packet member model valid
    simpa only [same,keySame,childrenSame] using result

theorem selected_evidence_of_recorded
    (recorded : RecordedCurrent registry state)
    (policy : defer = true ∨ ¬ gap registry state focus)
    (stable : (boundary defer gap).Stable registry state focus)
    (selected : Local defer gap registry state focus (.selected key children))
    (model : Assignment) (valid : Models state.current model) (dictionaries : List Payload)
    (given : All₂ (Evidence registry state.current.context model) children dictionaries) :
    Evidence registry state.current.context model focus (.node key dictionaries) :=
  evidence_node _ _ _ _ _ _ _ (selected_instance_of_recorded recorded policy stable selected model valid) given

private theorem classify_parts {v : B4Target.Vocabulary} (b : B4Target.SourceBoundary v)
    (r : v.Registry) (s : v.State) (d : v.Demand) (key : Nat)
    (dictionaries : List CommonRoleOutermostResolver.Dictionary)
    (derived : B4TargetV3.Classify b r s d (.selected (.node key dictionaries))) :
    ∃ children, B4Target.SafeKnown b r s d ∧ B4Target.Unique b r s d key children ∧
      All₂ (fun child dictionary => B4TargetV3.Classify b r s child (.selected dictionary)) children dictionaries := by
  cases derived with
  | selected safe unique children => exact ⟨_,safe,unique,children⟩

mutual
  /-- Whole dictionary soundness from a current journal invariant. The public
  halted trace theorem below produces this invariant from actual transitions.
  Classification and stability remain explicit in this snapshot lemma. -/
  theorem dictionary_evidence
      (recorded : RecordedCurrent registry state)
      (policy : ∀ demand, defer = true ∨ ¬ gap registry state demand)
      (rootStable : (boundary defer gap).Stable registry state root)
      (generatedStable : ∀ demand, Generated state.current root demand →
        (boundary defer gap).Stable registry state demand)
      (model : Assignment) (valid : Models state.current model)
      (dictionary : Payload) (focus : Occurrence roles)
      (reached : focus = root ∨ Generated state.current root focus)
      (derived : B4TargetV3.Classify (boundary defer gap).toSourceBoundary registry state focus
        (.selected dictionary)) : Evidence registry state.current.context model focus dictionary := by
    have stable : (boundary defer gap).Stable registry state focus := by
      rcases reached with same | generated
      · exact same ▸ rootStable
      · exact generatedStable focus generated
    cases dictionary with
    | node key dictionaries =>
      obtain ⟨childrenList,safe,unique,children⟩ := classify_parts
        (boundary defer gap).toSourceBoundary registry state focus key dictionaries derived
      have selected : B4TargetV3.Local (boundary defer gap).toSourceBoundary registry state focus
          (.selected key _) := .selected safe unique
      have childGenerated : ∀ child ∈ childrenList, Generated state.current root child :=
        fun child member => GeneralDictionaryAgreedEvidence174.selected_child_generated (policy focus) stable selected reached member
      exact selected_evidence_of_recorded recorded (policy focus) stable
        ((GeneralNominalActualAgreedBoundary.local_correspondence defer gap registry state focus _).mp selected)
        model valid dictionaries
        (dictionaries_evidence recorded policy rootStable generatedStable model valid
          _ _ (fun child member => Or.inr (childGenerated child member)) children)
  termination_by sizeOf dictionary

  theorem dictionaries_evidence
      (recorded : RecordedCurrent registry state)
      (policy : ∀ demand, defer = true ∨ ¬ gap registry state demand)
      (rootStable : (boundary defer gap).Stable registry state root)
      (generatedStable : ∀ demand, Generated state.current root demand →
        (boundary defer gap).Stable registry state demand)
      (model : Assignment) (valid : Models state.current model)
      (dictionaries : List Payload) (demands : List (Occurrence roles))
      (reached : ∀ child, child ∈ demands → child = root ∨ Generated state.current root child)
      (derived : All₂ (fun child dictionary =>
        B4TargetV3.Classify (boundary defer gap).toSourceBoundary registry state child (.selected dictionary))
        demands dictionaries) :
      All₂ (Evidence registry state.current.context model) demands dictionaries := by
    cases derived with
    | nil => exact .nil
    | cons first rest =>
      exact .cons (dictionary_evidence recorded policy rootStable generatedStable model valid
        _ _ (reached _ (by simp)) first)
        (dictionaries_evidence recorded policy rootStable generatedStable model valid
          _ _ (fun child member => reached child (by simp [member])) rest)
  termination_by sizeOf dictionaries
end

theorem halted_dictionary_evidence
    (checked : (boundary defer gap).Checked registry)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (halted : ∀ after, ¬ GeneralNominalActualInspectionSteps.Step registry root state after)
    (policy : ∀ demand, defer = true ∨ ¬ gap registry state demand)
    (model : Assignment) (valid : Models state.current model) (dictionary : Payload)
    (derived : B4TargetV3.Classify (boundary defer gap).toSourceBoundary registry state root (.selected dictionary)) :
    Evidence registry state.current.context model root dictionary := by
  have formed := (trace_formed_recorded (.initial context source) (initial_recorded context) path).1
  have reachable : B4TargetV5.Reachable (boundary defer gap) registry root state :=
    GeneralNominalActualAgreedBoundary.reachable_iff_sourceFormed.mpr formed
  obtain ⟨rootStable,generatedStable⟩ := GeneralNominalActualAgreedBoundary.closure registry checked state root reachable halted
  exact dictionary_evidence (initial_trace_recorded context source path) policy rootStable generatedStable model valid
    dictionary root (Or.inl rfl) derived

/-- The pending policy discharges the implementation gap condition, not a
language rule saying absent provenance must be pending. -/
theorem halted_pending_dictionary_evidence
    (checked : (boundary true gap).Checked registry)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (halted : ∀ after, ¬ GeneralNominalActualInspectionSteps.Step registry root state after)
    (model : Assignment) (valid : Models state.current model) (dictionary : Payload)
    (derived : B4TargetV3.Classify (boundary true gap).toSourceBoundary registry state root (.selected dictionary)) :
    Evidence registry state.current.context model root dictionary :=
  halted_dictionary_evidence checked context source path halted (fun _ => Or.inl rfl)
    model valid dictionary derived

end Yulang.GeneralDictionaryAgreedCompletion175
