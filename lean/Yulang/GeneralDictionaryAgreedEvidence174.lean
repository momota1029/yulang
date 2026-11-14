import Yulang.GeneralNominalActualAgreedBoundary
import Yulang.GeneralDictionaryActualStable173
import Yulang.GeneralDictionaryActualRecorded173

/-! Current-model evidence for the policy-parametric actual boundary.
The historical-context obligation is explicit: no arbitrary descriptor refresh
is claimed to preserve the inspection view. The `true` policy is an operational
restriction, not an assertion that missing sharing is a language rule. -/
namespace Yulang.GeneralDictionaryAgreedEvidence174
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionaryRecursiveEvidence
open GeneralNominalActualAgreedLocal
open GeneralNominalActualAgreedBoundary (boundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls} {defer : Bool} {gap : GapPredicate roles}
variable {registry : Registry} {state : Tracked roles} {root focus : Occurrence roles}

/-- A concrete context-shape condition, not an Evidence or B4 premise. -/
def RecordedExtensions (state : Tracked roles) : Prop :=
  ∀ packet ∈ state.current.packets,
    GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context

/-- Stable selected packets have current source instances in each specified
journal model. Only the historical branch needs the explicit context condition. -/
theorem selected_instance
    (formed : GeneralNominalActualInspectionSteps.SourceFormed registry root state)
    (growth : RecordedExtensions state)
    (policy : defer = true ∨ ¬ gap registry state focus)
    (stable : (boundary defer gap).Stable registry state focus)
    (selected : Local defer gap registry state focus (.selected key children))
    (model : Assignment) (valid : Models state.current model) :
    Instance registry state.current.context model focus key children := by
  obtain ⟨packet,same,keySame,childrenSame,enabled | ⟨_,recorded,_⟩⟩ :=
    selected_available policy selected
  · obtain ⟨enabled,support,guard⟩ := enabled
    have stablePacket : GeneralNominalActualBoundary.Stable registry state packet.site.occurrence :=
      same.symm ▸ stable
    have result := GeneralDictionaryActualStable173.stable_instance packet support
      stablePacket enabled guard model valid
    simpa only [same,keySame,childrenSame] using result
  · have result := GeneralDictionarySharedRecordedEvidence.current_instance
      (GeneralNominalActualInspectionSteps.formed_shared formed) packet recorded
      (growth packet recorded) model valid
    simpa only [same,keySame,childrenSame] using result

/-- One current-model parent combines all child dictionaries in that same model. -/
theorem selected_evidence
    (formed : GeneralNominalActualInspectionSteps.SourceFormed registry root state)
    (growth : RecordedExtensions state)
    (policy : defer = true ∨ ¬ gap registry state focus)
    (stable : (boundary defer gap).Stable registry state focus)
    (selected : Local defer gap registry state focus (.selected key children))
    (model : Assignment) (valid : Models state.current model) (dictionaries : List Payload)
    (given : All₂ (Evidence registry state.current.context model) children dictionaries) :
    Evidence registry state.current.context model focus (.node key dictionaries) :=
  evidence_node _ _ _ _ _ _ _
    (selected_instance formed growth policy stable selected model valid) given

/-- The unresolved historical-context invariant is separated from the policy
completeness invariant. Neither is silently included in Stable. -/
def ReachableRecordedExtensions (defer : Bool) (gap : GapPredicate roles) : Prop :=
  ∀ registry, (boundary defer gap).Checked registry → ∀ state root,
    B4TargetV5.Reachable (boundary defer gap) registry root state → RecordedExtensions state

theorem evidenceNode_of_policy
    (growth : ReachableRecordedExtensions defer gap)
    (policy : ∀ registry, (boundary defer gap).Checked registry → ∀ state root,
      B4TargetV5.Reachable (boundary defer gap) registry root state → ∀ demand,
      defer = true ∨ ¬ gap registry state demand) :
    B4SkeletonV5.EvidenceNode (boundary defer gap) := by
  intro registry checked state root reachable model valid focus key children dictionaries reached stable _ safe unique given
  exact selected_evidence
    (GeneralNominalActualAgreedBoundary.reachable_iff_sourceFormed.mp reachable)
    (growth registry checked state root reachable)
    (policy registry checked state root reachable focus) stable
    ((GeneralNominalActualAgreedBoundary.local_correspondence defer gap registry state focus _).mp
      (.selected safe unique)) model valid dictionaries given

theorem evidenceNode_pending (growth : ReachableRecordedExtensions true gap) :
    B4SkeletonV5.EvidenceNode (boundary true gap) :=
  evidenceNode_of_policy growth (fun _ _ _ _ _ _ => Or.inl rfl)

theorem evidenceNode_complete (growth : ReachableRecordedExtensions false gap)
    (complete : GeneralNominalActualAgreedBoundary.GapFree gap) :
    B4SkeletonV5.EvidenceNode (boundary false gap) :=
  evidenceNode_of_policy growth (fun registry checked state root reachable demand =>
    Or.inr (complete registry checked state root reachable demand))

/-! A genuine restricted trace discharges RecordedExtensions. Its constructors
are original actual rules; descriptor refresh and reobservation are excluded.
No Extension assertion is accepted as an edge premise. -/
inductive OrdinaryAt (registry : Registry) (before : Tracked roles) :
    Occurrence roles → Tracked roles → Prop where
  | enqueue (focus : Occurrence roles)
      (linked : GeneralNominalState.Linked before.current.context.state focus.demand)
      (absent : ∀ site ∈ before.current.sites, site.occurrence ≠ focus) :
      OrdinaryAt registry before focus {before with current := GeneralNominalSaturationState.enqueue before.current focus}
  | equate (focus : Occurrence roles) (first last : Nat)
      (one : first ∈ GeneralNominalState.sources before.current.context.state)
      (two : last ∈ GeneralNominalState.sources before.current.context.state)
      (equal : GeneralNominalFeedbackK2.Equal before.current first last)
      (novel : ¬ GeneralNominalFeedbackSteps.RawEqual before.current first last) :
      OrdinaryAt registry before focus {before with current := GeneralNominalFeedbackSteps.equate before.current first last}
  | install (packet : Packet roles) (support : List (Occurrence roles))
      (enabled : GeneralNominalFeedbackSteps.Installable registry before.current packet)
      (novel : ¬ GeneralNominalFeedbackSteps.Committed before.current packet)
      (guard : GeneralNominalActualInspectionSteps.PacketGuard before packet support) :
      OrdinaryAt registry before packet.site.occurrence (GeneralNominalSharedSteps.install before packet support)
  | merge (first last : GeneralNominalDemandMerging.Site roles) (support : List (Occurrence roles))
      (one : first ∈ before.current.sites) (two : last ∈ before.current.sites)
      (same : GeneralNominalFeedbackSites.SameInputs before.current first last)
      (novel : ¬ Alias before.current first.occurrence.identity last.occurrence.identity)
      (guard : GeneralNominalSupportChoices.MergeGuard before first last support) :
      OrdinaryAt registry before first.occurrence (GeneralNominalSharedSteps.merge before first last support)

def OrdinaryStep (registry : Registry) (root : Occurrence roles) (before after : Tracked roles) : Prop :=
  ∃ focus, Generated before.current root focus ∧ OrdinaryAt registry before focus after

theorem ordinary_at_actual (action : OrdinaryAt registry before focus after) :
    GeneralNominalActualInspectionSteps.At registry before focus after := by
  cases action with
  | enqueue focus linked absent => exact .administrative _ _ (.enqueue _ linked absent)
  | equate focus first last one two equal novel => exact .administrative _ _ (.equate _ _ _ one two equal novel)
  | install packet support enabled novel guard => exact .install packet support enabled novel guard
  | merge first last support one two same novel guard => exact .merge first last support one two same novel guard

theorem ordinary_step_actual (step : OrdinaryStep registry root before after) :
    GeneralNominalActualInspectionSteps.Step registry root before after :=
  ⟨step.choose,step.choose_spec.1,ordinary_at_actual step.choose_spec.2⟩

theorem ordinary_at_extension (action : OrdinaryAt registry before focus after) :
    GeneralDictionaryOrdinaryTrace.Extension before.current.context after.current.context := by
  cases action with
  | enqueue => exact GeneralDictionaryOrdinaryTrace.enqueue_extension _ _
  | equate => exact GeneralDictionaryOrdinaryTrace.equate_extension _ _ _
  | install packet support enabled novel guard =>
      simpa only [GeneralNominalSharedSteps.install, GeneralNominalFeedbackSites.install, enabled.1.2.1] using
        GeneralDictionaryOrdinaryTrace.packet_extension packet
  | merge => exact GeneralDictionaryOrdinaryTrace.merge_extension _ _ _

theorem ordinary_steps_actual
    (path : B4Target.Steps (OrdinaryStep registry root) before after) :
    B4Target.Steps (GeneralNominalActualInspectionSteps.Step registry root) before after := by
  induction path with
  | refl => exact .refl
  | tail prior update ih => exact .tail ih (ordinary_step_actual update)

theorem ordinary_packets_extension (old : RecordedExtensions before)
    (path : B4Target.Steps (OrdinaryStep registry root) before after) : RecordedExtensions after := by
  induction path with
  | refl => exact old
  | @tail middle finish prior update ih =>
    have retained : ∀ packet ∈ middle.current.packets,
        GeneralDictionaryOrdinaryTrace.Extension packet.context finish.current.context :=
      fun packet member => GeneralDictionaryOrdinaryTrace.extension_trans (ih packet member)
        (ordinary_at_extension update.choose_spec.2)
    obtain ⟨focus,generated,action⟩ := update
    intro packet member
    cases action with
    | enqueue => exact retained packet member
    | equate => exact retained packet member
    | merge => exact retained packet member
    | install installed support enabled novel guard =>
      rcases List.mem_cons.mp member with rfl | old
      · exact GeneralDictionaryOrdinaryTrace.packet_extension packet
      · exact retained packet old

theorem ordinary_initial_extensions (context : GeneralNominalCandidates.Context)
    (path : B4Target.Steps (OrdinaryStep registry root) (initial context root) state) :
    RecordedExtensions state :=
  ordinary_packets_extension (by intro packet member; cases member) path

theorem ordinary_initial_formed (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (OrdinaryStep registry root) (initial context root) state) :
    GeneralNominalActualInspectionSteps.SourceFormed registry root state := by
  have formed : GeneralNominalActualInspectionSteps.SourceFormed registry root (initial context root) :=
    .initial context source
  induction path with
  | refl => exact formed
  | tail prior update ih => exact .update ih (ordinary_step_actual update)

/-- In this no-refresh trace fragment, historical growth is a theorem rather
than a supplied premise. Stability, selection, the policy condition and child
Evidence remain exactly as displayed. This is not general B4. -/
theorem ordinary_initial_selected_evidence (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (OrdinaryStep registry root) (initial context root) state)
    (policy : defer = true ∨ ¬ gap registry state focus)
    (stable : (boundary defer gap).Stable registry state focus)
    (selected : Local defer gap registry state focus (.selected key children))
    (model : Assignment) (valid : Models state.current model) (dictionaries : List Payload)
    (given : All₂ (Evidence registry state.current.context model) children dictionaries) :
    Evidence registry state.current.context model focus (.node key dictionaries) :=
  selected_evidence (ordinary_initial_formed context source path)
    (ordinary_initial_extensions context path) policy stable selected model valid dictionaries given

/-- Exact selected edges at this snapshot join the root's generated closure. -/
theorem selected_child_generated
    (policy : defer = true ∨ ¬ gap registry state focus)
    (stable : (boundary defer gap).Stable registry state focus)
    (selected : B4TargetV3.Local (boundary defer gap).toSourceBoundary registry state focus (.selected key children))
    (reached : focus = root ∨ Generated state.current root focus)
    (member : child ∈ children) : Generated state.current root child := by
  obtain ⟨packet,same,childrenSame,done⟩ :=
    GeneralNominalActualAgreedBoundary.selected_committed policy stable selected
  have parent : Generated state.current root focus := reached.elim (fun same => same ▸ .root) id
  have edge : (focus,child) ∈ state.current.edges := by
    rw [← same]
    exact done.2 child (childrenSame ▸ member)
  exact .child parent edge

private theorem classify_parts {v : B4Target.Vocabulary} (b : B4Target.SourceBoundary v)
    (r : v.Registry) (s : v.State) (d : v.Demand) (key : Nat)
    (dictionaries : List CommonRoleOutermostResolver.Dictionary)
    (derived : B4TargetV3.Classify b r s d (.selected (.node key dictionaries))) :
    ∃ children, B4Target.SafeKnown b r s d ∧ B4Target.Unique b r s d key children ∧
      All₂ (fun child dictionary => B4TargetV3.Classify b r s child (.selected dictionary)) children dictionaries := by
  cases derived with
  | selected safe unique children => exact ⟨_,safe,unique,children⟩

mutual
  /-- Whole dictionary soundness at one SourceFormed snapshot. There is no
  universal reachable-state growth assumption: only this snapshot's history
  and policy facts are used. Classification and child stability are genuine
  premises, not conclusions about the executor. -/
  theorem dictionary_evidence_snapshot
      (formed : GeneralNominalActualInspectionSteps.SourceFormed registry root state)
      (growth : RecordedExtensions state)
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
        fun child member => selected_child_generated (policy focus) stable selected reached member
      exact selected_evidence formed growth (policy focus) stable
        ((GeneralNominalActualAgreedBoundary.local_correspondence defer gap registry state focus _).mp selected)
        model valid dictionaries
        (dictionaries_evidence_snapshot formed growth policy rootStable generatedStable model valid
          _ _ (fun child member => Or.inr (childGenerated child member)) children)
  termination_by sizeOf dictionary

  theorem dictionaries_evidence_snapshot
      (formed : GeneralNominalActualInspectionSteps.SourceFormed registry root state)
      (growth : RecordedExtensions state)
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
      exact .cons (dictionary_evidence_snapshot formed growth policy rootStable generatedStable model valid
        _ _ (reached _ (by simp)) first)
        (dictionaries_evidence_snapshot formed growth policy rootStable generatedStable model valid
          _ _ (fun child member => reached child (by simp [member])) rest)
  termination_by sizeOf dictionaries
end

/-- Arbitrarily deep classified dictionaries on this real no-refresh trace
have current-model Evidence; growth and source formation are produced by the
trace. This does not prove that classification returns a dictionary. -/
theorem ordinary_initial_dictionary_evidence (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (OrdinaryStep registry root) (initial context root) state)
    (policy : ∀ demand, defer = true ∨ ¬ gap registry state demand)
    (rootStable : (boundary defer gap).Stable registry state root)
    (generatedStable : ∀ demand, Generated state.current root demand →
      (boundary defer gap).Stable registry state demand)
    (model : Assignment) (valid : Models state.current model) (dictionary : Payload)
    (derived : B4TargetV3.Classify (boundary defer gap).toSourceBoundary registry state root (.selected dictionary)) :
    Evidence registry state.current.context model root dictionary :=
  dictionary_evidence_snapshot (ordinary_initial_formed context source path)
    (ordinary_initial_extensions context path) policy rootStable generatedStable model valid
    dictionary root (Or.inl rfl) derived

/-- At a halted end of the restricted actual trace, stability of the root and
all generated demands follows from the actual closure theorem. Success of the
diagnostic classification is still an explicit antecedent. -/
theorem ordinary_halted_dictionary_evidence
    (checked : (boundary defer gap).Checked registry)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (OrdinaryStep registry root) (initial context root) state)
    (halted : ∀ after, ¬ GeneralNominalActualInspectionSteps.Step registry root state after)
    (policy : ∀ demand, defer = true ∨ ¬ gap registry state demand)
    (model : Assignment) (valid : Models state.current model) (dictionary : Payload)
    (derived : B4TargetV3.Classify (boundary defer gap).toSourceBoundary registry state root (.selected dictionary)) :
    Evidence registry state.current.context model root dictionary := by
  have reachable : B4TargetV5.Reachable (boundary defer gap) registry root state :=
    GeneralNominalActualAgreedBoundary.reachable_iff_sourceFormed.mpr
      (ordinary_initial_formed context source path)
  obtain ⟨rootStable,generatedStable⟩ := GeneralNominalActualAgreedBoundary.closure registry checked state root reachable halted
  exact ordinary_initial_dictionary_evidence context source path policy rootStable generatedStable model valid dictionary derived

end Yulang.GeneralDictionaryAgreedEvidence174
