import Yulang.GeneralDictionaryVariableJournalMerge
import Yulang.GeneralDictionaryMergeSequence

/-! Historical repeated-variable materialization discharges every equation in
an arbitrary finite merge-only fold. This is semantic preservation, not an
executor, enabled support trace, or Joint amalgamation theorem. -/
namespace Yulang.GeneralDictionaryVariableMergeSequence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalDemandMerging (Site outputAtoms)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryVariableJournalMerge (Requests)
variable {roles : Roles.RoleDecls}

/-- One historical packet covers all events. The binder-name map may vary
between events; both sides of each event must use its same map. -/
def Covered (packet : Packet roles) (events : List (Site roles × Site roles)) : Prop :=
  ∀ pair ∈ events, ∃ names : Nat → Nat,
    Requests packet pair.1 names ∧ Requests packet pair.2 names

/-- Actual materialization, not an assumed associated interpretation, supplies
the entire conjunction of equations at each original journal assignment. -/
theorem output_atoms (state : State roles) (packet : Packet roles)
    (recorded : packet ∈ state.packets) (events : List (Site roles × Site roles))
    (covered : Covered packet events) (model : Assignment) (valid : Models state model) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (events.flatMap (fun pair => outputAtoms pair.1 pair.2)) := by
  intro atom present
  obtain ⟨pair,member,present⟩ := List.mem_flatMap.mp present
  obtain ⟨names,left,right⟩ := covered pair member
  exact GeneralDictionaryVariableJournalMerge.outputs_from_packet state pair.1 pair.2 packet
    recorded names left right model valid atom present

/-- No original journal assignment is lost by any covered finite fold. The
reverse implication requires no consistency assumption. -/
theorem models_fold_iff (state : State roles) (packet : Packet roles)
    (recorded : packet ∈ state.packets) (events : List (Site roles × Site roles))
    (covered : Covered packet events) (model : Assignment) :
    Models (events.foldl (fun current pair => merge current pair.1 pair.2) state) model ↔
      Models state model := by
  rw [GeneralDictionaryMergeSequence.models_fold]
  exact ⟨fun h => h.1,fun h => ⟨h,output_atoms state packet recorded events covered model h⟩⟩

/-- Full dictionaries retain their exact payload at the SAME original journal
assignment, through the whole finite fold. -/
theorem evidence_fold_iff (registry : Registry) (state : State roles) (packet : Packet roles)
    (recorded : packet ∈ state.packets) (events : List (Site roles × Site roles))
    (covered : Covered packet events) (model : Assignment) (valid : Models state model)
    (root : Occurrence roles) (payload : GeneralDictionaryReadback.Payload) :
    GeneralDictionaryRecursiveEvidence.Evidence registry
      (events.foldl (fun current pair => merge current pair.1 pair.2) state).context model root payload ↔
      GeneralDictionaryRecursiveEvidence.Evidence registry state.context model root payload := by
  rw [GeneralDictionaryMergeSequence.evidence_fold]
  exact ⟨fun h => h.1,fun h => ⟨h,output_atoms state packet recorded events covered model valid⟩⟩

/-- Reuse event-set invariance: arbitrary order and multiplicity preserve the
original model set, with coverage checked only on the original event list. -/
theorem reordered_models (state : State roles) (packet : Packet roles)
    (recorded : packet ∈ state.packets) (events reordered : List (Site roles × Site roles))
    (covered : Covered packet events) (same : ∀ pair, pair ∈ reordered ↔ pair ∈ events)
    (model : Assignment) :
    Models (reordered.foldl (fun current pair => merge current pair.1 pair.2) state) model ↔
      Models state model :=
  (GeneralDictionaryMergeSequence.models_events_iff state reordered events same model).trans
    (models_fold_iff state packet recorded events covered model)

/-- Reordering/repetition needs no reclassification of the stored packet and
no separate assignment for each event or each subtree. -/
theorem reordered_evidence (registry : Registry) (state : State roles) (packet : Packet roles)
    (recorded : packet ∈ state.packets) (events reordered : List (Site roles × Site roles))
    (covered : Covered packet events) (same : ∀ pair, pair ∈ reordered ↔ pair ∈ events)
    (model : Assignment) (valid : Models state model)
    (root : Occurrence roles) (payload : GeneralDictionaryReadback.Payload) :
    GeneralDictionaryRecursiveEvidence.Evidence registry
      (reordered.foldl (fun current pair => merge current pair.1 pair.2) state).context model root payload ↔
      GeneralDictionaryRecursiveEvidence.Evidence registry state.context model root payload :=
  (GeneralDictionaryMergeSequence.evidence_events_iff registry state reordered events same model root payload).trans
    (evidence_fold_iff registry state packet recorded events covered model valid root payload)
end Yulang.GeneralDictionaryVariableMergeSequence
