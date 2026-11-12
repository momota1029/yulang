import Yulang.GeneralDictionaryJointMerge

/-! Finite compositions of the existing merge state transformer. This fold is
not an executor: membership, SameInputs, guards, novelty, and reachability are
not inferred. Every equation is retained at the same assignment. -/
namespace Yulang.GeneralDictionaryMergeSequence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalDemandMerging (Site outputAtoms)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls}

/-- Exact model condition for a finite list of actual output-equation merges. -/
theorem models_fold (state : State roles) (steps : List (Site roles × Site roles))
    (model : Assignment) :
    Models (steps.foldl (fun current pair => merge current pair.1 pair.2) state) model ↔
      Models state model ∧ PresenceNormalForm.All CommonNominalFullCarrier.model model
        (steps.flatMap (fun pair => outputAtoms pair.1 pair.2)) := by
  induction steps generalizing state with
  | nil => simp
  | cons pair rest ih =>
    simp only [List.foldl_cons,List.flatMap_cons,ih,merge_models,PresenceNormalForm.all_append]
    exact and_assoc

/-- Full recursive source dictionaries survive the finite fold exactly when
all accumulated named-output equations hold at their original model. -/
theorem evidence_fold (registry : Registry) (state : State roles)
    (steps : List (Site roles × Site roles)) (model : Assignment)
    (root : Occurrence roles) (payload : GeneralDictionaryReadback.Payload) :
    GeneralDictionaryRecursiveEvidence.Evidence registry
      (steps.foldl (fun current pair => merge current pair.1 pair.2) state).context model root payload ↔
      GeneralDictionaryRecursiveEvidence.Evidence registry state.context model root payload ∧
      PresenceNormalForm.All CommonNominalFullCarrier.model model
        (steps.flatMap (fun pair => outputAtoms pair.1 pair.2)) := by
  induction steps generalizing state with
  | nil => simp
  | cons pair rest ih =>
    simp only [List.foldl_cons,List.flatMap_cons,ih,
      GeneralDictionaryJointMerge.evidence_merge_iff,PresenceNormalForm.all_append]
    exact and_assoc

/-- A model of the final fold can read every earlier full dictionary; no
separate existential witnesses are chosen for the individual merge events. -/
theorem evidence_at_final_model (registry : Registry) (state : State roles)
    (steps : List (Site roles × Site roles)) (model : Assignment)
    (valid : Models (steps.foldl (fun current pair => merge current pair.1 pair.2) state) model)
    (root : Occurrence roles) (payload : GeneralDictionaryReadback.Payload)
    (given : GeneralDictionaryRecursiveEvidence.Evidence registry state.context model root payload) :
    GeneralDictionaryRecursiveEvidence.Evidence registry
      (steps.foldl (fun current pair => merge current pair.1 pair.2) state).context model root payload :=
  (evidence_fold registry state steps model root payload).mpr
    ⟨given,((models_fold state steps model).mp valid).2⟩

/-- Repetition and ordering of the same merge pairs do not change their
conjoined output equations. This does not compare operationally enabled runs. -/
theorem event_atoms_iff (first last : List (Site roles × Site roles))
    (same : ∀ pair, pair ∈ first ↔ pair ∈ last) (model : Assignment) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (first.flatMap (fun pair => outputAtoms pair.1 pair.2)) ↔
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (last.flatMap (fun pair => outputAtoms pair.1 pair.2)) := by
  constructor
  · intro valid atom member
    obtain ⟨pair,present,member⟩ := List.mem_flatMap.mp member
    exact valid atom (List.mem_flatMap.mpr ⟨pair,(same pair).mpr present,member⟩)
  · intro valid atom member
    obtain ⟨pair,present,member⟩ := List.mem_flatMap.mp member
    exact valid atom (List.mem_flatMap.mpr ⟨pair,(same pair).mp present,member⟩)

/-- Model sets of merge-only folds depend on the set of events, not order or
multiplicity. No assertion about source selection or executor termination. -/
theorem models_events_iff (state : State roles)
    (first last : List (Site roles × Site roles))
    (same : ∀ pair, pair ∈ first ↔ pair ∈ last) (model : Assignment) :
    Models (first.foldl (fun current pair => merge current pair.1 pair.2) state) model ↔
    Models (last.foldl (fun current pair => merge current pair.1 pair.2) state) model := by
  rw [models_fold,models_fold,event_atoms_iff first last same model]

/-- The identical source-indexed payload has identical recursive meaning
under any reordering or repetition of the same finite merge events. -/
theorem evidence_events_iff (registry : Registry) (state : State roles)
    (first last : List (Site roles × Site roles))
    (same : ∀ pair, pair ∈ first ↔ pair ∈ last) (model : Assignment)
    (root : Occurrence roles) (payload : GeneralDictionaryReadback.Payload) :
    GeneralDictionaryRecursiveEvidence.Evidence registry
      (first.foldl (fun current pair => merge current pair.1 pair.2) state).context model root payload ↔
    GeneralDictionaryRecursiveEvidence.Evidence registry
      (last.foldl (fun current pair => merge current pair.1 pair.2) state).context model root payload := by
  rw [evidence_fold,evidence_fold,event_atoms_iff first last same model]

end Yulang.GeneralDictionaryMergeSequence
