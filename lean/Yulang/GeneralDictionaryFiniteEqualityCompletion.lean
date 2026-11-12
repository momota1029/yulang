import Yulang.GeneralDictionaryEqualityObservations
import Yulang.GeneralNominalSupportSteps
import Yulang.GeneralDictionaryJointEquality
import Yulang.GeneralDictionaryOrdinaryTrace

/-! A finite equality-feedback subphase of the actual support transition.
No claim that its endpoint is Stable: installation, refresh and merges remain. -/
namespace Yulang.GeneralDictionaryFiniteEqualityCompletion
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalFeedbackSteps GeneralNominalSupportSteps
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls}

private theorem paths_append {α : Type} {R : α → α → Prop} {a b c : α}
    (first : B4Target.Steps R a b) (last : B4Target.Steps R b c) :
    B4Target.Steps R a c := by
  induction last with
  | refl => exact first
  | tail _ step ih => exact .tail ih step

/-- Every finite list of journal-entailed equalities on existing sources can be
materialized by actual administrative steps. Already raw-entailed pairs cause
no step. The same journal models survive, and no source is introduced. -/
theorem complete_list (registry : Registry) (root : Occurrence roles)
    (pairs : List (Nat × Nat)) (before : GeneralNominalSupport.Tracked roles)
    (sources : ∀ p ∈ pairs, p.1 ∈ GeneralNominalState.sources before.current.context.state ∧
      p.2 ∈ GeneralNominalState.sources before.current.context.state)
    (equal : ∀ p ∈ pairs, GeneralNominalFeedbackK2.Equal before.current p.1 p.2) :
    ∃ after : GeneralNominalSupport.Tracked roles,
      B4Target.Steps (GeneralNominalSupportSteps.Step registry root) before after ∧
      (∀ model, Models after.current model ↔ Models before.current model) ∧
      (∀ model, GeneralNominalState.Models after.current.context.state model →
        GeneralNominalState.Models before.current.context.state model) ∧
      (∀ source, source ∈ GeneralNominalState.sources after.current.context.state ↔
        source ∈ GeneralNominalState.sources before.current.context.state) ∧
      GeneralDictionaryOrdinaryTrace.Extension before.current.context after.current.context ∧
      GeneralDictionaryEqualityObservations.Equates before.current after.current ∧
      (∀ p ∈ pairs, RawEqual after.current p.1 p.2) := by
  classical
  induction pairs generalizing before with
  | nil => exact ⟨before,.refl,(fun _ => Iff.rfl),(fun _ h => h),(fun _ => Iff.rfl),GeneralDictionaryOrdinaryTrace.extension_refl _,(.refl _),by simp⟩
  | cons p ps ih =>
    have one := (sources p (by simp)).1
    have two := (sources p (by simp)).2
    have eq := equal p (by simp)
    by_cases raw : RawEqual before.current p.1 p.2
    · obtain ⟨after,path,models,rawModels,domain,growth,journal,done⟩ := ih before
        (fun q h => sources q (by simp [h])) (fun q h => equal q (by simp [h]))
      refine ⟨after,path,models,rawModels,domain,growth,journal,?_⟩
      intro q h
      rcases List.mem_cons.mp h with rfl | h
      · exact fun model valid => raw model (rawModels model valid)
      · exact done q h
    · let next : GeneralNominalSupport.Tracked roles :=
        {before with current := equate before.current p.1 p.2}
      have step : GeneralNominalSupportSteps.Step registry root before next :=
        ⟨root,.root,.administrative root _ (.equate root p.1 p.2 one two eq raw)⟩
      have nextModels (model : Assignment) : Models next.current model ↔ Models before.current model :=
        equate_models before.current p.1 p.2 eq model
      have nextDomain (source : Nat) :
          source ∈ GeneralNominalState.sources next.current.context.state ↔
          source ∈ GeneralNominalState.sources before.current.context.state :=
        GeneralDictionaryJointEquality.sources_equate before.current p.1 p.2 source one two
      have nextRaw (model : Assignment) (valid : GeneralNominalState.Models next.current.context.state model) :
          GeneralNominalState.Models before.current.context.state model :=
        ((GeneralNominalState.extend_models _ _ _ model).mp valid).1
      obtain ⟨after,path,models,rawModels,domain,growth,journal,done⟩ := ih next
        (fun q h => ⟨(nextDomain q.1).mpr (sources q (by simp [h])).1,
          (nextDomain q.2).mpr (sources q (by simp [h])).2⟩)
        (fun q h model valid => equal q (by simp [h]) model ((nextModels model).mp valid))
      refine ⟨after,paths_append (.tail .refl step) path,
        (fun model => (models model).trans (nextModels model)),
        (fun model valid => nextRaw model (rawModels model valid)),
        (fun source => (domain source).trans (nextDomain source)),
        GeneralDictionaryOrdinaryTrace.extension_trans
          (GeneralDictionaryOrdinaryTrace.equate_extension _ _ _) growth,
        GeneralDictionaryEqualityObservations.Equates.trans (.tail (.refl _) p.1 p.2 one two eq) journal,?_⟩
      intro q h
      rcases List.mem_cons.mp h with rfl | h
      · exact fun model valid => equate_feedback before.current q.1 q.2 model (rawModels model valid)
      · exact done q h

/-- Equality-complete only on the finite source domain. This does not assert
Stable, nor change the support transition or choose new dictionary evidence. -/
def EqualityComplete (state : State roles) : Prop :=
  ∀ first ∈ GeneralNominalState.sources state.context.state,
    ∀ last ∈ GeneralNominalState.sources state.context.state,
      GeneralNominalFeedbackK2.Equal state first last → RawEqual state first last

/-- Every tracked journal has a finite real equality-feedback completion. Its
model set and source domain are exactly unchanged; no consistency hypothesis
is necessary (including the empty model set). -/
theorem complete_sources (registry : Registry) (root : Occurrence roles)
    (before : GeneralNominalSupport.Tracked roles) :
    ∃ after : GeneralNominalSupport.Tracked roles,
      B4Target.Steps (GeneralNominalSupportSteps.Step registry root) before after ∧
      (∀ model, Models after.current model ↔ Models before.current model) ∧
      (∀ source, source ∈ GeneralNominalState.sources after.current.context.state ↔
        source ∈ GeneralNominalState.sources before.current.context.state) ∧
      GeneralDictionaryOrdinaryTrace.Extension before.current.context after.current.context ∧
      GeneralDictionaryEqualityObservations.Equates before.current after.current ∧
      EqualityComplete after.current := by
  classical
  let sources := GeneralNominalState.sources before.current.context.state
  let pairs := (sources.flatMap (fun a => sources.map (fun b => (a,b)))).filter
    (fun p => decide (GeneralNominalFeedbackK2.Equal before.current p.1 p.2))
  have member (p : Nat × Nat) : p ∈ pairs ↔
      p.1 ∈ sources ∧ p.2 ∈ sources ∧ GeneralNominalFeedbackK2.Equal before.current p.1 p.2 := by
    rcases p with ⟨a,b⟩
    simp [pairs,List.mem_flatMap,List.mem_map,Prod.mk.injEq,and_assoc]
  obtain ⟨after,path,models,_,domain,growth,journal,done⟩ := complete_list registry root pairs before
    (fun p h => ⟨((member p).mp h).1,((member p).mp h).2.1⟩)
    (fun p h => ((member p).mp h).2.2)
  refine ⟨after,path,models,domain,growth,journal,?_⟩
  intro first one last two equal
  apply done (first,last)
  apply (member _).mpr
  exact ⟨(domain first).mp one,(domain last).mp two,
    fun model valid => equal model ((models model).mpr valid)⟩

/-- Starting from the actual support-reachability predicate preserves it. -/
theorem complete_sourceformed (registry : Registry) (root : Occurrence roles)
    (before : GeneralNominalSupport.Tracked roles)
    (formed : GeneralNominalSupportSteps.SourceFormed registry root before) :
    ∃ after, GeneralNominalSupportSteps.SourceFormed registry root after ∧ EqualityComplete after.current ∧
      (∀ model, Models after.current model ↔ Models before.current model) := by
  obtain ⟨after,path,models,domain,growth,journal,done⟩ := complete_sources registry root before
  refine ⟨after,?_,done,models⟩
  clear models domain growth journal done
  induction path with
  | refl => exact formed
  | tail _ step ih => exact .update ih step

/-- One and the same endpoint preserves every full recursive Evidence judgment
under every surviving journal assignment, rather than choosing separate models. -/
theorem complete_evidence (registry : Registry) (root : Occurrence roles)
    (before : GeneralNominalSupport.Tracked roles) :
    ∃ after : GeneralNominalSupport.Tracked roles,
      B4Target.Steps (GeneralNominalSupportSteps.Step registry root) before after ∧
      EqualityComplete after.current ∧
      (∀ model, Models after.current model ↔ Models before.current model) ∧
      (∀ model, Models before.current model → ∀ focus : Occurrence roles,
        ∀ payload : GeneralDictionaryReadback.Payload,
        GeneralDictionaryRecursiveEvidence.Evidence registry after.current.context model focus payload ↔
        GeneralDictionaryRecursiveEvidence.Evidence registry before.current.context model focus payload) := by
  obtain ⟨after,path,models,_,growth,_,done⟩ := complete_sources registry root before
  refine ⟨after,path,done,models,?_⟩
  intro model valid focus payload
  exact ⟨GeneralDictionaryOrdinaryTrace.evidence_extension_backward registry _ _ growth model focus payload,
    GeneralDictionaryOrdinaryTrace.evidence_extension registry _ _ growth model
      ((models model).mpr valid).1 focus payload⟩

/-- All equality-rule side conditions are incompatible at a completed journal.
Other administrative rules, and hence full Stable, are deliberately not ruled out. -/
theorem no_fresh_equality (state : State roles) (complete : EqualityComplete state)
    (first last : Nat)
    (one : first ∈ GeneralNominalState.sources state.context.state)
    (two : last ∈ GeneralNominalState.sources state.context.state)
    (equal : GeneralNominalFeedbackK2.Equal state first last) :
    ¬ (¬ RawEqual state first last) := by
  exact fun fresh => fresh (complete first one last two equal)

end Yulang.GeneralDictionaryFiniteEqualityCompletion
