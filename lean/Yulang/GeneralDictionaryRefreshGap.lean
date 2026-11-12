import Yulang.GeneralDictionaryJournalObstruction
import Yulang.GeneralDictionaryFeedbackEvidence
import Yulang.GeneralDictionaryRecursiveObstructionEvidence
/-! The actual unrestricted feedback EvidenceNode fails on an inhabited raw
journal with an invisible stale key. Exact refresh cannot reveal an unknown
source that admits two distinct scalar models. The same journal is proved not
SourceFormed; this is not a reachable-source or language-level counterexample.
No target or Astra definition is changed. -/
namespace Yulang.GeneralDictionaryRefreshGap
open CommonNominalFullCarrier
open GeneralDictionaryRecursiveObstruction
open GeneralDictionaryJournalObstruction

private theorem int_not_nominal (name : Nat) (arguments : List Argument) : ¬ Subtype (.base .int) (nominal name arguments) := by
  intro below
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.nominalHead name arguments.length) ⟨rfl,by simp⟩

private theorem int_not_shape (shape : GeneralNormalizedObservation.Shape)
    (children : Fin shape.arity → Fin slots)
    (assignment : Fin slots → Core.PresenceGeneration.Comp CommonNominalFullCarrier.model) :
    ¬ Subtype (.base .int) ((shape.term children).eval CommonNominalFullCarrier.model assignment) := by
  intro below
  let role : CommonNominalFullDemand.Head := match shape with
    | .pair => .pair | .variant tag => .variant tag | _ => .records
  have probe := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0
    ⟨fun _ => .bottom,fun _ => [role]⟩ (.role 0)
  cases shape with
  | pair | variant | exactEmpty =>
    simp [role, GeneralNormalizedObservation.Shape.term,Core.PresenceGeneration.TyTerm.eval,
      CommonNominalFullCarrier.model,CommonNominalFullCarrier.pair,CommonNominalFullCarrier.variant,observeTy,CommonNominalSyntax.Layer.evalAt,
      CommonNominalFullDemand.ProbeAt,CommonNominalFullDemand.ProbeStep,CommonNominalFullDemand.MaskedProbeStep] at probe
  | record labels =>
    cases labels <;>
      simp [role, GeneralNormalizedObservation.Shape.term,GeneralNormalizedObservation.recordTerm,List.ofFn_succ,
        Core.PresenceGeneration.TyTerm.eval,CommonNominalFullCarrier.model,CommonNominalFullCarrier.record,
        observeTy,CommonNominalSyntax.Layer.evalAt,CommonNominalFullDemand.ProbeAt,
        CommonNominalFullDemand.ProbeStep,CommonNominalFullDemand.MaskedProbeStep] at probe

/-- Two distinct scalar models prevent any certified known normalized head. -/
theorem no_known (state : GeneralNominalState.State)
    (one : GeneralNominalState.Models state GeneralNominalExamples.model)
    (two : GeneralNominalState.Models state badModel) :
    ¬ GeneralNominalState.Known state 1 := by
  rintro ⟨slot,source,head | ⟨descriptor,recorded⟩⟩
  · have seen1 := GeneralNominalState.normalized_models state _ one
    have seen2 := GeneralNominalState.normalized_models state _ two
    cases equation : state.view.heads slot with
    | deferred reason => exact head (by simp [GeneralNormalizedObservation.Snapshot.graph,equation,GeneralNormalizedObservation.Head.node])
    | scalar base =>
      have a := seen1 slot (.base base) (by simp [equation,GeneralNormalizedObservation.Head.term])
      have b := seen2 slot (.base base) (by simp [equation,GeneralNormalizedObservation.Head.term])
      have x : Equivalent (.base .int) (.base base) := by simpa [source,Core.PresenceGeneration.TyTerm.eval,CommonNominalFullCarrier.model] using a
      have y : Equivalent (.base .str) (.base base) := by simpa [source,Core.PresenceGeneration.TyTerm.eval,CommonNominalFullCarrier.model] using b
      exact bad_output_equation ⟨subtype_trans y.1 x.2,subtype_trans x.1 y.2⟩
    | structural kind children =>
      have a := seen1 slot ((state.view.shapes kind).term children) (by simp [equation,GeneralNormalizedObservation.Head.term])
      exact int_not_shape _ children _ (by simpa [source,Core.PresenceGeneration.TyTerm.eval,CommonNominalFullCarrier.model] using a.1)
  · obtain ⟨values,_,equal⟩ := one.2.1 slot descriptor recorded
    exact int_not_nominal _ _ (by simpa [GeneralNominalState.Denotes,source] using equal.1)


open GeneralNominalSaturationState
open GeneralDeclarationExamples (roles)
open GeneralSourceDictionaries

theorem good_journal_model : Models journal GeneralNominalExamples.model :=
  (journal_models _).mpr (GeneralNominalExamples.state_models false)

theorem refresh_unknown (after : GeneralNominalCandidates.Context)
    (certificate : GeneralNominalFeedbackSteps.Refresh journal after) :
    ¬ GeneralNominalState.Known after.state 1 :=
  no_known after.state (certificate.exact _ good_journal_model)
    (certificate.exact _ bad_journal_model)

theorem generated_only_root (child : Occurrence roles) (generated : Generated journal root child) : child = root := by
  induction generated with
  | root => rfl
  | child _ member _ => cases member
  | alias _ _ member _ _ =>
    have same := List.mem_singleton.mp member
    exact congrArg GeneralNominalDemandMerging.Site.occurrence same

theorem no_install (p : Packet roles) (same : p.site.occurrence = root) :
    ¬ GeneralNominalFeedbackSteps.Installable registry journal p := by
  intro enabled
  have visible := enabled.1.2.2.2.1
  have declarationEq : p.declaration = declaration := List.mem_singleton.mp visible
  have compatible := enabled.1.2.2.2.2.2.2.2.2.1
  have alias : Alias journal p.site.occurrence.identity stalePacket.site.occurrence.identity := by
    rw [same]
    exact .refl 300
  have conflict := compatible stalePacket (List.mem_singleton_self _) alias
  rw [declarationEq] at conflict
  cases conflict

theorem stable : GeneralNominalFeedbackSteps.Stable registry journal root := by
  intro focus generated after update
  have same := generated_only_root focus generated
  cases update with
  | enqueue focus _ absent => exact absent _ (List.mem_singleton_self _) same.symm
  | install p enabled _ => exact no_install p same enabled
  | merge first last one two _ novel =>
    have a := List.mem_singleton.mp one
    have b := List.mem_singleton.mp two
    subst first; subst last
    exact novel (.refl _)
  | refresh _ after certificate source member unknown known =>
    have alternatives : source = 0 ∨ source = 1 := by
      simp [GeneralNominalState.sources,List.ofFn_succ] at member
      rcases member with h | h | h | h <;> simp [h]
    rcases alternatives with rfl | rfl
    · exact unknown ⟨0,rfl,Or.inr ⟨GeneralNominalExamples.listDescriptor,rfl⟩⟩
    · exact refresh_unknown after certificate known
  | equate _ first last _ _ equal novel =>
    exact novel (fun model valid => equal model ((journal_models model).mpr valid))
theorem edge_shape (first last : Nat) (edge : GeneralNominalFeedbackK2.Edge journal first last) : first = 0 ∧ last = 1 := by
  have lastCases : last = 0 ∨ last = 1 := by
    have member := edge.2.1
    simp [GeneralNominalState.sources,List.ofFn_succ] at member
    rcases member with h | h | h | h <;> simp [h]
  rcases edge.2.2 with ⟨parent,child,⟨kind,_,_,_,_⟩,_,_⟩ | ⟨name,index,observed⟩
  · exact Fin.elim0 kind
  · obtain ⟨actual,seen,equal⟩ := observed GeneralNominalExamples.model good_journal_model
    cases seen with
    | argument source compared found =>
      cases source
      have zero : first = 0 := by
        by_cases zero : first = 0
        · exact zero
        · exact False.elim (int_not_nominal _ _ (by simpa [GeneralNominalExamples.model,zero] using compared.1))
      subst first
      have invariant := (nominal_regular_invariant_exact _ _ _ _).mp compared.1
      have size := invariant.2.1
      have indexZero : index = 0 := by
        obtain ⟨bound,_⟩ := List.getElem?_eq_some_iff.mp found
        simp only [List.length_cons,List.length_nil] at size
        omega
      subst index
      have arg := invariant.2.2 0 (.inl (.base .int)) (.inl actual) rfl found
      refine ⟨rfl,?_⟩
      rcases lastCases with rfl | one
      · exact False.elim (int_not_nominal _ _ (subtype_trans arg.1 equal.1))
      · exact one

theorem acyclic (source : Nat) : ¬ GeneralNominalFeedbackK2.Cycle journal source := by
  rintro ⟨next,edge,path⟩
  have shape := edge_shape source next edge
  cases path with
  | nil => omega
  | cons second _ => have another := edge_shape _ _ second; omega

private theorem old_edge (first last : Fin 2) (edge : GeneralNominalMixedRecurrence.Edge context.state first last) :
    GeneralNominalFeedbackK2.Edge journal first.val last.val := by
  refine ⟨?_,?_,?_⟩
  · simp [GeneralNominalState.sources,List.ofFn_succ]; omega
  · simp [GeneralNominalState.sources,List.ofFn_succ]; omega
  · rcases edge with ⟨kind,_,_,_,_⟩ | argument
    · exact Fin.elim0 kind
    · exact Or.inr (GeneralNominalFeedbackK2.actual_argument journal first last argument)

private theorem old_path (first last : Fin 2) (path : GeneralNominalMixedRecurrence.Path context.state first last) :
    GeneralNominalFeedbackK2.Path journal first.val last.val := by
  exact GeneralNominalMixedRecurrence.Path.rec
    (motive := fun first last _ => GeneralNominalFeedbackK2.Path journal first.val last.val)
    (fun _ => .nil _) (fun edge _ ih => .cons (old_edge _ _ edge) ih) path

theorem old_acyclic (slot : Fin 2) : ¬ GeneralNominalCycleK2.RecursAt context.state slot := by
  intro recurrent
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ recurrent
  exact acyclic slot.val ⟨next.val,old_edge _ _ edge,old_path _ _ path⟩


theorem selected : GeneralNominalFeedbackK2.Local registry journal root (.selected 40 []) := by
  refine .selected ⟨not_pending,?_,?_,?_⟩ unique
  · rintro (⟨_,_,_,slot,_,recurs⟩ | ⟨_,_,_,cycle,_⟩)
    · exact old_acyclic slot recurs
    · exact acyclic _ cycle
  · rintro (⟨_,_,_,_,_,_,_,_,visited,_,recurs⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
    · exact old_acyclic visited.1 recurs
    · exact acyclic _ cycle
  · rintro (⟨_,decl,visible,checked,_,_,unprepared⟩ | ⟨_,legacy⟩)
    · have same := List.mem_singleton.mp visible
      subst decl
      exact unprepared prepared
    · rcases legacy with ⟨bad,_⟩ | ⟨bad,_⟩
      · exact not_rootK2 bad
      · exact not_candidateK2 bad

/-- The actual unrestricted raw-journal feedback EvidenceNode obligation fails. -/
theorem no_evidenceNode : ¬ B4SkeletonV4.EvidenceNode (GeneralDictionaryFeedbackEvidence.boundary roles) := by
  intro claimed
  have localRule := selected
  cases localRule with
  | selected safe unique =>
    exact bad_not_evidence (claimed registry ⟨rfl,registry_checked⟩ journal badModel bad_journal_model
      root 40 [] [] stable (by intro child member; cases member) safe unique .nil)

/-- The stale packet cannot arise in the existing source-formation invariant. -/
theorem not_sourceFormed : ¬ GeneralNominalFeedbackSteps.SourceFormed registry root journal := by
  intro formed
  have source := (GeneralDictionaryFeedbackEvidence.sourceFormed_recorded_instances registry root journal formed
    stalePacket (List.mem_singleton_self _)).1 GeneralNominalExamples.model good_journal_model
  obtain ⟨decl,visible,_,identity,_⟩ := source
  have same := List.mem_singleton.mp visible
  subst decl
  cases identity
end Yulang.GeneralDictionaryRefreshGap
