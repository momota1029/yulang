import Yulang.GeneralDeclarativeI65I74PendingAssociatedEntry434

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.PendingAssociated434
open GeneralDeclarativeI65
open GeneralDeclarationPatterns (normalize Pattern)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDictionaryAssociatedProvenance (Supplies)
open CommonNominalFullCarrier (Ty Row Argument nominal subtype_refl Equivalent observeTy)

def literalEpisodeModel434 {s q} (a : LiteralEpisode434 s q) : I72.Model :=
  ⟨fun n => ((if n = a.seed.slot then nominal a.key [.inl (nominal a.key [.inl (.base .int)])]
                  else if n = a.a then nominal a.key [.inl (.base .int)]
                  else .base .int),Common.rowEmpty),
    fun _ => none,fun n => if n = a.seed.slot then some a.seed.endpoint else none⟩

theorem exact_episode_model_fits434 {s q} (a : LiteralEpisode434 s q) :
    I72.Fits s (literalEpisodeModel434 a) := by
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  · intro _ h; rw [a.noAtoms] at h; cases h
  · intro _ h; rw [a.noIntervals] at h; cases h
  · intro row h
    rw [a.exactRows] at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl
    · exact ⟨by simpa [literalEpisodeModel434,outerRow434,GeneralDeclarativeHead320.environment,GeneralNominalCenteredHeadMatExpressions.value,GeneralNominalCenteredHeadMatExpressions.values,a.sourceNeA.symm] using
           subtype_refl (nominal a.key [.inl (nominal a.key [.inl (.base .int)])]),
        by simpa [literalEpisodeModel434,outerRow434,GeneralDeclarativeHead320.environment,GeneralNominalCenteredHeadMatExpressions.value,GeneralNominalCenteredHeadMatExpressions.values,a.sourceNeA.symm] using
           subtype_refl (nominal a.key [.inl (nominal a.key [.inl (.base .int)])])⟩
    · exact ⟨by simpa [literalEpisodeModel434,retainedOutput434,GeneralDeclarativeHead320.environment,GeneralNominalCenteredHeadMatExpressions.value,GeneralNominalCenteredHeadMatExpressions.values,a.sourceNeA.symm,
           a.sourceNeB.symm,a.aNeB.symm] using subtype_refl (nominal a.key [.inl (.base .int)]),
        by simpa [literalEpisodeModel434,retainedOutput434,GeneralDeclarativeHead320.environment,GeneralNominalCenteredHeadMatExpressions.value,GeneralNominalCenteredHeadMatExpressions.values,a.sourceNeA.symm,
           a.sourceNeB.symm,a.aNeB.symm] using subtype_refl (nominal a.key [.inl (.base .int)])⟩
    · exact ⟨subtype_refl _,subtype_refl _⟩
  · intro _ h; rw [a.noNative] at h; cases h
  · intro o h
    rw [a.onlySeed] at h
    obtain rfl := List.mem_singleton.mp h
    simp [literalEpisodeModel434]

private theorem authored_unary_result_has_declared_nominal434
    {s : GeneralDeclarativeI65.State} {leaf c k p}
    (t : MixedRhs401 s leaf c (.app k [p]))
    (read : ∀ kind n, leaf kind n → Option (Ty × Row)) {value}
    (result : evaluateMixedRhs401 read t = some value) :
    ∃ args : List Argument, value = nominal k args := by
  cases t with
  | declaredApp _ use names modes typed =>
    simp only [evaluateMixedRhs401] at result
    cases h : evaluateMixedArgs401 read typed with
    | none => simp [h] at result
    | some args =>
      exact ⟨args,(by simpa [h] using result : nominal k args = value).symm⟩

private theorem nominal_from_index434 {s : GeneralDeclarativeI65.State} {leaf c idx k p}
    (t : MixedRhs401 s leaf c idx) (read : ∀ kind n, leaf kind n → Option (Ty × Row))
    (index : idx = .app k [p]) {value} (result : evaluateMixedRhs401 read t = some value) :
    ∃ args : List Argument, value = nominal k args := by
  cases index
  exact authored_unary_result_has_declared_nominal434 t read result

private theorem scalar_cannot_be_declared_nominal434 (k : Nat) (args : List Argument) :
    ¬ Equivalent (.base .int) (nominal k args) := by
  intro bad
  have h := bad.1 0
  rw [CommonNominalFullCarrier.observe_nominal] at h
  let env : CommonNominalFullDemand.Environment Row := ⟨fun _ => .bottom,fun _ => []⟩
  have accepted : CommonNominalFullDemand.ProbeAt Common.rowLe 0 env
      (.nominal k (args.map (CommonNominalFullCarrier.argumentAt 0)))
      (.nominalHead k (args.map (CommonNominalFullCarrier.argumentAt 0)).length) := ⟨rfl,rfl⟩
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp h 0 env _ accepted

theorem original_pending_child_has_no_dictionary_in_fitting_model434
    {s q} (o : OriginalPendingWhere434 s q) (d : CommonRoleOutermostResolver.Dictionary) :
    ¬ DictionaryEvidence s (literalEpisodeModel434 o.episode) q d := by
  intro impossible
  cases impossible with
  | node ev meaning keeps ch =>
    have dec : ev.frame.decl = o.event.frame.decl :=
      List.mem_singleton.mp (o.onlyR ▸ List.mem_of_getElem? ev.frame.authored)
    have len : q.demand.outputs.length = 1 := by rw [o.childDemandOut]; rfl
    let i : Fin q.demand.outputs.length := ⟨0,by omega⟩
    have target : q.demand.outputs[i] = ⟨o.originalBody.name,o.episode.b⟩ := by
      have e := List.getElem?_eq_getElem i.isLt
      have h : q.demand.outputs[0]? = some ⟨o.originalBody.name,o.episode.b⟩ := by rw [o.childDemandOut]; rfl
      exact Option.some.inj (e.symm.trans h)
    have atBody : (ev.outputs i).body = .explicit o.originalBody := by
      have supplies := (ev.outputs i).supplied
      generalize hb : (ev.outputs i).body = body at supplies ⊢
      cases supplies with
      | explicit eq mem name =>
        have ea : eq = o.originalBody := List.mem_singleton.mp (by simpa only [dec,o.onlyAssociated] using mem)
        rw [ea]
      | default rhs absent declared =>
        exact (absent o.originalBody (by rw [dec,o.onlyAssociated]; exact List.mem_singleton_self _) (by rw [target])).elim
    obtain ⟨value,actual,retained⟩ := keeps i
    have seen : evaluateMixedRhs401 (actualNamedMixedRead401 (literalEpisodeModel434 o.episode))
        (ev.outputs i).rhs = some value := by
      change Option.map (fun v => (q.demand.outputs[i].target,v))
        (evaluateMixedRhs401 (actualNamedMixedRead401 (literalEpisodeModel434 o.episode))
          (ev.outputs i).rhs) = some (q.demand.outputs[i].target,value) at actual
      cases v : evaluateMixedRhs401 _ (ev.outputs i).rhs with
      | none => simp [v] at actual
      | some t =>
        have eq : t = value := by simpa [v] using congrArg (Option.map Prod.snd) actual
        simp [eq]
    have pat : normalize (bodyPattern (ev.outputs i).body) = .app o.episode.key [.var o.binder.name] := by
      rw [atBody]
      simp [bodyPattern,o.bodyRhs,normalize,GeneralDeclarationPatterns.normalizeArgs]
    have impossibleValue : ∃ args, value = nominal o.episode.key args := by
      exact nominal_from_index434 (ev.outputs i).rhs _ pat seen
    obtain ⟨args,rfl⟩ := impossibleValue
    apply scalar_cannot_be_declared_nominal434 o.episode.key args
    simpa [target,literalEpisodeModel434,o.episode.sourceNeB.symm,o.episode.aNeB.symm] using retained
  | endpointLeaf ev _ _ =>
    have dec : ev.out.row = o.event.frame.decl :=
      List.mem_singleton.mp (o.onlyR ▸ List.mem_of_getElem? ev.out.authored)
    have impossibleHead := ev.out.pattern
    rw [dec,o.selectedHead] at impossibleHead
    cases impossibleHead

open CommonRoleOutermostResolver (Dictionary Summarizes Tree)
open Checker408 (Problem Result)

/-- The actual enclosing classifier cannot complete the source's original child.
The model is used to refute a supposed selected derivation using dictionary
soundness, not to authorize pending or filter the raw source graph. -/
theorem original_pending_child_is_not_selected434 {s q}
    (o : OriginalPendingWhere434 s q) (d : Dictionary) :
    ¬ Classifies R17 s q (.selected d) := by
  intro completed
  exact original_pending_child_has_no_dictionary_in_fitting_model434 o d
    (dictionary_sound_R17 s q d completed _ (exact_episode_model_fits434 o.episode))

theorem checked_pending_is_not_selected434 {p : Problem} {r : Result} {w : Wire}
    (accepted : check p r (.pendingAssociated w) = true) (d : Dictionary) :
    ¬ Classifies R17 p.state p.root (.selected d) := by
  obtain ⟨o,_,_⟩ := checked_pending_reads_actual_original_episode434 accepted
  exact original_pending_child_is_not_selected434 o.original d

theorem original_pending_parent_has_no_selected_trace434 {s q}
    (o : OriginalPendingWhere434 s q) {t : Tree} {key : Nat} {ds : List Dictionary}
    (trace : SourceTrace R17.named426 s o.parent t (some o.event)) :
    ¬ Summarizes t (.selected (.node key ds)) := by
  intro selected
  have atChild : o.event.kids[0]? = some q := by rw [o.originalChild]; rfl
  obtain ⟨kt,d,e,childTrace,_,_,summary⟩ :=
    WhereAssociated432.selected_parent_uses_actual_child_trace432 trace selected atChild
  exact original_pending_child_is_not_selected434 o d
    (legacy_classification_included426 ⟨kt,some e,⟨childTrace⟩,summary⟩)

end Yulang.GeneralDeclarativeI65.I72.PendingAssociated434
