import Yulang.GeneralDeclarativeI65I74NestedInvariantRead440

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NestedInvariant440
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open Checker408 (Result)
open CommonRoleOutermostResolver (Dictionary Summarizes)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeInspect321 (Visit PatternK2)
open GeneralDeclarativeGraphRows321 (observed structural)
open GeneralDeclarativeK2Alias321 (AliasCycle)

def Original.candidate {s q d} (a : Original s q d) : AuthoredCandidate s.core q d :=
  ⟨by simp [a.only],a.covered,a.checked.signature,a.head⟩

def Original.tape {s q d} (a : Original s q d) :
    CandidateTape s.core q (visible s.core q) :=
  a.only.symm ▸ .next (.matched a.candidate) .nil

theorem Original.picked {s q d} (a : Original s q d) :
    TapedMatch s.core q a.tape d := by
  have characteristics : ∀ rows (same : rows = [d]),
      let t : CandidateTape s.core q rows := same.symm ▸ .next (.matched a.candidate) .nil
      t.waits = false ∧ t.live = [d] := by
    intro rows same
    cases same
    exact ⟨rfl,rfl⟩
  exact ⟨a.rootSafe,(characteristics _ a.only).1,(characteristics _ a.only).2⟩

theorem Original.allOriginalOrigins {s q d} (a : Original s q d)
    (m : I72.Model) (fit : I72.Fits s m) :
    m.nativeSyntax a.arg.lower = some (nestedEndpoint a.outer a.inner a.low a.high) ∧
    m.nativeSyntax a.site = some (nestedInner a.inner a.low a.high) := by
  have outer := fit.2 a.root a.source
  have inner := fit.2 a.innerSource a.innerAuthored
  exact ⟨by simpa only [a.rootLower,a.endpoint] using outer,
    by simpa only [a.innerSlot,a.innerEndpoint] using inner⟩

structure Local {s : I72.State} {q : Request} (e : Event s q) where
  original : Original s q e.frame.decl
  head : e.head = original.head
  preoutput : e.frame.input = preoutputInputOfHead399 e.head (fun _ => emptyCapture403)

def nestedLocal : SourcePrimitives where
  elected := fun _ _ e needs => needs = [] ∧ Nonempty (Local e)
  other := fun _ _ _ _ => False

theorem Local.noKids {s q} {e : Event s q} (a : Local e) : e.kids = [] := by
  simp [Event.kids,frameWhereKids400,AuthoredBodyFrame393.clauses,a.original.noWhere,children]

theorem Local.noIndex {s q} {e : Event s q} (a : Local e)
    (i : Fin q.demand.outputs.length) : False := by
  have natural := i.isLt
  simp [a.original.noOutputs] at natural

theorem Local.evidence {s q} {e : Event s q} (a : Local e)
    (m : I72.Model) (fit : I72.Fits s m) :
    I72.DictionaryEvidence s m q (.node e.frame.decl.id []) := by
  refine .node e ?_ ?_ (a.noKids ▸ .nil)
  · exact semantic_node_in_signature s q e
      (node_from_exact_preoutput_head405 e a.original.checked (fun _ => emptyCapture403) a.preoutput)
      m fit
  · intro i
    exact (a.noIndex i).elim

theorem nested_only_dictionary_sound440 : I72.DictionarySound nestedLocal := by
  intro s q d chosen m fit
  obtain ⟨tree,_,⟨t⟩,summary⟩ := chosen
  cases t with
  | rootK2 _ => cases summary
  | other _ _ bad _ => exact bad.elim
  | selected e _ elected _ f =>
    obtain ⟨a⟩ := elected.2
    have nil : _ = [] := a.noKids
    rw [nil] at f
    cases f
    have exactResult := (CommonRoleOutermostResolver.classification_exact _ _).mpr summary
    change CommonRoleOutermostResolver.Result.selected (.node e.frame.decl.id []) = .selected d at exactResult
    cases exactResult
    exact a.evidence m fit

def leafReport (d : Declaration) : Result := Check408.nullaryReport d

theorem actual_nested_selected_trace440 {s q d} (a : Original s q d) :
    ∃ (event : Event s q) (_actual : SourceTrace nestedLocal s q (leafReport d).tree (some event)),
      Nonempty (Local event) ∧
      event.frame.input a.binder = ⟨a.low,a.center,a.high⟩ ∧
      Check408.encodedEventWrites event = [] ∧ event.kids = [] := by
  obtain ⟨origin⟩ := selected_head_original_origin395 a.picked
  have samePick : origin.pick = a.candidate := by
    have one : ∀ rows (same : rows = [d]),
        let t : CandidateTape s.core q rows := same.symm ▸ .next (.matched a.candidate) .nil
        storedCandidateEntries401 t = [(0,⟨d,a.candidate⟩)] := by
      intro rows eq
      cases eq
      rfl
    have sight := original_stored_entry_is_listed401 origin.stored
    change (origin.visibleOrdinal,⟨d,origin.pick⟩) ∈ storedCandidateEntries401 a.tape at sight
    unfold Original.tape at sight
    rw [one _ a.only] at sight
    exact eq_of_heq (Sigma.mk.inj (congrArg Prod.snd (List.mem_singleton.mp sight))).2
  have empty : ∀ i : Fin q.demand.outputs.length, False := by
    intro i
    have bad := i.isLt
    simp [a.noOutputs] at bad
  let event : Event s q := ⟨preoutputFrameOfOrigin399 origin unusedPlacement403 (fun _ => emptyCapture403),
    origin.pick.head,fun i => (empty i).elim⟩
  have head : event.head = a.head := congrArg AuthoredCandidate.head samePick
  let chosen : Local event := ⟨a,head,rfl⟩
  let trace : SourceTrace nestedLocal s q (leafReport d).tree (some event) :=
    .selected event a.rootSafe ⟨rfl,⟨chosen⟩⟩ .nil (chosen.noKids ▸ .nil)
  have capture : event.frame.input a.binder = ⟨a.low,a.center,a.high⟩ := by
    change preoutputInputOfHead399 origin.pick.head (fun _ => emptyCapture403) a.binder = _
    rw [samePick]
    change a.capture a.binder = _
    simp [Original.capture]
  have zero : Check408.encodedEventWrites event = [] :=
    List.length_eq_zero_iff.mp (by simp [Check408.encodedEventWrites,a.noOutputs])
  exact ⟨event,trace,⟨chosen⟩,capture,zero,chosen.noKids⟩

theorem actual_nested_classifies440 {s q d} (a : Original s q d) :
    I72.Classifies nestedLocal s q (.selected (.node d.id [])) := by
  obtain ⟨ev,trace,_,_,_,_⟩ := actual_nested_selected_trace440 a
  exact ⟨(leafReport d).tree,some ev,⟨trace⟩,.selected .nil (.selected rfl)⟩

end Yulang.GeneralDeclarativeI65.I72.NestedInvariant440
