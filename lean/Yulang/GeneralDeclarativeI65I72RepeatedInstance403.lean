import Yulang.GeneralDeclarativeI65I72RepeatedChoice403

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Dictionary Result Tree Summarizes)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDictionaryAssociatedProvenance (Body Supplies)
open GeneralDeclarativeOutputs320 (bodyPattern)
open GeneralDeclarationPatterns (normalize Pattern)

def repeatedFrame403 {s q d} {picked : RepeatedElection403 s q d}
    {retained : RetainedCenterRows403 picked}
    (origin : SelectedHeadOrigin395 (row := d) (selectedRepeatedTape403 picked retained)) :
    AuthoredBodyFrame393 s.core q :=
  preoutputFrameOfOrigin399 origin unusedPlacement403 (fun _ => emptyCapture403)

theorem repeated_origin_keeps_exact_candidate403 {s q d}
    (picked : RepeatedElection403 s q d) (retained : RetainedCenterRows403 picked)
    (origin : SelectedHeadOrigin395 (row := d) (selectedRepeatedTape403 picked retained)) :
    origin.pick = selectedRepeatedCandidate403 picked retained ∧ origin.visibleOrdinal = 0 := by
  have one : ∀ rows (eq : rows = [d]),
      let t : CandidateTape s.core q rows := eq.symm ▸ .next
        (.matched (selectedRepeatedCandidate403 picked retained)) .nil
      storedCandidateEntries401 t = [(0,⟨d,selectedRepeatedCandidate403 picked retained⟩)] := by
    intro rows eq
    subst rows
    rfl
  have h := original_stored_entry_is_listed401 origin.stored
  change (origin.visibleOrdinal,⟨d,origin.pick⟩) ∈
    storedCandidateEntries401 (selectedRepeatedTape403 picked retained) at h
  unfold selectedRepeatedTape403 at h
  rw [one _ picked.sole] at h
  have atSame := List.mem_singleton.mp h
  exact ⟨eq_of_heq (Sigma.mk.inj (congrArg Prod.snd atSame)).2,congrArg Prod.fst atSame⟩

structure RepeatedReadback403 {s q} (e : Event s q) where
  elected : RepeatedElection403 s q e.frame.decl
  retained : RetainedCenterRows403 elected
  origin : SelectedHeadOrigin395 (row := e.frame.decl) (selectedRepeatedTape403 elected retained)
  sameFrame : e.frame = repeatedFrame403 origin
  sameHead : e.head = origin.pick.head
  noWhere : e.frame.decl.requirements = []

theorem repeated_readback_no_where403 {s q e}
    (read : RepeatedReadback403 (s := s) (q := q) e) : e.kids = [] := by
  simp [Event.kids,frameWhereKids400,AuthoredBodyFrame393.clauses,read.noWhere,children]

/-- A literal variable fixed target is determined by the original
supplier and post-selection lexical capture, independently of the
B6 event. The equations/bounds must be present in the same State. -/
def RetainedOutputSources403 {s : State} {q : Request} (frame : AuthoredBodyFrame393 s.core q) : Prop :=
  ∀ (i : Fin q.demand.outputs.length) (body : Body),
    Supplies (authoredRegistry s.core.current).roles frame.decl q.demand.outputs[i].name body →
    ∃ n : Nat, ∃ cap : Capture,
      normalize (bodyPattern body) = .var n ∧ frame.slots body n = some cap ∧
      Bound s.core.current.ordinary.normal q.demand.outputs[i].target cap.center ∧
      Bound s.core.current.ordinary.normal cap.center q.demand.outputs[i].target

theorem addressed_sources_give_real_output_rows403 {s q} (e : Event s q)
    (found : RetainedOutputSources403 (s := s) e.frame) :
    RetainedVariableOutputs403 e := fun i => found i (e.outputs i).body (e.outputs i).supplied

inductive RepeatedOther403 (s : State) (q : Request) : OtherVerdict → Prop where
  | ambiguous : Nonempty (RepeatedScope403 s q) → 2 ≤ (visible s.core q).length →
      RepeatedOther403 s q .ambiguous

/-- The concrete same-state source rule, now including arbitrary
patterns of repeated variable binders *inside this exact fragment*.
A chosen event has actual preselected occurrence, post-selection
literal tie rows, and the original B6 input reflected into its receipt.
An unresolved case is not silently turned into a negative rule. -/
def repeatedSource403 : SourcePrimitives where
  elected := fun _ _ e needs =>
    needs = [] ∧ Nonempty (RepeatedReadback403 e) ∧ RetainedVariableOutputs403 e
  other := fun s q verdict needs => needs = [] ∧ RepeatedOther403 s q verdict

theorem repeated_ambiguity_needs_no_center_ties403 {s q} (scope : RepeatedScope403 s q)
    (rawSafe : ¬ RootCycle s q) (multiple : 2 ≤ (visible s.core q).length) :
    Classifies repeatedSource403 s q .ambiguous :=
  ⟨.ambiguous,none,⟨.other .ambiguous rawSafe (needs := []) ⟨rfl,.ambiguous ⟨scope⟩ multiple⟩ .nil⟩,
    .ambiguous⟩

theorem repeated_scope_elects_then_reads_B6403 {s q d}
    (picked : RepeatedElection403 s q d) (retained : RetainedCenterRows403 picked)
    (noWhere : d.requirements = [])
    (declared : DeclaredOriginalOutputs400 s.core q)
    (typed : ∀ origin : SelectedHeadOrigin395 (row := d) (selectedRepeatedTape403 picked retained),
      NamedInputAtStoredHead401 s.b6 (repeatedFrame403 origin)) :
    ∃ e : Event s q, Nonempty (RepeatedReadback403 e) ∧ e.frame.decl = d ∧
      e.kids = [] ∧ ∀ i : Fin q.demand.outputs.length,
        (e.outputs i).receipt.occurrence = q.occurrence ∧
        (e.outputs i).receipt.outputOrdinal = i.val ∧
        (e.outputs i).receipt.original = q.demand.outputs[i] ∧
        ∀ m : Model, ∃ ty,
          (e.outputs i).receipt.actualEquation m = some (q.demand.outputs[i].target,ty) ∧
          evaluateMixedRhs401 (sourceRead401 m (e.frame.slots (e.outputs i).body))
            (e.outputs i).plan = some ty := by
  obtain ⟨origin⟩ := selected_head_original_origin395 (selected_repeated_tape_exact403 picked retained)
  obtain ⟨out,_,_,checks⟩ := stored_head_emits_exact_ordered_mixed_values401
    origin unusedPlacement403 (fun _ => emptyCapture403) picked.scope.checked declared s.b6 (typed origin)
  let event : Event s q := ⟨repeatedFrame403 origin,origin.pick.head,out⟩
  have read : RepeatedReadback403 event := ⟨picked,retained,origin,rfl,rfl,noWhere⟩
  refine ⟨event,⟨read⟩,rfl,repeated_readback_no_where403 read,?_⟩
  intro i
  exact ⟨(checks i).2.2.1,(checks i).2.2.2.1,(checks i).2.2.2.2.1,(checks i).2.2.2.2.2⟩

theorem repeated_selection_mints_same_event_trace403 {s q d}
    (picked : RepeatedElection403 s q d) (retained : RetainedCenterRows403 picked)
    (noWhere : d.requirements = [])
    (declared : DeclaredOriginalOutputs400 s.core q)
    (typed : ∀ origin : SelectedHeadOrigin395 (row := d) (selectedRepeatedTape403 picked retained),
      NamedInputAtStoredHead401 s.b6 (repeatedFrame403 origin))
    (fixed : ∀ origin : SelectedHeadOrigin395 (row := d) (selectedRepeatedTape403 picked retained),
      RetainedOutputSources403 (s := s) (repeatedFrame403 origin)) :
    Classifies repeatedSource403 s q (.selected (.node d.id [])) := by
  obtain ⟨origin⟩ := selected_head_original_origin395 (selected_repeated_tape_exact403 picked retained)
  obtain ⟨out,_,_,_⟩ := stored_head_emits_exact_ordered_mixed_values401
    origin unusedPlacement403 (fun _ => emptyCapture403) picked.scope.checked declared s.b6 (typed origin)
  let event : Event s q := ⟨repeatedFrame403 origin,origin.pick.head,out⟩
  have read : RepeatedReadback403 event := ⟨picked,retained,origin,rfl,rfl,noWhere⟩
  have empty : WhereForest repeatedSource403 s event.kids [] :=
    repeated_readback_no_where403 read ▸ .nil
  have fixed' := addressed_sources_give_real_output_rows403 event (fixed origin)
  exact ⟨.selected d.id [],some event,
    ⟨.selected event picked.rawSafe (needs := []) ⟨rfl,⟨read⟩,fixed'⟩ .nil empty⟩,
    .selected .nil (.selected rfl)⟩

theorem repeated_variable_dictionary_sound403 : DictionarySound repeatedSource403 := by
  intro s q d selected m fit
  obtain ⟨t,event,⟨trace⟩,summary⟩ := selected
  cases trace with
  | rootK2 => cases summary
  | other _ _ localProof _ =>
    rcases localProof with ⟨_,reason⟩
    cases reason
    cases summary
  | selected event safe localProof support kids =>
    rename_i needs trees
    rcases localProof with ⟨_,⟨read⟩,fixed⟩
    have empty := repeated_readback_no_where403 read
    have noTrees : trees = [] := by
      have child : WhereForest repeatedSource403 s [] trees := empty ▸ kids
      cases child
      rfl
    subst trees
    cases summary with
    | selected summaries combined =>
      cases summaries
      cases combined with
      | selected allEmpty =>
        rename_i dicts
        have noDicts : dicts = [] := List.map_eq_nil_iff.mp allEmpty.symm
        subst dicts
        refine .node event ⟨source_head_sound event.head m fit,?_⟩
          (retained_variable_targets_sound403 fixed m fit) (empty ▸ .nil)
        intro i
        let out := event.outputs i
        have checked := read.elected.scope.checked.2 event.frame.decl
          (List.mem_of_getElem? event.frame.authored)
        have supplied := (GeneralDictionaryAssociatedProvenance.lookup_exact _ _
          checked.identified.2.2.1 _ _).mpr out.supplied
        exact ⟨rfl,rfl,rfl,supplied,out.originalTyped,named_mixed_output_is_fixed_equation401 out m⟩

end Yulang.GeneralDeclarativeI65.I72
