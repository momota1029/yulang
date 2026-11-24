import Yulang.GeneralDeclarativeI65I72RepeatedInstance403

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (All₂ Combine Dictionary Result Summarizes Tree)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarations (Clause Declaration)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeEmissionForest322 (Placement)
open GeneralDeclarativeSourceEmission322 (Names inputs useArg demand)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)

/-- Each actual written clause has only direct same-name inputs and
no requested child outputs. This leaves arbitrary finite ordered
children, but does not invent a placement for a compound or a target. -/
def LiteralVariableWhere403 (d : Declaration) : Prop :=
  ∀ c ∈ d.requirements,
    (∃ binders : List Nat, c.arguments = binders.map Pattern.var) ∧ c.outputs = []

private theorem uses_exact_original_variable403 (names : Names) (other : Nat → Capture)
    (position : Nat) (binders : List Nat) :
    inputs names other position (binders.map Pattern.var) = binders.map names.input := by
  induction binders generalizing position with
  | nil => rfl
  | cons n rest ih =>
    simp only [List.map_cons,inputs,useArg,normalize,ih]

theorem literal_variable_where_uses_actual_names403 {s q} (f : AuthoredBodyFrame393 s q)
    {c : Clause} {binders : List Nat} (written : c.arguments = binders.map Pattern.var)
    (noOutputs : c.outputs = []) :
    (f.whereFor c).demand = ⟨c.role,binders.map f.names.input,[]⟩ := by
  unfold AuthoredBodyFrame393.whereFor demand
  rw [written,noOutputs,uses_exact_original_variable403]
  rfl

private theorem sourceInputs_no_output_shadow403 {s q} (f : AuthoredBodyFrame393 s q)
    (checked : GeneralDeclarations.Checked (authoredRegistry s.current)) {x : Nat}
    (literal : x ∈ f.decl.inputNames) : f.names.input x = f.input x := by
  exact GeneralDeclarativeProducedNames325.exact_input
    (checked.2 f.decl (List.mem_of_getElem? f.authored)) literal

/-- The genuine authored where request at original ordinal keeps its
exact source names, occurrence path, and positional order. All captures
are already from the selected original input; no synthesized child. -/
theorem literal_where_child_at403 {s q}
    (f : AuthoredBodyFrame393 s q) (scope : LiteralVariableWhere403 f.decl)
    (checked : GeneralDeclarations.Checked (authoredRegistry s.current))
    {i : Nat} {c : Clause} (seen : f.decl.requirements[i]? = some c) :
    ∃ binders : List Nat, c.arguments = binders.map Pattern.var ∧
      (frameWhereKids400 f)[i]? = some ⟨q.occurrence ++ [i],
        ⟨c.role,binders.map f.input,[]⟩⟩ := by
  have mem := List.mem_of_getElem? seen
  obtain ⟨⟨ns,written⟩,noOutputs⟩ := scope c mem
  refine ⟨ns,written,?_⟩
  have all := (checked.2 f.decl (List.mem_of_getElem? f.authored)).scope.1 c mem
  have atNames : ns.map f.names.input = ns.map f.input := by
    apply List.map_congr_left
    intro n used
    apply sourceInputs_no_output_shadow403 f checked
    apply all n
    have inArgs : Pattern.var n ∈ c.arguments := by rw [written]; exact List.mem_map_of_mem used
    exact GeneralDeclarativeProducedNames325.enters_normal inArgs rfl
  have exactDemand := literal_variable_where_uses_actual_names403 f written noOutputs
  rw [atNames] at exactDemand
  simp only [frameWhereKids400,children,AuthoredBodyFrame393.clauses,List.getElem?_map]
  rw [List.getElem?_zipIdx]
  simp [List.getElem?_map,seen,exactDemand]

/-- Entire original pre-output event, but from the represented
source readback; its ordered where list is genuine syntax. -/
structure VariableWhereReadback403 {s q} (e : Event s q) where
  elected : RepeatedElection403 s q e.frame.decl
  retained : RetainedCenterRows403 elected
  origin : SelectedHeadOrigin395 (row := e.frame.decl) (selectedRepeatedTape403 elected retained)
  sameFrame : e.frame = repeatedFrame403 origin
  sameHead : e.head = origin.pick.head
  sourceClauses : LiteralVariableWhere403 e.frame.decl

def variableWhereSource403 : SourcePrimitives where
  elected := fun _ _ e needs =>
    needs = [] ∧ Nonempty (VariableWhereReadback403 e) ∧ RetainedVariableOutputs403 e
  other := fun s q verdict needs => needs = [] ∧ RepeatedOther403 s q verdict

private theorem collectActualChildren403 {s qs ds}
    (choice : All₂ (fun q d => Classifies variableWhereSource403 s q (.selected d)) qs ds) :
    ∃ ts, Nonempty (WhereForest variableWhereSource403 s qs ts) ∧
      All₂ Summarizes ts (ds.map Result.selected) := by
  induction choice with
  | nil => exact ⟨[],⟨.nil⟩,.nil⟩
  | cons a rest ih =>
    obtain ⟨t,_,⟨trace⟩,proof⟩ := a
    obtain ⟨ts,⟨traces⟩,proofs⟩ := ih
    exact ⟨t::ts,⟨.cons trace traces⟩,.cons proof proofs⟩

/-- Produce the genuinely selected node from its original candidate and
B6 occurrence, then compose independent same-state children in the
literal source order. A dictionary key or a passed-in Event cannot
select the row; the children are obtained from concrete Classifies. -/
theorem authored_variable_where_selects403 {s q d ds}
    (picked : RepeatedElection403 s q d) (retained : RetainedCenterRows403 picked)
    (clauses : LiteralVariableWhere403 d)
    (declared : DeclaredOriginalOutputs400 s.core q)
    (typed : ∀ origin : SelectedHeadOrigin395 (row := d) (selectedRepeatedTape403 picked retained),
      NamedInputAtStoredHead401 s.b6 (repeatedFrame403 origin))
    (fixed : ∀ origin : SelectedHeadOrigin395 (row := d) (selectedRepeatedTape403 picked retained),
      RetainedOutputSources403 (s := s) (repeatedFrame403 origin))
    (childrenSelected : ∀ origin : SelectedHeadOrigin395 (row := d) (selectedRepeatedTape403 picked retained),
      All₂ (fun child dict => Classifies variableWhereSource403 s child (.selected dict))
        (frameWhereKids400 (repeatedFrame403 origin)) ds) :
    Classifies variableWhereSource403 s q (.selected (.node d.id ds)) := by
  obtain ⟨origin⟩ := selected_head_original_origin395 (selected_repeated_tape_exact403 picked retained)
  obtain ⟨out,_,_,_⟩ := stored_head_emits_exact_ordered_mixed_values401
    origin unusedPlacement403 (fun _ => emptyCapture403) picked.scope.checked declared s.b6 (typed origin)
  let event : Event s q := ⟨repeatedFrame403 origin,origin.pick.head,out⟩
  have read : VariableWhereReadback403 event := ⟨picked,retained,origin,rfl,rfl,clauses⟩
  obtain ⟨ts,⟨forest⟩,sameKids⟩ := collectActualChildren403 (childrenSelected origin)
  exact ⟨.selected d.id ts,some event,
    ⟨.selected event picked.rawSafe (needs := [])
      ⟨rfl,⟨read⟩,addressed_sources_give_real_output_rows403 event (fixed origin)⟩ .nil forest⟩,
    .selected sameKids (.selected rfl)⟩

/-- Same-modeled recursive dictionary proof for the concrete source
rules. No solver execution, extra Fit hypothesis, unknown leaves, or
termination assumption is used. Every successful child is proved by
the same finite source rule in this State and Model. -/
theorem variable_where_dictionary_sound403 : DictionarySound variableWhereSource403 := by
  intro s q dict chosen m fit
  obtain ⟨t,_,⟨trace⟩,summary⟩ := chosen
  exact SourceTrace.rec
    (motive_1 := fun q t _ _ =>
      ∀ d, Summarizes t (.selected d) → DictionaryEvidence s m q d)
    (motive_2 := fun qs ts _ =>
      ∀ ds, All₂ Summarizes ts (ds.map Result.selected) → DictionaryEvidenceForest s m qs ds)
    (motive_3 := fun _ _ => True)
    (fun _ _ impossible => by cases impossible)
    (fun verdict _ proof _ _ _ impossible => by cases verdict <;> cases impossible)
    (fun e _ recognized _ _ _ child d combined => by
      obtain ⟨_,⟨read⟩,fixed⟩ := recognized
      cases combined with
      | selected localKids merge =>
        cases merge with
        | selected exacts =>
          rw [exacts] at localKids
          refine .node e ⟨source_head_sound e.head m fit,?_⟩
            (retained_variable_targets_sound403 fixed m fit) (child _ localKids)
          intro i
          let out := e.outputs i
          have checked := read.elected.scope.checked.2 e.frame.decl
            (List.mem_of_getElem? e.frame.authored)
          have supplied := (GeneralDictionaryAssociatedProvenance.lookup_exact _ _
            checked.identified.2.2.1 _ _).mpr out.supplied
          exact ⟨rfl,rfl,rfl,supplied,out.originalTyped,named_mixed_output_is_fixed_equation401 out m⟩)
    (fun ds both => by
      cases ds with
      | nil => exact .nil
      | cons => cases both)
    (fun _ _ one rest ds both => by
      cases ds with
      | nil => cases both
      | cons d ds =>
        cases both with
        | cons first later => exact .cons (one d first) (rest ds later))
    True.intro
    (fun _ _ _ _ _ _ => True.intro)
    trace dict summary

end Yulang.GeneralDeclarativeI65.I72
