import Yulang.GeneralDeclarativeI65I72TypedTargetRows403
import Yulang.GeneralDeclarativeI65NativePrefixCore377

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (All₂ Dictionary Result Summarizes Tree)
open CommonRecursiveNominalIntervals (Endpoint Argument Obligation)
open CommonDeclaredNominalInspection (Parameter)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessConstructorModes357 (Use)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeInspect321 (Inspects Visit PatternK2)

/-- Literal source frontier of one structurally inspecting unary
candidate. The outer shape is known at both exact authored endpoints,
its one declared value parameter is covariant, and its one written
child has a rigid ordinary query. There is no previous child or
argument to skip, no solver route/release, and no fitted model. -/
structure AuthoredUnaryEntry403 (s : State) (q : Request) (d : Declaration) where
  visibleRow : d ∈ visible s.core q
  input : Capture
  exactInput : q.demand.arguments = [input]
  written : Pattern
  exactHead : d.head = [written]
  key : Nat
  inner : Pattern
  dispatch : normalize written = .app key [inner]
  declared : Use s.core.current.environment key 1
  mode : declared.mode = .declared [⟨.value,.covariant⟩]
  table : s.core.modes[key]? = some [⟨.value,.covariant⟩]
  lower : Origin
  upper : Origin
  lowerAuthored : lower ∈ s.core.origins
  upperAuthored : upper ∈ s.core.origins
  lowerRoute : OriginRoute s.core lower input.lower
  upperRoute : OriginRoute s.core upper input.upper
  lowerSite : Nat
  upperSite : Nat
  lowerSyntax : lower.endpoint = .nominal key [.inl (.point (.ordinary (.var lowerSite)))]
  upperSyntax : upper.endpoint = .nominal key [.inl (.point (.ordinary (.var upperSite)))]
  query : Expr
  literalQuery : translate (authoredRegistry s.core.current).constructors
    (interpretation s.core.current.environment.source.snapshot) inner = some query
  enters : Inspects query

def AuthoredUnaryEntry403.lowerPrefix {s q d} (p : AuthoredUnaryEntry403 s q d) :
    NativeHeadPrefix s.core q d (fun _ => True) .lower :=
  ⟨p.visibleRow,0,p.input,by simp [p.exactInput],
    ⟨p.lower,p.lowerAuthored,p.lowerRoute,True.intro⟩,
    p.written,by simp [p.exactHead],
    p.key,[p.inner],p.dispatch,[.inl (.point (.ordinary (.var p.lowerSite)))],
    p.lowerSyntax,p.declared,[_],p.mode,p.table⟩

def AuthoredUnaryEntry403.lowerPort {s q d} (p : AuthoredUnaryEntry403 s q d) :
    NativeValuePort p.lowerPrefix false :=
  ⟨0,p.inner,rfl,⟨.value,.covariant⟩,rfl,rfl,
    .point (.ordinary (.var p.lowerSite)),rfl,[_],rfl,
    ⟨0,.left,.lower,.ordinary (.var p.lowerSite)⟩,List.mem_cons_self⟩

/-- Recover the *first actual written subpattern* and its exact
ordinary site from the original lower authored operand. The matching
upper operand resolves the paired job, not the choice of a site.
There is no success premise for the comparison or for the child. -/
theorem unary_source_enters_exact_current_site403 {s q d}
    (p : AuthoredUnaryEntry403 s q d) :
    p.lowerPrefix.written[0]? = some p.inner ∧
    p.lowerPort.which.payload = .ordinary (.var p.lowerSite) ∧
    (CommonRecursiveNominalIntervals.decomposeContextArgument
      (α := Nat) false ⟨.value,.covariant⟩
      (.inl (.point (.ordinary (.var p.lowerSite))))
      (.inl (.point (.ordinary (.var p.upperSite))))) =
      some [(false,Obligation.value (.ordinary (.var p.lowerSite)) (.ordinary (.var p.upperSite)))] ∧
    Visit (GeneralDeclarativeGraphRows321.structural s.core.current.ordinary)
      p.lowerSite p.query p.lowerSite :=
  ⟨rfl,rfl,rfl,.here p.enters⟩

def AuthoredCandidateK2403 (s : State) (q : Request) : Prop :=
  ∃ d, ∃ visit : AuthoredUnaryEntry403 s q d, CurrentCycleAt s visit.lowerSite

theorem authored_candidate_k2_uses_unfiltered_graph403 {s q d}
    (entry : AuthoredUnaryEntry403 s q d) (cycle : CurrentCycleAt s entry.lowerSite) :
    PatternK2 s.core.current.ordinary entry.lowerSite entry.query :=
  ⟨entry.lowerSite,(unary_source_enters_exact_current_site403 entry).2.2.2,cycle⟩

/-- A known opened structural row cannot also appear in the
all-variable successful/ambiguous scope. No candidate ignored before
that exclusive rule, and no unobserved child vetoes it. -/
theorem entered_structural_excludes_only_variable403 {s q d}
    (entry : AuthoredUnaryEntry403 s q d) (scope : RepeatedScope403 s q) : False := by
  have listed : entry.written ∈ d.head := by rw [entry.exactHead]; exact List.mem_cons_self
  rw [(scope.allVisible d entry.visibleRow).literal] at listed
  obtain ⟨binder,_,shape⟩ := List.mem_map.mp listed
  have mismatch := entry.dispatch
  rw [← shape] at mismatch
  cases mismatch

/-- A concrete classifier with the safe variable fragment and the
separately represented native opening. Outside both sources there
is no manufactured negative/default branch. -/
def variableWithNativeK2403 : SourcePrimitives where
  elected := fun _ _ e needs =>
    needs = [] ∧ Nonempty (VariableWhereReadback403 e) ∧
      (RetainedVariableOutputs403 e ∨ RetainedTypedValueRows403 e)
  other := fun s q verdict needs => needs = [] ∧
    (RepeatedOther403 s q verdict ∨ verdict = .rejected ∧ AuthoredCandidateK2403 s q)

theorem authored_native_k2_is_rejected403 {s q}
    (opened : AuthoredCandidateK2403 s q) :
    Classifies variableWithNativeK2403 s q .rejected := by
  classical
  by_cases raw : RootCycle s q
  · exact root_k2_is_rejected_for_every_primitive_system raw
  · exact ⟨.rejected,none,
      ⟨.other .rejected raw (needs := []) ⟨rfl,.inr ⟨rfl,opened⟩⟩ .nil⟩,.rejected⟩

theorem authored_native_k2_cannot_be_variable_selection403 {s q}
    (opened : AuthoredCandidateK2403 s q) {d} :
    ¬ Classifies variableWithNativeK2403 s q (.selected d) := by
  rintro ⟨t,_,⟨trace⟩,summary⟩
  obtain ⟨impl,entry,_⟩ := opened
  cases trace with
  | rootK2 => cases summary
  | other v _ reason _ => cases v <;> cases summary
  | selected event _ primitive _ _ =>
    obtain ⟨_,⟨read⟩,_⟩ := primitive
    exact entered_structural_excludes_only_variable403 entry read.elected.scope


/-- A known candidate-local K2 site cannot become a pre-selection
ambiguity or a where-child ambiguity in this concrete represented rule. -/
theorem authored_native_k2_cannot_be_variable_ambiguity403 {s q}
    (opened : AuthoredCandidateK2403 s q) :
    ¬ Classifies variableWithNativeK2403 s q .ambiguous := by
  rintro ⟨t,_,⟨trace⟩,summary⟩
  obtain ⟨impl,entry,_⟩ := opened
  cases trace with
  | rootK2 => cases summary
  | other v safe reason support =>
    cases v with
    | pending => cases summary
    | rejected => cases summary
    | ambiguous =>
      rcases reason.2 with either|⟨opposite,_⟩
      · cases either with
        | ambiguous known _ =>
          obtain ⟨scope⟩ := known
          exact entered_structural_excludes_only_variable403 entry scope
      · cases opposite
  | selected event safe primitive support kids =>
    obtain ⟨_,⟨read⟩,_⟩ := primitive
    exact entered_structural_excludes_only_variable403 entry read.elected.scope

/-- Ordered children for the same concrete source rules, not an
external solver result or alias of a different rule system. -/
private theorem collectNativeScopedChildren403 {s qs ds}
    (proof : All₂ (fun q d => Classifies variableWithNativeK2403 s q (.selected d)) qs ds) :
    ∃ ts, Nonempty (WhereForest variableWithNativeK2403 s qs ts) ∧
      All₂ Summarizes ts (ds.map Result.selected) := by
  induction proof with
  | nil => exact ⟨[],⟨.nil⟩,.nil⟩
  | cons now rest ih =>
    obtain ⟨t,_,⟨one⟩,a⟩ := now
    obtain ⟨ts,⟨later⟩,b⟩ := ih
    exact ⟨t::ts,⟨.cons one later⟩,.cons a b⟩

/-- At each original B6 body/ordinal, evaluate neither a model nor
the compiler to decide the existence of its retained row. The RHS
tree is the literal lexical instantiation of the read input. -/
def TypedRowsAtOriginalInput403 {s : State} {q : Request}
    (frame : AuthoredBodyFrame393 s.core q) : Prop :=
  ∀ (i : Fin q.demand.outputs.length) (out : NamedMixedOutput401 s.b6 frame i),
    ∃ rhs, fixedValueCode403 out.rhs = some rhs ∧
      ⟨q.demand.outputs[i].target,rhs⟩ ∈ s.core.current.ordinary.equations

theorem authored_typed_rows_select_where403 {s q d ds}
    (picked : RepeatedElection403 s q d) (retained : RetainedCenterRows403 picked)
    (clauses : LiteralVariableWhere403 d)
    (declared : DeclaredOriginalOutputs400 s.core q)
    (typed : ∀ origin : SelectedHeadOrigin395 (row := d) (selectedRepeatedTape403 picked retained),
      NamedInputAtStoredHead401 s.b6 (repeatedFrame403 origin))
    (fixed : ∀ origin : SelectedHeadOrigin395 (row := d) (selectedRepeatedTape403 picked retained),
      TypedRowsAtOriginalInput403 (s := s) (repeatedFrame403 origin))
    (childrenSelected : ∀ origin : SelectedHeadOrigin395 (row := d) (selectedRepeatedTape403 picked retained),
      All₂ (fun child dict => Classifies variableWithNativeK2403 s child (.selected dict))
        (frameWhereKids400 (repeatedFrame403 origin)) ds) :
    Classifies variableWithNativeK2403 s q (.selected (.node d.id ds)) := by
  obtain ⟨origin⟩ := selected_head_original_origin395 (selected_repeated_tape_exact403 picked retained)
  obtain ⟨out,_,_,_⟩ := stored_head_emits_exact_ordered_mixed_values401
    origin unusedPlacement403 (fun _ => emptyCapture403) picked.scope.checked declared s.b6 (typed origin)
  let event : Event s q := ⟨repeatedFrame403 origin,origin.pick.head,out⟩
  have read : VariableWhereReadback403 event := ⟨picked,retained,origin,rfl,rfl,clauses⟩
  have actual : RetainedTypedValueRows403 event := fun i => fixed origin i (out i)
  obtain ⟨ts,⟨forest⟩,summaries⟩ := collectNativeScopedChildren403 (childrenSelected origin)
  exact ⟨.selected d.id ts,some event,⟨.selected event picked.rawSafe (needs := [])
    ⟨rfl,⟨read⟩,.inr actual⟩ .nil forest⟩,.selected summaries (.selected rfl)⟩

/-- Same fixed quantifiers and recursive dictionary meaning for the
concrete positive rules plus their independent unary native K2 case. -/
theorem variable_native_priority_dictionary_sound403 : DictionarySound variableWithNativeK2403 := by
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
      obtain ⟨_,⟨read⟩,retained⟩ := recognized
      have fixed : FixedTargets m e := retained.elim
        (fun alias => retained_variable_targets_sound403 alias m fit)
        (fun typed => retained_typed_rows_satisfy_fixed_targets403 typed m fit)
      cases combined with
      | selected localKids merge =>
        cases merge with
        | selected exacts =>
          rw [exacts] at localKids
          refine .node e ⟨source_head_sound e.head m fit,?_⟩ fixed (child _ localKids)
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


/-- Literal pending-output self-ring is excluded as head support but
not from this already-entered raw-cycle test. It does not open a
different candidate and is not promoted to input provenance. -/
theorem pending_equation_still_vetoes_entered_unary403 {s q d}
    (entry : AuthoredUnaryEntry403 s q d) {done : Nat → Prop}
    (support : GeneralDeclarativeOrigins321.Supported s.core.current.ordinary done)
    (tag owner : Nat)
    (derived : support.derivesFrom
      (⟨entry.lowerSite,.nominal tag [.variable entry.lowerSite]⟩ : GeneralDeclarativeHead320.Equation)
      (.output owner))
    (onlyPending : ∀ o, support.derivesFrom
      (⟨entry.lowerSite,.nominal tag [.variable entry.lowerSite]⟩ : GeneralDeclarativeHead320.Equation) o →
        ∃ i, o = .output i ∧ ¬ done i) :
    (⟨entry.lowerSite,.nominal tag [.variable entry.lowerSite]⟩ : GeneralDeclarativeHead320.Equation)
      ∉ (GeneralDeclarativeOrigins321.restriction support).equations ∧
      Classifies variableWithNativeK2403 s q .rejected := by
  refine ⟨GeneralDeclarativeOrigins321.pending_only support _ onlyPending,?_⟩
  exact authored_native_k2_is_rejected403 ⟨d,entry,
    GeneralDeclarativeK2Alias321.cycle_in_alias_graph
      (GeneralDeclarativeGraphRows321.pending_nominal_self_cycle support owner derived)⟩

end Yulang.GeneralDeclarativeI65.I72
