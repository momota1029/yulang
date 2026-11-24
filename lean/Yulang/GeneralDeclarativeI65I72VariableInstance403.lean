import Yulang.GeneralDeclarativeI65I72VariableChoice403

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open CommonRoleOutermostResolver (Dictionary Result Tree Summarizes All₂)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEmissionForest322 (Placement)
open GeneralDeclarativeBounds319 (Bound bound_sound)
open GeneralDictionaryAssociatedProvenance (Body Supplies)
open GeneralDeclarativeOutputs320 (bodyPattern)
open CommonNominalFullCarrier (Ty Equivalent)

/-- Padding is unreachable: every declaration in the represented
scope has no where clauses. Defaults still use the original request. -/
def unusedPlacement403 : Placement := ⟨fun _ _ => emptyCapture403,fun _ _ => 0⟩

def sourceFrame403 {s q d} {scope : VariableScope403 s q}
    (origin : SelectedHeadOrigin395 (row := d) (variableTape403 scope)) :
    AuthoredBodyFrame393 s.core q :=
  preoutputFrameOfOrigin399 origin unusedPlacement403 (fun _ => emptyCapture403)

structure VariableReadback403 {s q} (e : Event s q) where
  scope : VariableScope403 s q
  one : visible s.core q = [e.frame.decl]
  origin : SelectedHeadOrigin395 (row := e.frame.decl) (variableTape403 scope)
  sameFrame : e.frame = sourceFrame403 origin
  sameHead : e.head = origin.pick.head

theorem variable_readback_no_where403 {s q e} (read : VariableReadback403 (s := s) (q := q) e) :
    e.kids = [] := by
  have none := (read.scope.allVisible e.frame.decl e.frame.inScope).noWhere
  simp [Event.kids,frameWhereKids400,AuthoredBodyFrame393.clauses,none,children]

/-- A currently present two-way binding of the literal requested target
to the authored variable read at the exact output's lexical occurrence.
This implies the target equality; no model, expected answer, or RHS
solver check appears in this rule. Mixed RHS trees can be generated
below, but their target derivation is not handled by this constructor. -/
def RetainedVariableOutputs403 {s q} (e : Event s q) : Prop :=
  ∀ i : Fin q.demand.outputs.length,
    ∃ n : Nat, ∃ cap : Capture,
      normalize (bodyPattern (e.outputs i).body) = .var n ∧
      e.frame.slots (e.outputs i).body n = some cap ∧
      Bound s.core.current.ordinary.normal q.demand.outputs[i].target cap.center ∧
      Bound s.core.current.ordinary.normal cap.center q.demand.outputs[i].target

private theorem named_variable_eval403 {s slots} (m : Model) {c p}
    (tree : NamedMixedTree401 s slots c p) {n cap} (written : p = .var n)
    (named : slots n = some cap) :
    evaluateMixedRhs401 (actualNamedMixedRead401 m) tree = some (m.assignment cap.center).1 := by
  subst p
  cases tree with
  | binder _ slot =>
    have same := Option.some.inj (slot.property.symm.trans named)
    simp only [evaluateMixedRhs401,actualNamedMixedRead401,Option.map_some,same]

theorem retained_variable_targets_sound403 {s q} {e : Event s q}
    (reads : RetainedVariableOutputs403 e) (m : Model) (fit : Fits s m) : FixedTargets m e := by
  intro i
  obtain ⟨n,cap,literal,present,there,back⟩ := reads i
  refine ⟨(m.assignment cap.center).1,?_,bound_sound m.assignment fit.1.1.1 there,bound_sound m.assignment fit.1.1.1 back⟩
  have eval := named_variable_eval403 (s := s.core) m (e.outputs i).rhs literal present
  simp only [NamedMixedReceipt401.actualEquation,NamedMixedOutput401.receipt,eval,Option.map_some]

inductive VariableOther403 (s : State) (q : Request) : OtherVerdict → Prop where
  | ambiguous : Nonempty (VariableScope403 s q) → (visible s.core q).length ≥ 2 →
      VariableOther403 s q .ambiguous

/-- Concrete source rule for this represented fragment. Its selection
part contains actual all-visible election and exact post-selection
addresses and retained rows. No model-valued positive evidence occurs
in its premises. Other patterns are not classified by this module. -/
def variableSource403 : SourcePrimitives where
  elected := fun _ _ e needs =>
    needs = [] ∧ Nonempty (VariableReadback403 e) ∧ RetainedVariableOutputs403 e
  other := fun s q v needs => needs = [] ∧ VariableOther403 s q v

abbrev VariableClassifies403 := Classifies variableSource403

theorem source_variable_ambiguous403 {s q} (scope : VariableScope403 s q)
    (safe : ¬ RootCycle s q) (multiple : 2 ≤ (visible s.core q).length) :
    VariableClassifies403 s q .ambiguous :=
  ⟨.ambiguous,none,⟨.other .ambiguous safe (needs := []) ⟨rfl,.ambiguous ⟨scope⟩ multiple⟩ .nil⟩,
    .ambiguous⟩

theorem variable_root_k2_precedes_ambiguity403 {s q} (cycle : RootCycle s q) :
    VariableClassifies403 s q .rejected ∧ ¬ VariableClassifies403 s q .ambiguous := by
  refine ⟨root_k2_is_rejected_for_every_primitive_system cycle,?_⟩
  rintro ⟨t,event,⟨trace⟩,summary⟩
  rw [root_k2_forces_original_trace_verdict cycle trace] at summary
  cases summary

theorem variable_selected_from_actual_readback403 {s q} {e : Event s q}
    (safe : ¬ RootCycle s q) (read : VariableReadback403 e)
    (fixed : RetainedVariableOutputs403 e) :
    VariableClassifies403 s q (.selected (.node e.frame.decl.id [])) := by
  have noKids := variable_readback_no_where403 read
  have empty : WhereForest variableSource403 s e.kids [] := noKids ▸ .nil
  exact ⟨.selected e.frame.decl.id [],some e,
    ⟨.selected e safe (needs := []) ⟨rfl,⟨read⟩,fixed⟩ .nil empty⟩,
    .selected .nil (.selected rfl)⟩

/-- Actual B6 inputs are read only after election. This construction
takes no candidate tape, winning source event, prepared receipt or
model as an input and supports arbitrary mixed RHS syntax as data. -/
theorem elected_source_reads_original_B6403 {s q d} (scope : VariableScope403 s q)
    (safe : ¬ RootCycle s q) (one : visible s.core q = [d])
    (declared : DeclaredOriginalOutputs400 s.core q)
    (typed : ∀ origin : SelectedHeadOrigin395 (row := d) (variableTape403 scope),
      NamedInputAtStoredHead401 s.b6 (sourceFrame403 origin)) :
    ∃ e : Event s q, Nonempty (VariableReadback403 e) ∧ e.frame.decl = d ∧ e.kids = [] ∧
      ∀ i : Fin q.demand.outputs.length,
        (e.outputs i).receipt.occurrence = q.occurrence ∧
        (e.outputs i).receipt.outputOrdinal = i.val ∧
        (e.outputs i).receipt.original = q.demand.outputs[i] ∧
        ∀ m : Model, ∃ ty,
          (e.outputs i).receipt.actualEquation m = some (q.demand.outputs[i].target,ty) ∧
          evaluateMixedRhs401 (sourceRead401 m (e.frame.slots (e.outputs i).body))
            (e.outputs i).plan = some ty := by
  obtain ⟨origin⟩ := selected_head_original_origin395 (variable_single_selection403 scope safe one)
  obtain ⟨out,_,_,checks⟩ := stored_head_emits_exact_ordered_mixed_values401
    origin unusedPlacement403 (fun _ => emptyCapture403) scope.checked declared s.b6 (typed origin)
  let e : Event s q := ⟨sourceFrame403 origin,origin.pick.head,out⟩
  have read : VariableReadback403 e := ⟨scope,one,origin,rfl,rfl⟩
  refine ⟨e,⟨read⟩,rfl,variable_readback_no_where403 read,?_⟩
  intro i
  exact ⟨(checks i).2.2.1,(checks i).2.2.2.1,(checks i).2.2.2.2.1,(checks i).2.2.2.2.2⟩

theorem selected_without_requested_outputs403 {s q d}
    (scope : VariableScope403 s q) (safe : ¬ RootCycle s q)
    (one : visible s.core q = [d]) (absent : q.demand.outputs = []) :
    VariableClassifies403 s q (.selected (.node d.id [])) := by
  have noIndex : ∀ i : Fin q.demand.outputs.length, False := by
    intro i
    obtain ⟨v,h⟩ := i
    simp [absent] at h
  obtain ⟨event,⟨read⟩,row,_,_⟩ := elected_source_reads_original_B6403 scope safe one
    (fun i => (noIndex i).elim) (fun _ i => (noIndex i).elim)
  rw [← row]
  exact variable_selected_from_actual_readback403 safe read (fun i => (noIndex i).elim)

/-- Exact C402 top-level soundness quantified over all states, models,
and outputs of this concrete instance. It is not soundness of an
as-yet undefined general source classifier. -/
theorem variable_dictionary_sound403 : DictionarySound variableSource403 := by
  intro s q d selected m fit
  obtain ⟨t,event,⟨trace⟩,summary⟩ := selected
  cases trace with
  | rootK2 => cases summary
  | other verdict safe localProof supported =>
    rcases localProof with ⟨_,reason⟩
    cases reason
    cases summary
  | selected event safe localProof support kids =>
    rename_i needs trees
    rcases localProof with ⟨_,⟨read⟩,fixed⟩
    have empty := variable_readback_no_where403 read
    have noTrees : trees = [] := by
      have child : WhereForest variableSource403 s [] trees := empty ▸ kids
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
        have checked := read.scope.checked.2 event.frame.decl (List.mem_of_getElem? event.frame.authored)
        have supplied := (GeneralDictionaryAssociatedProvenance.lookup_exact _ _
          checked.identified.2.2.1 _ _).mpr out.supplied
        exact ⟨rfl,rfl,rfl,supplied,out.originalTyped,named_mixed_output_is_fixed_equation401 out m⟩

end Yulang.GeneralDeclarativeI65.I72
