import Yulang.GeneralDeclarativeI65I74ListReport410
import Yulang.GeneralDeclarativeI65I74ExactEscape410
import Yulang.GeneralDeclarativeWitnessModeDeclaration357

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.List410
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration DeclarationChecked)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessConstructorModes357 (readUse)
open GeneralDeclarativeWitnessSparseIntervals357 (names)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open CommonRoleOutermostResolver (Summarizes)
open Checker408 (Problem Result)

structure ListWire where
  original : Nat
  escape : ExactEscapeWire

structure VerifiedList (p : Problem) (d : Declaration) where
  known : InvariantListHead p.state p.root d
  rawSafe : ¬RootCycle p.state p.root


open PresenceNormalForm (Atom)

/-- The witness has only the origin-table index and raw escape colours.
Read the original binder and point endpoint in the same problem. The
raw proof visits the demanded root; a literal variable does not visit
its payload, even if that payload can itself exhibit a closed path. -/
def replayListHead (p : Problem) (d : Declaration)
    (whole : visible p.state.core p.root = [d]) (w : ListWire) :
    Option (VerifiedList p d) := do
  let core := p.state.core
  let env := core.current.environment
  let src := env.source
  if roleSeen : (Checker408.originalRole p).isSome = true then
    if header : (GeneralSourceMetadataRoles291.check src.roles &&
        GeneralDeclarativeWitnessModeCoverage357.checkDecl env d &&
        GeneralDeclarativeWitnessCovariantDescent353.legal src d) = true then
      if boundary : (d.requirements.isEmpty && p.root.demand.outputs.isEmpty) = true then
        match named : d.head, args : p.root.demand.arguments with
        | [.app key [.var binder]], [arg] =>
          if clear : checkExactEscape core.current.ordinary arg.lower w.escape = true then
            match atOrigin : core.origins[w.original]? with
            | none => none
            | some origin =>
              match endpoint : origin.endpoint with
              | .nominal originKey [.inl (.point (.ordinary (.var payload)))] =>
                if same : originKey = key ∧ origin.slot = arg.lower ∧
                    origin.slot = arg.center ∧ origin.slot = arg.upper then
                  let actual ← readUse env key 1
                  if mode : names actual.mode 1 = some [invariantValue410] then
                    if table : core.modes[key]? = some [invariantValue410] then
                      if atom : (Atom.tyLe (.var payload) (.var payload) : Atom Nat)
                          ∈ core.current.ordinary.normal.ordinary then
                        let knownRoles := (GeneralSourceMetadataRoles291.check_exact _).mp
                          (splitAnd (splitAnd header).1).1
                        let covered := (GeneralDeclarativeWitnessModeCoverage357.declaration_exact _ _).mp
                          (splitAnd (splitAnd header).1).2
                        let ready := GeneralDeclarativeWitnessModeDeclaration357.declaration_ready
                          covered (splitAnd header).2
                        let noWhere := List.isEmpty_iff.mp (splitAnd boundary).1
                        have checked : DeclarationChecked (authoredRegistry core.current).constructors
                            (authoredRegistry core.current).roles d := by
                          refine ⟨ready.signature,ready.identified,ready.produced,ready.outputOnly,
                            ready.scopeOK,ready.constructorScoped,?_,?_,?_,?_⟩ <;>
                            (intro c member; simp [noWhere] at member)
                        let noOut := List.isEmpty_iff.mp (splitAnd boundary).2
                        have author : ∃ row ∈ src.roles.rows, row.role = p.root.demand.role := by
                          cases roleAt : Checker408.originalRole p with
                          | none => simp [roleAt] at roleSeen
                          | some row =>
                            have original := GeneralSourceMetadataRoles291.indexed roleAt
                            exact ⟨row,original.1,original.2⟩
                        let matched : InvariantListHead p.state p.root d :=
                          ⟨whole,author,knownRoles,checked,covered,arg,args,key,binder,named,origin,
                            List.mem_of_getElem? atOrigin,same.2.1,same.2.2.1,same.2.2.2,
                            payload,by rw [endpoint,same.1]; rfl,actual,mode,table,atom,noWhere,noOut⟩
                        let safe : ¬RootCycle p.state p.root := by
                          rintro ⟨a,position,cycle⟩
                          rw [args] at position
                          cases List.mem_singleton.mp position
                          exact exact_escape_refutes_raw_root_K2410 clear cycle
                        some ⟨matched,safe⟩
                      else none
                    else none
                  else none
                else none
              | _ => none
          else none
        | _,_ => none
      else none
    else none
  else none

theorem replay_list_possesses_actual_point410 {p d whole w packet}
    (_ : replayListHead p d whole w = some packet) :
    ∃ origin ∈ p.state.core.origins,
      d.head = [.app packet.known.key [.var packet.known.binder]] ∧
      origin.slot = packet.known.arg.center ∧
      origin.endpoint = listPoint410 packet.known.key packet.known.payload ∧
      packet.known.capture packet.known.binder =
        GeneralDeclarativeWitnessDeclaredState357.point packet.known.payload ∧
      ¬RootCycle p.state p.root :=
  ⟨packet.known.origin,packet.known.authored,packet.known.named,packet.known.center,
    packet.known.endpoint,by simp [InvariantListHead.capture],packet.rawSafe⟩

private theorem list_forest_empty410 {s qs} (f : WhereForest R2 s qs []) :
    forestWrites f = [] := by cases f; rfl

theorem list_choice_captures_exact_report410 {p d} (live : VerifiedList p d) :
    ∃ (event : Event p.state p.root)
      (trace : SourceTrace R2 p.state p.root (.selected d.id []) (some event)),
      event.frame.input live.known.binder =
        GeneralDeclarativeWitnessDeclaredState357.point live.known.payload ∧
      writes trace = [] := by
  let a := live.known
  obtain ⟨origin⟩ := selected_head_original_origin395
    (invariant_list_selected_without_visit410 a live.rawSafe)
  have first : origin.pick = a.candidate := by
    have one : ∀ rows (h : rows = [d]),
        let t : CandidateTape p.state.core p.root rows := h.symm ▸ .next (.matched a.candidate) .nil
        storedCandidateEntries401 t = [(0,⟨d,a.candidate⟩)] := by
      intro rows h
      cases h
      rfl
    have sight := original_stored_entry_is_listed401 origin.stored
    change (origin.visibleOrdinal,⟨d,origin.pick⟩) ∈ storedCandidateEntries401 a.tape at sight
    unfold InvariantListHead.tape at sight
    rw [one _ a.only] at sight
    exact eq_of_heq (Sigma.mk.inj (congrArg Prod.snd (List.mem_singleton.mp sight))).2
  have empty : ∀ i : Fin p.root.demand.outputs.length, False := by
    intro i
    have bad := i.isLt
    simp [a.noOutputs] at bad
  let event : Event p.state p.root := ⟨preoutputFrameOfOrigin399 origin unusedPlacement403 (fun _ => emptyCapture403),
    origin.pick.head, fun i => (empty i).elim⟩
  have head : event.head = a.head := congrArg AuthoredCandidate.head first
  let rule : R2.elected p.state p.root event [] := .inr ⟨rfl,⟨a,head,rfl⟩⟩
  have noKids : event.kids = [] := by
    simp [Event.kids,event,frameWhereKids400,AuthoredBodyFrame393.clauses,
      preoutputFrameOfOrigin399,frameAtSource395,a.noWhere,children]
  let forest : WhereForest R2 p.state event.kids [] := noKids ▸ .nil
  let exactTrace : SourceTrace R2 p.state p.root (.selected d.id []) (some event) :=
    .selected event live.rawSafe rule .nil forest
  have capture : event.frame.input a.binder =
      GeneralDeclarativeWitnessDeclaredState357.point a.payload := by
    change preoutputInputOfHead399 origin.pick.head (fun _ => emptyCapture403) a.binder = _
    rw [first]
    change a.capture a.binder = _
    simp [InvariantListHead.capture]
  refine ⟨event,exactTrace,capture,?_⟩
  have emptyW : Check408.encodedEventWrites event = [] :=
    List.length_eq_zero_iff.mp (by simp [Check408.encodedEventWrites,a.noOutputs])
  have emptyF : forestWrites forest = [] := list_forest_empty410 forest
  change Check408.encodedEventWrites event ++ forestWrites forest = []
  rw [emptyW,emptyF]
  rfl

theorem list_choice_has_exact_R2_report410 {p d} (live : VerifiedList p d) :
    ClassifiedAs p.state p.root (Check408.nullaryReport d) := by
  obtain ⟨event,trace,_,writes⟩ := list_choice_captures_exact_report410 live
  exact ⟨some event,trace,.selected .nil (.selected rfl),writes.symm⟩

inductive Witness where
  | previous (data : Named409.Witness)
  | listLeaf (data : ListWire)
  | unsupported

def check (p : Problem) (r : Result) : Witness → Bool
  | .previous w => Named409.check p r w
  | .listLeaf w =>
    match whole : visible p.state.core p.root with
    | [d] => (replayListHead p d whole w).isSome &&
        Check408.matchesNoWrites r (.selected d.id []) (.selected (.node d.id []))
    | _ => false
  | .unsupported => false

theorem previous_entry_unchanged410 (p : Problem) (r : Result) (w : Named409.Witness) :
    check p r (.previous w) = Named409.check p r w := rfl

theorem checked_entry_has_exact_original_report410 (p : Problem) (r : Result) (w : Witness)
    (yes : check p r w = true) : ClassifiedAs p.state p.root r := by
  cases w with
  | previous proof => exact existing_exact_report_lifts410 (Named409.check_sound p r proof yes).1
  | unsupported => simp [check] at yes
  | listLeaf proof =>
    simp only [check] at yes
    split at yes
    · rename_i d scope
      obtain ⟨valid,report⟩ := splitAnd yes
      cases replay : replayListHead p d scope proof with
      | none => simp [replay] at valid
      | some verified =>
        obtain ⟨tree,verdict,writes⟩ := Check408.matchesNoWrites_exact408.mp report
        have matchReport : r = Check408.nullaryReport d := by
          cases r
          simp only at tree verdict writes
          subst_vars
          rfl
        exact matchReport ▸ list_choice_has_exact_R2_report410 verified
    · simp at yes

/-- Same I-65 report meanings and universal fits; only the local rules
classified by the extended exact trace are enlarged. -/
theorem check_sound (p : Problem) (r : Result) (w : Witness) (yes : check p r w = true) :
    ClassifiedAs p.state p.root r ∧ ∀ m : I72.Model, Fits p.state m → ReportEvidence p.state m p.root r := by
  have eq := checked_entry_has_exact_original_report410 p r w yes
  refine ⟨eq,?_⟩
  obtain ⟨e,t,sums,out⟩ := eq
  exact fun m fit => ⟨e,t,sums,out,mixed_R2_trace_model_meaning410 t m fit⟩

end Yulang.GeneralDeclarativeI65.I72.List410
