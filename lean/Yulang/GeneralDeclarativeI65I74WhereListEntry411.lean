import Yulang.GeneralDeclarativeI65I74WhereListReport411
import Yulang.GeneralDeclarativeWitnessChecks349
import Yulang.GeneralDeclarativeI65I74ExactEscape410
import Yulang.GeneralDeclarativeWitnessModeDeclaration357

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereCycle411
open GeneralDeclarativeI65
open List410 (ListWire ExactEscapeWire checkExactEscape exact_escape_refutes_raw_root_K2410 invariantValue410 listPoint410)
open GeneralDeclarativeWitnessChecks349 (checkedDescent descent_parts)
open GeneralDeclarations (Declaration DeclarationChecked)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessConstructorModes357 (readUse)
open GeneralDeclarativeWitnessSparseIntervals357 (names)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open CommonRoleOutermostResolver (Summarizes)
open Checker408 (Problem Result)

structure VerifiedWhereList (p : Problem) (d : Declaration) where
  known : WhereListHead p.state p.root d
  rawSafe : ¬RootCycle p.state p.root


open PresenceNormalForm (Atom)

/-- Read the actual original parent, literal where clause, and its lexical
validity. The child does not come from the witness. -/
def replayWhereList411 (p : Problem) (d : Declaration)
    (whole : visible p.state.core p.root = [d]) (w : ListWire) :
    Option (VerifiedWhereList p d) := do
  let core := p.state.core
  let env := core.current.environment
  let src := env.source
  if roleSeen : (Checker408.originalRole p).isSome = true then
    if header : (GeneralSourceMetadataRoles291.check src.roles &&
        GeneralDeclarativeWitnessModeCoverage357.checkDecl env d &&
        GeneralDeclarativeWitnessCovariantDescent353.legal src d) = true then
      match named : d.head, args : p.root.demand.arguments, whereAt : d.requirements with
      | [.app key [.var binder]], [arg], [c] =>
        if boundary : c.role = p.root.demand.role ∧ c.arguments = [.var binder] ∧
            c.outputs = [] ∧ p.root.demand.outputs = [] then
          if descent : checkedDescent d.head c.arguments = true then
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
                          have checked : DeclarationChecked (authoredRegistry core.current).constructors
                              (authoredRegistry core.current).roles d := by
                            refine ⟨ready.signature,ready.identified,ready.produced,ready.outputOnly,
                              ready.scopeOK,ready.constructorScoped,?_,?_,?_,?_⟩
                            all_goals
                              intro x member
                              rw [whereAt] at member
                              cases List.mem_singleton.mp member
                            · exact (descent_parts descent).1
                            · exact (descent_parts descent).2.1
                            · exact (descent_parts descent).2.2.1
                            · exact (descent_parts descent).2.2.2
                          have author : ∃ row ∈ src.roles.rows, row.role = p.root.demand.role := by
                            cases roleAt : Checker408.originalRole p with
                            | none => simp [roleAt] at roleSeen
                            | some row =>
                              have original := GeneralSourceMetadataRoles291.indexed roleAt
                              exact ⟨row,original.1,original.2⟩
                          let matched : WhereListHead p.state p.root d :=
                            ⟨whole,author,knownRoles,checked,covered,arg,args,key,binder,named,origin,
                              List.mem_of_getElem? atOrigin,same.2.1,same.2.2.1,same.2.2.2,
                              payload,by rw [endpoint,same.1]; rfl,actual,mode,table,atom,c,whereAt,
                              boundary.1,boundary.2.1,boundary.2.2.1,boundary.2.2.2⟩
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
          else none
        else none
      | _,_,_ => none
    else none
  else none

open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open GeneralDeclarativeWitnessCycle350 (Wire)

def WhereListHead.childDemand {s q d} (a : WhereListHead s q d) : Demand :=
  ⟨a.clause.role,[point a.payload],[]⟩

def WhereListHead.child {s q d} (a : WhereListHead s q d) : I72.Request :=
  ⟨q.occurrence ++ [0],a.childDemand⟩

theorem selected_where_is_exact_actual_child411 {p d} (live : VerifiedWhereList p d) :
    ∃ (event : Event p.state p.root), R3.elected p.state p.root event [] ∧
      event.frame.decl = d ∧ event.kids = [live.known.child] ∧
      event.frame.input live.known.binder = point live.known.payload ∧
      Check408.encodedEventWrites event = [] := by
  let a := live.known
  obtain ⟨origin⟩ := selected_head_original_origin395
    (invariant_list_selected_without_visit411 a live.rawSafe)
  have first : origin.pick = a.candidate := by
    have one : ∀ rows (h : rows = [d]),
        let t : CandidateTape p.state.core p.root rows := h.symm ▸ .next (.matched a.candidate) .nil
        storedCandidateEntries401 t = [(0,⟨d,a.candidate⟩)] := by
      intro rows h
      cases h
      rfl
    have sight := original_stored_entry_is_listed401 origin.stored
    change (origin.visibleOrdinal,⟨d,origin.pick⟩) ∈ storedCandidateEntries401 a.tape at sight
    unfold WhereListHead.tape at sight
    rw [one _ a.only] at sight
    exact eq_of_heq (Sigma.mk.inj (congrArg Prod.snd (List.mem_singleton.mp sight))).2
  have empty : ∀ i : Fin p.root.demand.outputs.length, False := by
    intro i
    have bad := i.isLt
    simp [a.noOutputs] at bad
  let event : Event p.state p.root := ⟨preoutputFrameOfOrigin399 origin unusedPlacement403 (fun _ => emptyCapture403),
    origin.pick.head, fun i => (empty i).elim⟩
  have head : event.head = a.head := congrArg AuthoredCandidate.head first
  let rule : R3.elected p.state p.root event [] := .inr ⟨rfl,⟨a,head,rfl⟩⟩
  have capture : event.frame.input a.binder = point a.payload := by
    change preoutputInputOfHead399 origin.pick.head (fun _ => emptyCapture403) a.binder = _
    rw [first]
    change a.capture a.binder = _
    simp [WhereListHead.capture]
  have whereDemand : (event.frame.whereFor a.clause).demand = a.childDemand := by
    have literal := literal_variable_where_uses_actual_names403 event.frame
      (binders := [a.binder]) (by simpa using a.whereArgs) a.whereOutputs
    have binderSource : a.binder ∈ d.inputNames := by
      simp [Declaration.inputNames,a.named,GeneralDeclarationPatterns.normalizeArgs,
        GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.normalize,
        GeneralDeclarationPatterns.Pattern.variables]
    have exactName : event.frame.names.input a.binder = event.frame.input a.binder :=
      GeneralDeclarativeProducedNames325.exact_input a.checked binderSource
    simpa [WhereListHead.childDemand,exactName,capture] using literal
  have kids : event.kids = [a.child] := by
    change frameWhereKids400 event.frame = _
    unfold frameWhereKids400 children AuthoredBodyFrame393.clauses
    change _ = _
    simp [event,preoutputFrameOfOrigin399,frameAtSource395,a.exactWhere]
    change (⟨p.root.occurrence ++ [0],(event.frame.whereFor a.clause).demand⟩ : I72.Request) = a.child
    rw [whereDemand]
    rfl
  have noWrites : Check408.encodedEventWrites event = [] :=
    List.length_eq_zero_iff.mp (by simp [Check408.encodedEventWrites,a.noOutputs])
  exact ⟨event,rule,rfl,kids,capture,noWrites⟩

def expected411 (d : Declaration) : Result :=
  ⟨.selected d.id [.rejected],.rejected,[]⟩

theorem selected_where_child_K2_has_exact_report411 {p d} (live : VerifiedWhereList p d)
    (cycle : RootCycle p.state live.known.child) :
    ClassifiedAs p.state p.root (expected411 d) := by
  obtain ⟨event,rule,decl,kids,_,ew⟩ := selected_where_is_exact_actual_child411 live
  let one : WhereForest R3 p.state [live.known.child] [.rejected] :=
    .cons (.rootK2 cycle) .nil
  let actual : WhereForest R3 p.state event.kids [.rejected] := kids.symm ▸ one
  let tree : SourceTrace R3 p.state p.root (.selected event.frame.decl.id [.rejected]) (some event) :=
    .selected event live.rawSafe rule .nil actual
  have sums : Summarizes (.selected event.frame.decl.id [.rejected]) .rejected :=
    .selected (.cons .rejected .nil) (.rejected List.mem_cons_self)
  have forestZero : ∀ qs (h : qs = [live.known.child]),
      forestWrites (h.symm ▸ one) = [] := by
    intro qs h
    cases h
    rfl
  have empty : writes tree = [] := by
    change Check408.encodedEventWrites event ++ forestWrites actual = []
    rw [ew,forestZero event.kids kids]
    rfl
  unfold expected411
  rw [← decl]
  exact ⟨some event,tree,sums,empty.symm⟩

structure CycleWire where
  parent : ListWire
  cycle : Wire

inductive Witness where
  | previous (w : List410.Witness)
  | whereChild (w : CycleWire)
  | unsupported

def check (p : Problem) (r : Result) : Witness → Bool
  | .previous w => List410.check p r w
  | .whereChild w =>
    match only : visible p.state.core p.root with
    | [d] =>
      match replayWhereList411 p d only w.parent with
      | none => false
      | some accepted =>
        GeneralDeclarativeWitnessCycle350.check p.state.core.current.ordinary
          accepted.known.child.demand w.cycle &&
        Check408.matchesNoWrites r (.selected d.id [.rejected]) .rejected
    | _ => false
  | .unsupported => false

theorem previous_entry_unchanged411 (p : Problem) (r : Result) (w : List410.Witness) :
    check p r (.previous w) = List410.check p r w := rfl

theorem checked_entry_has_exact_original_report411 (p : Problem) (r : Result) (w : Witness)
    (yes : check p r w = true) : ClassifiedAs p.state p.root r := by
  cases w with
  | previous proof => exact existing_exact_report_lifts411 (List410.check_sound p r proof yes).1
  | unsupported => simp [check] at yes
  | whereChild proof =>
    simp only [check] at yes
    split at yes
    · rename_i d scope
      split at yes
      · cases yes
      · rename_i packet replay
        obtain ⟨raw,report⟩ := splitAnd yes
        obtain ⟨tree,verdict,writes⟩ := Check408.matchesNoWrites_exact408.mp report
        have matchReport : r = expected411 d := by
          cases r
          simp only at tree verdict writes
          subst_vars
          rfl
        have cycle : RootCycle p.state packet.known.child :=
          GeneralDeclarativeWitnessCycle350.rooted raw
        exact matchReport ▸ selected_where_child_K2_has_exact_report411 packet cycle
    · simp at yes

theorem check_sound (p : Problem) (r : Result) (w : Witness) (yes : check p r w = true) :
    ClassifiedAs p.state p.root r ∧ ∀ m : I72.Model, Fits p.state m → ReportEvidence p.state m p.root r := by
  have eq := checked_entry_has_exact_original_report411 p r w yes
  refine ⟨eq,?_⟩
  obtain ⟨e,t,sums,out⟩ := eq
  exact fun m fit => ⟨e,t,sums,out,mixed_R3_trace_model_meaning411 t m fit⟩

end Yulang.GeneralDeclarativeI65.I72.WhereCycle411
