import Yulang.GeneralDeclarativeI65I74NamedReport409
import Yulang.GeneralDeclarativeWitnessModeDeclaration357

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Named409
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration DeclarationChecked)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessConstructorModes357 (readUse)
open GeneralDeclarativeWitnessSparseIntervals357 (names)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralDeclarativeWitnessRank350 (Table)
open CommonRoleOutermostResolver (Summarizes)
open Checker408 (Problem Result)

structure NamedWire where
  original : Nat
  levels : Table

structure VerifiedName (p : Problem) (d : Declaration) where
  known : NamedHead p.state p.root d
  rawSafe : ¬RootCycle p.state p.root

/-- Use the original ordered list, actual role metadata and origin. Bare
named syntax makes the recursion inside its nominal declaration opaque;
the unfiltered ordinary K2 check still applies before every positive leaf. -/
def replayNamedHead (p : Problem) (d : Declaration)
    (whole : visible p.state.core p.root = [d]) (w : NamedWire) :
    Option (VerifiedName p d) := do
  let core := p.state.core
  let env := core.current.environment
  let src := env.source
  if roleSeen : (Checker408.originalRole p).isSome = true then
    if header : (GeneralSourceMetadataRoles291.check src.roles &&
        GeneralDeclarativeWitnessModeCoverage357.checkDecl env d &&
        GeneralDeclarativeWitnessCovariantDescent353.legal src d) = true then
      if boundary : (d.requirements.isEmpty && p.root.demand.outputs.isEmpty) = true then
        if ranked : GeneralDeclarativeWitnessRank350.check core.current.ordinary w.levels = true then
          match named : d.head, args : p.root.demand.arguments with
          | [.app key []], [arg] =>
            match atOrigin : core.origins[w.original]? with
            | none => none
            | some origin =>
              match endpoint : origin.endpoint with
              | .nominal originKey [] =>
                if same : originKey = key ∧ origin.slot = arg.lower ∧ origin.slot = arg.upper then
                  let actual ← readUse env key 0
                  if mode : names actual.mode 0 = some [] then
                    if table : core.modes[key]? = some [] then
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
                      let matched : NamedHead p.state p.root d :=
                        ⟨whole,author,checked,covered,arg,args,key,named,origin,List.mem_of_getElem? atOrigin,
                          same.2.1,same.2.2,by rw [endpoint,same.1],actual,mode,table,noWhere,noOut⟩
                      let safe : ¬RootCycle p.state p.root := by
                        rintro ⟨a,_,cycle⟩
                        exact GeneralDeclarativeTaggedElection340.no_cycles
                          (GeneralDeclarativeWitnessRank350.sound ranked) a.lower cycle
                      some ⟨matched,safe⟩
                    else none
                  else none
                else none
              | _ => none
          | _,_ => none
        else none
      else none
    else none
  else none

theorem replay_named_route_is_original409 {p d whole w checked}
    (_ : replayNamedHead p d whole w = some checked) :
    ∃ origin ∈ p.state.core.origins,
      p.root.demand.arguments = [checked.known.arg] ∧
      d.head = [.app checked.known.key []] ∧
      origin.slot = checked.known.arg.lower ∧ origin.slot = checked.known.arg.upper ∧
      origin.endpoint = .nominal checked.known.key [] ∧ ¬RootCycle p.state p.root :=
  ⟨checked.known.origin,checked.known.authored,checked.known.asked,checked.known.named,
    checked.known.lo,checked.known.hi,checked.known.endpoint,checked.rawSafe⟩

private theorem named_forest_empty409 {s qs} (f : WhereForest R1 s qs []) :
    forestWrites f = [] := by cases f; rfl

theorem named_choice_has_exact_R1_report409 {p d} (live : VerifiedName p d) :
    ClassifiedAs p.state p.root (Check408.nullaryReport d) := by
  let a := live.known
  obtain ⟨origin⟩ := selected_head_original_origin395
    (named_sole_selected_without_opening409 a live.rawSafe)
  have first : origin.pick = a.candidate := by
    have one : ∀ rows (h : rows = [d]),
        let t : CandidateTape p.state.core p.root rows := h.symm ▸ .next (.matched a.candidate) .nil
        storedCandidateEntries401 t = [(0,⟨d,a.candidate⟩)] := by
      intro rows h
      cases h
      rfl
    have sight := original_stored_entry_is_listed401 origin.stored
    change (origin.visibleOrdinal,⟨d,origin.pick⟩) ∈ storedCandidateEntries401 a.tape at sight
    unfold NamedHead.tape at sight
    rw [one _ a.only] at sight
    exact eq_of_heq (Sigma.mk.inj (congrArg Prod.snd (List.mem_singleton.mp sight))).2
  have empty : ∀ i : Fin p.root.demand.outputs.length, False := by
    intro i
    have bad := i.isLt
    simp [a.noOutputs] at bad
  let event : Event p.state p.root := ⟨preoutputFrameOfOrigin399 origin unusedPlacement403 (fun _ => emptyCapture403),
    origin.pick.head, fun i => (empty i).elim⟩
  have head : event.head = a.head := congrArg AuthoredCandidate.head first
  let rule : R1.elected p.state p.root event [] := .inr ⟨rfl,⟨a,head,rfl⟩⟩
  have noKids : event.kids = [] := by
    simp [Event.kids,event,frameWhereKids400,AuthoredBodyFrame393.clauses,
      preoutputFrameOfOrigin399,frameAtSource395,a.noWhere,children]
  let forest : WhereForest R1 p.state event.kids [] := noKids ▸ .nil
  let exactTrace : SourceTrace R1 p.state p.root (.selected d.id []) (some event) :=
    .selected event live.rawSafe rule .nil forest
  refine ⟨some event,exactTrace,.selected .nil (.selected rfl),?_⟩
  have emptyW : Check408.encodedEventWrites event = [] :=
    List.length_eq_zero_iff.mp (by simp [Check408.encodedEventWrites,a.noOutputs])
  have emptyF : forestWrites forest = [] := named_forest_empty409 forest
  change [] = Check408.encodedEventWrites event ++ forestWrites forest
  rw [emptyW,emptyF]
  rfl

inductive Witness where
  | previous (data : Checker408.Witness)
  | bareName (data : NamedWire)
  | unsupported

def check (p : Problem) (r : Result) : Witness → Bool
  | .previous w => Checker408.check p r w
  | .bareName w =>
    match whole : visible p.state.core p.root with
    | [d] => (replayNamedHead p d whole w).isSome &&
        Check408.matchesNoWrites r (.selected d.id []) (.selected (.node d.id []))
    | _ => false
  | .unsupported => false

theorem previous_entry_unchanged409 (p : Problem) (r : Result) (w : Checker408.Witness) :
    check p r (.previous w) = Checker408.check p r w := rfl

theorem checked_entry_has_exact_original_report409 (p : Problem) (r : Result) (w : Witness)
    (yes : check p r w = true) : ClassifiedAs p.state p.root r := by
  cases w with
  | previous proof => exact existing_exact_report_lifts409 (Checker408.check_sound p r proof yes).1
  | unsupported => simp [check] at yes
  | bareName proof =>
    simp only [check] at yes
    split at yes
    · rename_i d scope
      obtain ⟨valid,report⟩ := splitAnd yes
      cases replay : replayNamedHead p d scope proof with
      | none => simp [replay] at valid
      | some verified =>
        obtain ⟨tree,verdict,writes⟩ := Check408.matchesNoWrites_exact408.mp report
        have matchReport : r = Check408.nullaryReport d := by
          cases r
          simp only at tree verdict writes
          subst_vars
          rfl
        exact matchReport ▸ named_choice_has_exact_R1_report409 verified
    · simp at yes

/-- Same I-65 report meanings and universal fits; only the local rules
classified by the extended exact trace are enlarged. -/
theorem check_sound (p : Problem) (r : Result) (w : Witness) (yes : check p r w = true) :
    ClassifiedAs p.state p.root r ∧ ∀ m : I72.Model, Fits p.state m → ReportEvidence p.state m p.root r := by
  have eq := checked_entry_has_exact_original_report409 p r w yes
  refine ⟨eq,?_⟩
  obtain ⟨e,t,sums,out⟩ := eq
  exact fun m fit => ⟨e,t,sums,out,mixed_R1_trace_model_meaning409 t m fit⟩

end Yulang.GeneralDeclarativeI65.I72.Named409
