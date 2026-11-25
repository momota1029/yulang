import Yulang.GeneralDeclarativeI65I74OpenTailReport414

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.OpenTail414
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarativeWitnessDeclaredState357 (point authoredRegistry)
open GeneralNominalCenteredHeadMatExpressions (application)
open GeneralSourceMetadataRows291 (interpretation)
open Checker408 (Problem Result)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open List410 (ExactEscapeWire checkExactEscape exact_escape_refutes_raw_root_K2410)

structure OpenWire where
  original : Nat
  rootEscape : ExactEscapeWire

structure VerifiedOpen (p : Problem) where
  actual : OpenInput p.state p.root
  rootSafe : ¬ RootCycle p.state p.root

private theorem pointExact414 {a : GeneralDeclarativeWhere319.Capture}
    (same : a.center = a.lower ∧ a.upper = a.lower) : a = point a.lower := by
  cases a
  simp only [point]
  congr
  · exact same.1
  · exact same.2

def readOpen414 (p : Problem) (w : OpenWire) : Option (VerifiedOpen p) := do
  let core := p.state.core
  let cur := core.current
  if output : p.root.demand.outputs = [] then
    match asked : p.root.demand.arguments with
    | [arg] =>
      if pointProof : arg.center = arg.lower ∧ arg.upper = arg.lower then
        if escape : checkExactEscape cur.ordinary arg.lower w.rootEscape = true then
          match found : core.origins[w.original]? with
          | some o =>
            match endpoint : o.endpoint with
            | .ordinary (.record label (.var field) (.var tail)) =>
              if names : arg.lower ≠ field ∧ arg.lower ≠ tail ∧ field ≠ tail then
                if rows : cur.ordinary.equations = [openRow arg.lower label field tail,intRow field] then
                  if absence : (cur.ordinary.normal.ordinary.isEmpty &&
                      cur.ordinary.normal.intervals.isEmpty && cur.visible.isEmpty && core.routes.isEmpty &&
                      core.origins.all (fun r => decide (r.slot ≠ tail))) = true then
                    if originSlot : o.slot = arg.lower then
                      let ⟨parts,noOriginal⟩ := splitAnd absence
                      let ⟨parts,noRoute⟩ := splitAnd parts
                      let ⟨parts,noNative⟩ := splitAnd parts
                      let ⟨noAtoms,noBounds⟩ := splitAnd parts
                      let actual : OpenInput p.state p.root :=
                        ⟨arg.lower,label,field,tail,asked.trans (congrArg (fun r => [r]) (pointExact414 pointProof)),
                          output,names.1,names.2.1,names.2.2,o,List.mem_of_getElem? found,originSlot,endpoint,
                          fun r h => of_decide_eq_true (List.all_eq_true.mp noOriginal r h),rows,
                          List.isEmpty_iff.mp noAtoms,List.isEmpty_iff.mp noBounds,
                          List.isEmpty_iff.mp noNative,List.isEmpty_iff.mp noRoute⟩
                      have safe : ¬ RootCycle p.state p.root := by
                        rintro ⟨a,member,cycle⟩
                        rw [asked] at member
                        cases List.mem_singleton.mp member
                        exact exact_escape_refutes_raw_root_K2410 escape cycle
                      some ⟨actual,safe⟩
                    else none
                  else none
                else none
              else none
            | _ => none
          | none => none
        else none
      else none
    | _ => none
  else none

def readCandidate414 {s q} (a : OpenInput s q) : Option (OpenCandidate a) := do
  let cur := s.core.current
  let roles := cur.environment.source.roles
  if table : GeneralSourceMetadataRoles291.check roles = true then
    match picked : GeneralSourceMetadataFiniteLookup291.get q.demand.role
          (GeneralSourceMetadataRoles291.index roles) with
    | none => none
    | some row =>
      let facts := GeneralSourceMetadataRoles291.indexed picked
      let declared : ∃ row ∈ roles.rows, row.role = q.demand.role := ⟨row,facts.1,facts.2⟩
      let valid := (GeneralSourceMetadataRoles291.check_exact roles).mp table
        match visibleRows : visible s.core q with
        | [d] =>
          if both : (GeneralDeclarativeWitnessModeCoverage357.checkDecl cur.environment d &&
              RecordK2412.header412 cur d) = true then
            if noWrites : d.associated = [] ∧ d.outputBinders = [] then
              match head : d.head, kids : d.requirements with
              | [.record label (.app intName []) (.var binder)], [clause] =>
                if verified : label = a.label ∧ clause = tailRequirement q.demand.role binder clause.id then
                  match real : application (authoredRegistry cur).constructors
                        (interpretation cur.environment.source.snapshot) intName [] with
                  | some (.primitive (.scalar .int) []) =>
                    some ⟨d,visibleRows,declared,valid,intName,binder,clause.id,by simpa [openHead,verified.1] using head,
                      kids.trans (congrArg (fun c => [c]) verified.2),noWrites.1,noWrites.2,
                      (GeneralDeclarativeWitnessModeCoverage357.declaration_exact _ _).mp (splitAnd both).1,
                      (splitAnd both).2,real⟩
                  | _ => none
                else none
              | _, _ => none
            else none
          else none
        | _ => none
  else none

structure OpenVerified (p : Problem) where
  pending : OpenTailPending p.state p.root
  rootSafe : ¬ RootCycle p.state p.root

def replayOpen414 (p : Problem) (w : OpenWire) : Option (OpenVerified p) := do
  let v ← readOpen414 p w
  let row ← readCandidate414 v.actual
  some ⟨⟨v.actual,row⟩,v.rootSafe⟩

def pendingReport : Result := ⟨.pending,.pending,[]⟩

theorem exact_open_input_supplies_pending414 (p : Problem) (proof : OpenVerified p) :
    ClassifiedAs p.state p.root pendingReport := by
  let actual : SourceTrace R6 p.state p.root .pending none :=
    .other .pending proof.rootSafe (.inr ⟨rfl,rfl,⟨proof.pending⟩⟩) .nil
  exact ⟨none,actual,.pending,rfl⟩

inductive Witness where
  | previous (old : MixedRecord413.Witness)
  | openTail (w : OpenWire)
  | unsupported

def check (p : Problem) (r : Result) : Witness → Bool
  | .previous w => MixedRecord413.check p r w
  | .openTail w => (replayOpen414 p w).isSome && Check408.matchesNoWrites r .pending .pending
  | .unsupported => false

theorem previous_entry_unchanged414 (p : Problem) (r : Result) (old : MixedRecord413.Witness) :
    check p r (.previous old) = MixedRecord413.check p r old := rfl

theorem checked_open_tail_reflects_original414 (p : Problem) (r : Result) (w : OpenWire)
    (success : check p r (.openTail w) = true) :
    ∃ v : OpenVerified p, replayOpen414 p w = some v ∧ r = pendingReport := by
  obtain ⟨source,report⟩ := splitAnd success
  cases captured : replayOpen414 p w with
  | none => simp [captured] at source
  | some v =>
    obtain ⟨tree,verdict,output⟩ := Check408.matchesNoWrites_exact408.mp report
    refine ⟨v,rfl,?_⟩
    cases r
    simp only at tree verdict output
    subst_vars
    rfl

theorem checked_entry_has_exact_original_report414 (p : Problem) (r : Result) (w : Witness)
    (yes : check p r w = true) : ClassifiedAs p.state p.root r := by
  cases w with
  | previous old => exact existing_exact_report_lifts414 (MixedRecord413.check_sound p r old yes).1
  | openTail fresh =>
    obtain ⟨v,_,same⟩ := checked_open_tail_reflects_original414 p r fresh yes
    exact same ▸ exact_open_input_supplies_pending414 p v
  | unsupported => simp [check] at yes

theorem check_sound (p : Problem) (r : Result) (w : Witness) (yes : check p r w = true) :
    ClassifiedAs p.state p.root r ∧ ∀ m : I72.Model, Fits p.state m → ReportEvidence p.state m p.root r := by
  have exact := checked_entry_has_exact_original_report414 p r w yes
  refine ⟨exact,?_⟩
  obtain ⟨e,t,sums,out⟩ := exact
  exact fun m fit => ⟨e,t,sums,out,open_R6_trace_model_meaning414 t m fit⟩

end Yulang.GeneralDeclarativeI65.I72.OpenTail414
