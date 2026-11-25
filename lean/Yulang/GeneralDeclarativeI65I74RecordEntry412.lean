import Yulang.GeneralDeclarativeI65I74RecordReport412
import Yulang.GeneralDeclarativeI65I74RecordDeclaration412

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RecordK2412
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralNominalCenteredHeadMatExpressions (application translate)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeWitnessCycle350 (Link Hop checksHop close hop path)
open List410 (ExactEscapeWire checkExactEscape exact_escape_refutes_raw_root_K2410)
open Checker408 (Problem Result)

structure FieldCycleWire where
  first : Hop
  rest : List Hop
  closes : Link

/-- Run the existing raw graph checks directly on the entered logical
site. There is no substituted Request, fabricated where, or child's
root judgement in this branch. -/
def checkCycleAt412 (s : GeneralDeclarativeHead320.State) (site : Nat) (w : FieldCycleWire) : Bool :=
  checksHop s site w.first && close s w.first.child site w.closes w.rest

theorem cycle_at_sound412 {s site w} (yes : checkCycleAt412 s site w = true) :
    AliasCycle s (observed s) site := by
  obtain ⟨first,tail⟩ := splitAnd yes
  obtain ⟨last,walk,alias⟩ := path tail
  exact ⟨w.first.child,last,hop first,walk,alias⟩

structure FieldWire where
  originOrdinal : Nat
  outerRowOrdinal : Nat
  escape : ExactEscapeWire
  cycle : FieldCycleWire

structure VerifiedField (p : Problem) where
  rejection : RecordRejection p.state p.root
  rootSafe : ¬RootCycle p.state p.root

open GeneralNominalCenteredHeadMatExpressions (Expr)

theorem nested_pattern_uses_original_empty412 {s : GeneralDeclarativeWitnessDeclaredState357.Current}
    {box tick binder empty : Nat}
    (source : application (authoredRegistry s).constructors
      (interpretation s.environment.source.snapshot) empty [] = some (.primitive .emptyRecord [])) :
    translate (authoredRegistry s).constructors (interpretation s.environment.source.snapshot)
      (normalize (closedHead412 box tick empty binder)) = some (query412 box tick binder) := by
  simp [closedHead412,query412,normalize,GeneralDeclarationPatterns.normalizeArgs,translate,
    GeneralDeclarationPatterns.hide,GeneralNominalCenteredHeadMatExpressions.translateMany,source]

def replayField412 (p : Problem) (d : Declaration) (single : visible p.state.core p.root = [d])
    (w : FieldWire) : Option (VerifiedField p) := do
  let core := p.state.core
  let cur := core.current
  let src := cur.environment.source
  if roleSeen : (Checker408.originalRole p).isSome = true then
    if metadata : (GeneralSourceMetadataRoles291.check src.roles &&
        GeneralDeclarativeWitnessModeCoverage357.checkDecl cur.environment d && header412 cur d) = true then
      match h : d.head, asked : p.root.demand.arguments, body : d.requirements with
      | [.record box (.record tick (.var binder) (.app innerEmpty [])) (.app empty [])], [arg], [c] =>
        if outline : innerEmpty = empty ∧ c.role = p.root.demand.role ∧
            c.arguments = [closedWhere412 box empty binder] ∧ c.outputs = [] ∧
            p.root.demand.outputs = [] then
          if dec : recordDescent412 d.head c.arguments = true then
            if safe : checkExactEscape cur.ordinary arg.lower w.escape = true then
              match originAt : core.origins[w.originOrdinal]? with
              | some origin =>
                match endpoint : origin.endpoint with
                | .ordinary (.record observedBox (.var site) .emptyRecord) =>
                  if rows : observedBox = box ∧ origin.slot = arg.lower ∧ origin.slot = arg.center ∧
                      origin.slot = arg.upper ∧
                      cur.ordinary.equations[w.outerRowOrdinal]? = some (recordRow412 arg.lower box site) then
                    match tailAt : application (authoredRegistry cur).constructors
                        (interpretation src.snapshot) empty [] with
                    | some (.primitive .emptyRecord []) =>
                      if raw : checkCycleAt412 cur.ordinary site w.cycle = true then
                        let goodRoles := (GeneralSourceMetadataRoles291.check_exact _).mp
                          (splitAnd (splitAnd metadata).1).1
                        let coverage := (GeneralDeclarativeWitnessModeCoverage357.declaration_exact _ _).mp
                          (splitAnd (splitAnd metadata).1).2
                        let actualHead : d.head = [closedHead412 box tick empty binder] := by
                          simpa [closedHead412,outline.1] using h
                        let checked := checked_record_header412 coverage (splitAnd metadata).2
                          actualHead body outline.2.2.1 dec
                        have author : ∃ row ∈ src.roles.rows, row.role = p.root.demand.role := by
                          cases roleAt : Checker408.originalRole p with
                          | none => simp [roleAt] at roleSeen
                          | some row =>
                            have named := GeneralSourceMetadataRoles291.indexed roleAt
                            exact ⟨row,named.1,named.2⟩
                        let actual : ActualRecordField p.state p.root d :=
                          ⟨single,author,goodRoles,checked,arg,asked,outline.2.2.2.2,
                            box,tick,empty,binder,actualHead,c,body,outline.2.1,outline.2.2.1,
                            outline.2.2.2.1,nested_pattern_uses_original_empty412 tailAt,
                            origin,List.mem_of_getElem? originAt,rows.2.1,rows.2.2.1,rows.2.2.2.1,
                            site,by rw [endpoint,rows.1]; rfl,List.mem_of_getElem? rows.2.2.2.2⟩
                        let rootSafe : ¬RootCycle p.state p.root := by
                          rintro ⟨a,present,cycle⟩
                          rw [asked] at present
                          cases List.mem_singleton.mp present
                          exact exact_escape_refutes_raw_root_K2410 safe cycle
                        some ⟨⟨d,actual,cycle_at_sound412 raw⟩,rootSafe⟩
                      else none
                    | _ => none
                  else none
                | _ => none
              | none => none
            else none
          else none
        else none
      | _,_,_ => none
    else none
  else none

theorem field_rejection_has_exact_report412 (p : Problem) (v : VerifiedField p) :
    ClassifiedAs p.state p.root Check408.rawReport := by
  let actual : SourceTrace R4 p.state p.root .rejected none :=
    .other .rejected v.rootSafe (.inr ⟨rfl,rfl,⟨v.rejection⟩⟩) .nil
  exact ⟨none,actual,.rejected,rfl⟩

inductive Witness where
  | previous (w : WhereCycle411.Witness)
  | fieldCycle (w : FieldWire)
  | unsupported

def check (p : Problem) (r : Result) : Witness → Bool
  | .previous w => WhereCycle411.check p r w
  | .fieldCycle w =>
    match scope : visible p.state.core p.root with
    | [d] => (replayField412 p d scope w).isSome && Check408.matchesNoWrites r .rejected .rejected
    | _ => false
  | .unsupported => false

theorem previous_entry_unchanged412 (p : Problem) (r : Result) (w : WhereCycle411.Witness) :
    check p r (.previous w) = WhereCycle411.check p r w := rfl

theorem checked_field_reflects_actual_original_rejection412 (p : Problem) (r : Result) (w : FieldWire)
    (yes : check p r (.fieldCycle w) = true) :
    ∃ (d : Declaration) (scope : visible p.state.core p.root = [d]) (v : VerifiedField p),
      replayField412 p d scope w = some v ∧ r = Check408.rawReport := by
  simp only [check] at yes
  split at yes
  · rename_i d scope
    obtain ⟨good,output⟩ := splitAnd yes
    cases found : replayField412 p d scope w with
    | none => simp [found] at good
    | some v =>
      obtain ⟨tree,verdict,writes⟩ := Check408.matchesNoWrites_exact408.mp output
      refine ⟨d,scope,v,found,?_⟩
      cases r
      simp only at tree verdict writes
      subst_vars
      rfl
  · simp at yes

theorem checked_field_has_exact_original_report412 (p : Problem) (r : Result) (w : Witness)
    (yes : check p r w = true) : ClassifiedAs p.state p.root r := by
  cases w with
  | previous old => exact existing_exact_report_lifts412 (WhereCycle411.check_sound p r old yes).1
  | fieldCycle data =>
    obtain ⟨_,_,v,_,same⟩ := checked_field_reflects_actual_original_rejection412 p r data yes
    exact same ▸ field_rejection_has_exact_report412 p v
  | unsupported => simp [check] at yes

theorem check_sound (p : Problem) (r : Result) (w : Witness) (yes : check p r w = true) :
    ClassifiedAs p.state p.root r ∧ ∀ m : I72.Model, Fits p.state m → ReportEvidence p.state m p.root r := by
  have eq := checked_field_has_exact_original_report412 p r w yes
  refine ⟨eq,?_⟩
  obtain ⟨e,t,sums,out⟩ := eq
  exact fun m fit => ⟨e,t,sums,out,mixed_R4_trace_model_meaning412 t m fit⟩

end Yulang.GeneralDeclarativeI65.I72.RecordK2412
