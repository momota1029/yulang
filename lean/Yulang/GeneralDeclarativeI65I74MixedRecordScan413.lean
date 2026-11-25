import Yulang.GeneralDeclarativeI65I74MixedRecordRule413

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.MixedRecord413
open GeneralDeclarativeI65
open GeneralDeclarations (Declaration DeclarationChecked)
open GeneralDeclarativeWitnessDeclaredState357 (point authoredRegistry)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open GeneralDeclarativeWitnessChecks349 (identified output_only produced scope_sound)
open GeneralDeclarativeWitnessSignature349 (checked_signature)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open GeneralNominalCenteredHeadMatExpressions (translate translateMany application)
open GeneralSourceMetadataRows291 (interpretation)
open RecordK2412 (closedHead412 closedWhere412 recordInput412 recordRow412 header412
  nested_pattern_uses_original_empty412)
open Checker408 (Problem)
open List410 (ExactEscapeWire checkExactEscape exact_escape_refutes_raw_root_K2410)

structure RootWire where
  original : Nat
  outerRow : Nat
  escape : ExactEscapeWire

structure VerifiedOuter (p : Problem) where
  actual : ActualOuterRecord p.state p.root
  safe : ¬RootCycle p.state p.root

def rootRead413 (p : Problem) (w : RootWire) : Option (VerifiedOuter p) := do
  let core := p.state.core
  let current := core.current
  let role := current.environment.source.roles
  if roleSeen : (Checker408.originalRole p).isSome = true then
    if metadata : GeneralSourceMetadataRoles291.check role = true then
      if output : p.root.demand.outputs = [] then
        match asked : p.root.demand.arguments with
        | [arg] =>
          if equal : arg.center = arg.lower ∧ arg.upper = arg.lower then
            if checked : checkExactEscape current.ordinary arg.lower w.escape = true then
              match found : core.origins[w.original]? with
              | some o =>
                match endpoint : o.endpoint with
                | .ordinary (.record box (.var site) .emptyRecord) =>
                  if row : o.slot = arg.lower ∧
                      current.ordinary.equations[w.outerRow]? = some (recordRow412 arg.lower box site) then
                    have same : arg = point arg.lower := by
                      cases arg
                      simp only [point]
                      congr
                      · exact equal.1
                      · exact equal.2
                    have authored : ∃ r ∈ role.rows, r.role = p.root.demand.role := by
                      cases seen : Checker408.originalRole p with
                      | none => simp [seen] at roleSeen
                      | some r =>
                        have facts := GeneralSourceMetadataRoles291.indexed seen
                        exact ⟨r,facts.1,facts.2⟩
                    let actual : ActualOuterRecord p.state p.root :=
                      ⟨arg.lower,box,site,asked.trans (congrArg (fun c => [c]) same),output,authored,
                        (GeneralSourceMetadataRoles291.check_exact _).mp metadata,o,List.mem_of_getElem? found,
                        row.1,endpoint,List.mem_of_getElem? row.2⟩
                    have safe : ¬RootCycle p.state p.root := by
                      rintro ⟨a,member,cycle⟩
                      rw [asked] at member
                      cases List.mem_singleton.mp member
                      exact exact_escape_refutes_raw_root_K2410 checked cycle
                    some ⟨actual,safe⟩
                  else none
                | _ => none
              | none => none
            else none
          else none
        | _ => none
      else none
    else none
  else none

theorem no_clause_header413 {s : GeneralDeclarativeWitnessDeclaredState357.Current} {d : Declaration}
    (cov : DeclarationCovered s.environment d) (head : header412 s d = true)
    (noWhere : d.requirements = []) :
    DeclarationChecked (authoredRegistry s).constructors (authoredRegistry s).roles d := by
  obtain ⟨ids,tail⟩ := splitAnd head
  obtain ⟨sig,unique⟩ := splitAnd ids
  obtain ⟨binders,scope⟩ := splitAnd tail
  obtain ⟨bind,only⟩ := splitAnd binders
  refine ⟨checked_signature sig,identified unique,produced bind,output_only only,scope_sound scope,
    GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cov,?_,?_,?_,?_⟩ <;>
    (intro c impossible; simp [noWhere] at impossible)

inductive RowKind {s q} (a : ActualOuterRecord s q) (d : Declaration) : Type where
  | binding (fact : PlainCandidate a d)
  | nested (fact : NestedCandidate a d)

theorem plain_uses_actual_empty413 {s : GeneralDeclarativeWitnessDeclaredState357.Current} {box empty binder}
    (known : application (authoredRegistry s).constructors (interpretation s.environment.source.snapshot)
      empty [] = some (.primitive .emptyRecord [])) :
    translate (authoredRegistry s).constructors (interpretation s.environment.source.snapshot)
      (closedWhere412 box empty binder) = some (bindingQuery413 box binder) := by
  simp [closedWhere412,bindingQuery413,translate,translateMany,known]

def readRow413 {s q} (a : ActualOuterRecord s q) (d : Declaration) : Option (RowKind a d) := do
  let cur := s.core.current
  let src := cur.environment.source
  if both : (GeneralDeclarativeWitnessModeCoverage357.checkDecl cur.environment d &&
      header412 cur d) = true then
    if noWhere : d.requirements = [] then
      let cov := (GeneralDeclarativeWitnessModeCoverage357.declaration_exact _ _).mp (splitAnd both).1
      let checked := no_clause_header413 cov (splitAnd both).2 noWhere
      match pattern : d.head with
      | [.record box (.var binder) (.app empty [])] =>
        if label : box = a.box then
          match tail : application (authoredRegistry cur).constructors (interpretation src.snapshot) empty [] with
          | some (.primitive .emptyRecord []) =>
            some (.binding ⟨binder,empty,by simpa [closedWhere412,label] using pattern,
              noWhere,cov,checked,plain_uses_actual_empty413 tail⟩)
          | _ => none
        else none
      | [.record box (.record tick (.var binder) (.app inner [])) (.app outer [])] =>
        if label : box = a.box ∧ inner = outer then
          match tail : application (authoredRegistry cur).constructors (interpretation src.snapshot) outer [] with
          | some (.primitive .emptyRecord []) =>
            some (.nested ⟨tick,binder,outer,by simpa [closedHead412,label.1,label.2] using pattern,
              noWhere,cov,checked,nested_pattern_uses_original_empty412 tail⟩)
          | _ => none
        else none
      | _ => none
    else none
  else none

inductive ListShape {s q} (a : ActualOuterRecord s q) (rows : List Declaration) where
  | plain (tape : PlainTape a rows)
  | mixed (tape : MixedTape a rows)

/-- Scan the entire independently recovered visibility list. Two
nested rows or any unsupported row gives no certificate in this
scope, rather than silently dropping that row. -/
def scanAll413 {s q} (a : ActualOuterRecord s q) :
    (rows : List Declaration) → Option (ListShape a rows)
  | [] => some (.plain .nil)
  | d :: rest => do
    let front ← readRow413 a d
    let tail ← scanAll413 a rest
    match front,tail with
    | .binding first,.plain after => some (.plain (.cons first after))
    | .binding first,.mixed after => some (.mixed (.next first after))
    | .nested first,.plain after => some (.mixed (.opens first after))
    | .nested _,.mixed _ => none

end Yulang.GeneralDeclarativeI65.I72.MixedRecord413
