import Yulang.GeneralDeclarativeI65I74RoutedNominalMixedEntry456

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RecordDiagnosticReady457
open GeneralDeclarations (Declaration Clause DeclarationChecked)
open GeneralDeclarativeWitnessClassifyVariance357 (DeclarationReady)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry Current)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open GeneralDeclarationPatterns
open RecordTrail455 (localAuthorBits local_author_bits_exact455)
open RecordTree455
open GeneralDeclarativeWitnessChecks349 (counts)

theorem countsExact457 (head child : List Pattern) : counts head child = true ↔ CountsCovered head child := by
  exact Bool.and_eq_true_iff

structure ExactClosedTreeHeader (cur : Current) (d : Declaration) (c : Clause) (empty : Nat) : Prop where
  original : d.requirements = [c]
  covered : DeclarationCovered cur.environment d
  signature : d.Signature (authoredRegistry cur).roles
  identified : d.Identified
  produced : d.Produced
  outputs : d.OutputOnly
  lexical : d.Scoped
  head : WrittenArgs empty d.head
  whereTree : WrittenArgs empty c.arguments
  scopeCount : CountsCovered d.head c.arguments
  actualSmaller : Smaller d.head c.arguments

def checkDiagnosticReady (cur : Current) (d : Declaration) (c : Clause) (empty : Nat) : Bool :=
  localAuthorBits cur.environment d && checkTrees empty d.head &&
    checkTrees empty c.arguments && counts d.head c.arguments &&
    checkSmaller d.head c.arguments

theorem genuine_local_header_checks_the_same_authored_scope457 {cur d c empty}
    (actual : d.requirements = [c]) :
    checkDiagnosticReady cur d c empty = true ↔ ExactClosedTreeHeader cur d c empty := by
  constructor
  · intro yes
    simp only [checkDiagnosticReady,Bool.and_eq_true] at yes
    rcases yes with ⟨⟨⟨⟨declaration,head⟩,body⟩,count⟩,smaller⟩
    obtain ⟨cover,sig,id,produces,only,scope⟩ := (local_author_bits_exact455 ..).mp declaration
    exact ⟨actual,cover,sig,id,produces,only,scope,(checkTrees_exact ..).mp head,(checkTrees_exact ..).mp body,
      (countsExact457 ..).mp count,(checkSmaller_exact ..).mp smaller⟩
  · intro ctx
    simp only [checkDiagnosticReady,Bool.and_eq_true]
    exact ⟨⟨⟨⟨(local_author_bits_exact455 ..).mpr
      ⟨ctx.covered,ctx.signature,ctx.identified,ctx.produced,ctx.outputs,ctx.lexical⟩,
      (checkTrees_exact ..).mpr ctx.head⟩,(checkTrees_exact ..).mpr ctx.whereTree⟩,
      (countsExact457 ..).mpr ctx.scopeCount⟩,(checkSmaller_exact ..).mpr ctx.actualSmaller⟩

theorem actual_closed_header_supplies_prior_declaration_ready457 {cur d c empty}
    (p : ExactClosedTreeHeader cur d c empty) : DeclarationReady (authoredRegistry cur) d := by
  refine ⟨p.signature,p.identified,p.produced,p.outputs,p.lexical,
    GeneralDeclarativeWitnessModeDeclaration357.scoped_decl p.covered,?_⟩
  intro k present
  rw [p.original] at present
  cases List.mem_singleton.mp present
  exact ⟨p.actualSmaller,written_tree_paterson_stable_under_all_captures455 p.head p.whereTree p.actualSmaller⟩

theorem conservativity_is_the_only_missing_closed_header_field457 {cur d c empty}
    (p : ExactClosedTreeHeader cur d c empty) :
    DeclarationChecked (authoredRegistry cur).constructors (authoredRegistry cur).roles d ↔
      ConservativeSmaller d.head c.arguments := by
  have mem : c ∈ d.requirements := p.original ▸ List.mem_cons_self
  constructor
  · intro verified
    exact verified.conservative c mem
  · intro conservative
    refine ⟨p.signature,p.identified,p.produced,p.outputs,p.lexical,
      GeneralDeclarativeWitnessModeDeclaration357.scoped_decl p.covered,?_,?_,?_,?_⟩
    all_goals intro k present; rw [p.original] at present; cases List.mem_singleton.mp present
    · exact p.scopeCount
    · exact p.actualSmaller
    · exact conservative
    · exact written_tree_paterson_stable_under_all_captures455 p.head p.whereTree p.actualSmaller





end Yulang.GeneralDeclarativeI65.I72.RecordDiagnosticReady457



set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RoutedReadyHeader457
open Yulang.GeneralDeclarativeI65
open GeneralDeclarationPatterns
open GeneralDeclarations (Declaration Clause DeclarationChecked)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCenteredHeadMatExpressions (Expr application translate)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open RecordTree455
open RecordTrail455 (localAuthorBits local_author_bits_exact455 checkEmpty EmptyConstructor
  check_empty_reads_actual_primitive455)
open RecordK2412 (recordDescent412)
open Checker408 (Problem)

open RoutedRecord455 (admitted_source_trees_retain_their_true_authored_declaration455 verifySyntax)

open RecordDiagnosticReady457
open RoutedQueryHeader456 (QueryDecoder)

structure AuthoredHeader (p : Problem) (q : QueryDecoder p.state.core) (d : Declaration) where
  emptyKey : Nat
  written : Pattern
  clause : Clause
  arg : Capture
  query : Expr
  only : visible p.state.core p.root = [d]
  head : d.head = [written]
  requirement : d.requirements = [clause]
  argv : p.root.demand.arguments = [arg]
  atCenter : arg.lower = arg.center ∧ arg.center = arg.upper
  noGoalOutputs : p.root.demand.outputs = []
  noWhereOutputs : clause.outputs = []
  actualEmpty : EmptyConstructor p ⟨emptyKey,0,[],[]⟩
  admissibleHead : WrittenArgs emptyKey d.head
  admissibleBody : WrittenArgs emptyKey clause.arguments
  authoredRole : ∃ row ∈ p.state.core.current.environment.source.roles.rows,
    row.role = p.root.demand.role
  rolesValid : GeneralSourceMetadataRoles291.Valid p.state.core.current.environment.source.roles
  preserved : ExactClosedTreeHeader p.state.core.current d clause emptyKey
  translated : q.declarative (normalize written) query

private theorem role_present_exact (p : Problem) :
    (Checker408.originalRole p).isSome = true ↔
      ∃ row ∈ p.state.core.current.environment.source.roles.rows, row.role = p.root.demand.role := by
  constructor
  · intro did
    cases read : Checker408.originalRole p with
    | none => simp [read] at did
    | some row =>
      have observed := GeneralSourceMetadataRoles291.indexed read
      exact ⟨row,observed.1,observed.2⟩
  · exact Opaque448.original_role_is_read448 (p := p)

def readReadyHeader (p : Problem) (q : QueryDecoder p.state.core) (d : Declaration) (only : visible p.state.core p.root = [d])
    (key : Nat) : Option (AuthoredHeader p q d) :=
  let cur := p.state.core.current
  match h : d.head, req : d.requirements, args : p.root.demand.arguments with
  | [t],[c],[a] =>
    if shape : verifySyntax p d a c key = true then
      if builtin : checkEmpty p ⟨key,0,[],[]⟩ = true then
        if role : (Checker408.originalRole p).isSome = true then
          if valid : GeneralSourceMetadataRoles291.check cur.environment.source.roles = true then
            if ready : checkDiagnosticReady cur d c key = true then
              match translated : q.decode (normalize t) with
              | none => none
              | some expr => by
                obtain ⟨arity,tree⟩ := splitAnd shape
                obtain ⟨pt,none⟩ := splitAnd arity
                obtain ⟨noQ,noC⟩ := splitAnd none
                obtain ⟨hr,br⟩ := splitAnd tree
                have core := (genuine_local_header_checks_the_same_authored_scope457 req).mp ready
                exact some ⟨key,t,c,a,expr,only,h,req,args,of_decide_eq_true pt,
                  List.isEmpty_iff.mp noQ,List.isEmpty_iff.mp noC,
                  (check_empty_reads_actual_primitive455 ..).mp builtin,
                  (checkTrees_exact ..).mp hr,(checkTrees_exact ..).mp br,(role_present_exact p).mp role,
                  (GeneralSourceMetadataRoles291.check_exact _).mp valid,core,(q.exact _ _).mp translated⟩
            else none
          else none
        else none
      else none
    else none
  | _,_,_ => none

theorem exact_same_written_local_ready_header_replays457 {p q d} (a : AuthoredHeader p q d) :
    readReadyHeader p q d a.only a.emptyKey = some a := by
  have exactQuery := (q.exact _ _).mpr a.translated
  have shape : verifySyntax p d a.arg a.clause a.emptyKey = true := by
    unfold verifySyntax
    rw [decide_eq_true a.atCenter,List.isEmpty_iff.mpr a.noGoalOutputs,
      List.isEmpty_iff.mpr a.noWhereOutputs,(checkTrees_exact ..).mpr a.admissibleHead,
      (checkTrees_exact ..).mpr a.admissibleBody]
    rfl
  have builtin := (check_empty_reads_actual_primitive455 ..).mpr a.actualEmpty
  have role := (role_present_exact _).mpr a.authoredRole
  have valid := (GeneralSourceMetadataRoles291.check_exact _).mpr a.rolesValid
  have ready := (genuine_local_header_checks_the_same_authored_scope457 a.requirement).mpr a.preserved
  unfold readReadyHeader
  split
  · rename_i t c input head req args
    have et := List.singleton_inj.mp (head.symm.trans a.head)
    have ec := List.singleton_inj.mp (req.symm.trans a.requirement)
    have eq := List.singleton_inj.mp (args.symm.trans a.argv)
    subst t; subst c; subst input
    simp only [shape,builtin,role,valid,ready,dite_true]
    split
    · rename_i absent
      rw [exactQuery] at absent
      cases absent
    · rename_i expr present
      rw [exactQuery] at present
      cases Option.some.inj present
      cases a
      rfl
  · rename_i no
    exact (no _ _ _ a.head a.requirement a.argv).elim

theorem read_ready_supplies_already_established_declaration_ready457
    {p q d} (h : AuthoredHeader p q d) :
    GeneralDeclarativeWitnessClassifyVariance357.DeclarationReady
      (authoredRegistry p.state.core.current) d :=
  actual_closed_header_supplies_prior_declaration_ready457 h.preserved



theorem old_exact_header_gives_same_ready_header457
    {p q d} (h : RoutedQueryHeader456.AuthoredHeader p q d) :
    ∃ a : AuthoredHeader p q d,
      a.query = h.query ∧ a.written = h.written ∧ a.clause = h.clause ∧
        readReadyHeader p q d h.only h.emptyKey = some a := by
  have member : h.clause ∈ d.requirements := h.requirement ▸ List.mem_cons_self
  let proof : ExactClosedTreeHeader p.state.core.current d h.clause h.emptyKey :=
    ⟨h.requirement,h.covered,h.checked.signature,h.checked.identified,h.checked.produced,
      h.checked.outputOnly,h.checked.scope,h.admissibleHead,h.admissibleBody,
      h.checked.countsCovered h.clause member,h.checked.paterson h.clause member⟩
  let same : AuthoredHeader p q d :=
    ⟨h.emptyKey,h.written,h.clause,h.arg,h.query,h.only,h.head,h.requirement,h.argv,h.atCenter,
      h.noGoalOutputs,h.noWhereOutputs,h.actualEmpty,h.admissibleHead,h.admissibleBody,h.authoredRole,
      h.rolesValid,proof,h.translated⟩
  exact ⟨same,rfl,rfl,rfl,exact_same_written_local_ready_header_replays457 same⟩



end Yulang.GeneralDeclarativeI65.I72.RoutedReadyHeader457

set_option backward.isDefEq.respectTransparency false
