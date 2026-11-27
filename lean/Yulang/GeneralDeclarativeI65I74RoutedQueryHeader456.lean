import Yulang.GeneralDeclarativeI65I74RoutedNominalPoint456

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RoutedQueryHeader456
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

structure QueryDecoder (s : GeneralDeclarativeI65.State) where
  declarative : Pattern → Expr → Prop
  decode : Pattern → Option Expr
  exact : ∀ clause code, decode clause = some code ↔ declarative clause code

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
  covered : DeclarationCovered p.state.core.current.environment d
  checked : DeclarationChecked (authoredRegistry p.state.core.current).constructors
    (authoredRegistry p.state.core.current).roles d
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

def readHeader (p : Problem) (q : QueryDecoder p.state.core) (d : Declaration) (only : visible p.state.core p.root = [d])
    (key : Nat) : Option (AuthoredHeader p q d) :=
  let cur := p.state.core.current
  match h : d.head, req : d.requirements, args : p.root.demand.arguments with
  | [t],[c],[a] =>
    if shape : verifySyntax p d a c key = true then
      if builtin : checkEmpty p ⟨key,0,[],[]⟩ = true then
        if role : (Checker408.originalRole p).isSome = true then
          if valid : GeneralSourceMetadataRoles291.check cur.environment.source.roles = true then
            if stated : localAuthorBits cur.environment d = true then
              if desc : recordDescent412 d.head c.arguments = true then
                match translated : q.decode (normalize t) with
                | none => none
                | some expr => by
                  obtain ⟨arity,trees⟩ := splitAnd shape
                  obtain ⟨point,none⟩ := splitAnd arity
                  obtain ⟨noQ,noC⟩ := splitAnd none
                  obtain ⟨head,body⟩ := splitAnd trees
                  have hTree := (checkTrees_exact _ _).mp head
                  have bTree := (checkTrees_exact _ _).mp body
                  have localChecked :=
                    admitted_source_trees_retain_their_true_authored_declaration455 req hTree bTree stated desc
                  exact some ⟨key,t,c,a,expr,only,h,req,args,of_decide_eq_true point,
                    List.isEmpty_iff.mp noQ,List.isEmpty_iff.mp noC,
                    (check_empty_reads_actual_primitive455 ..).mp builtin,hTree,bTree,(role_present_exact p).mp role,
                    (GeneralSourceMetadataRoles291.check_exact _).mp valid,localChecked.1,localChecked.2,(q.exact _ _).mp translated⟩
              else none
            else none
          else none
        else none
      else none
    else none
  | _,_,_ => none

theorem exact_same_written_header_replays456 {p q d} (a : AuthoredHeader p q d) :
    readHeader p q d a.only a.emptyKey = some a := by
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
  have header := a.checked
  have stated := (local_author_bits_exact455 ..).mpr
    ⟨a.covered,header.signature,header.identified,header.produced,header.outputOnly,header.scope⟩
  have mem : a.clause ∈ d.requirements := a.requirement ▸ List.mem_cons_self
  have desc : recordDescent412 d.head a.clause.arguments = true := by
    obtain ⟨h,c⟩ := header.countsCovered a.clause mem
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨h,c⟩,
        (checkSmaller_exact ..).mpr (header.paterson a.clause mem)⟩,header.conservative a.clause mem⟩
  unfold readHeader
  split
  · rename_i t c input head req args
    have et := List.singleton_inj.mp (head.symm.trans a.head)
    have ec := List.singleton_inj.mp (req.symm.trans a.requirement)
    have eq := List.singleton_inj.mp (args.symm.trans a.argv)
    subst t; subst c; subst input
    simp only [shape,builtin,role,valid,stated,desc,dite_true]
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

end Yulang.GeneralDeclarativeI65.I72.RoutedQueryHeader456

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RoutedNominalPoint456
open GeneralDeclarativeWitnessConstructorModes357 (Use SourceMode)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry Current)
open GeneralNominalCenteredHeadMatExpressions (Expr application translate translateMany)
open GeneralSourceMetadataRows291 (interpretation primitives invariants)
open GeneralDeclarationPatterns (Pattern)

theorem legacy_application_cannot_read_original_declared_mode456
    {cur : Current} {key arity params}
    (u : Use cur.environment key arity) (mode : u.mode = .declared params)
    (arguments : List Expr) :
    application (authoredRegistry cur).constructors
      (interpretation cur.environment.source.snapshot) key arguments = none := by
  have raw : SourceMode cur.environment key (.declared params) := mode ▸ u.sourced
  cases raw with
  | declared own noPrimitive noOldName =>
    have hp : (interpretation cur.environment.source.snapshot).primitives key = none := noPrimitive
    have hi : (interpretation cur.environment.source.snapshot).invariantNominal key = false := noOldName
    simp [application,hp,hi,Option.bind]
    cases (authoredRegistry cur).constructors key with
    | none => rfl
    | some ctor => simp

theorem legacy_translation_cannot_read_the_same_declared_application456
    {cur : Current} {key arity params}
    (u : Use cur.environment key arity) (mode : u.mode = .declared params)
    (arguments : List Pattern) :
    translate (authoredRegistry cur).constructors
      (interpretation cur.environment.source.snapshot) (.app key arguments) = none := by
  rw [translate.eq_def]
  cases read : translateMany (authoredRegistry cur).constructors
      (interpretation cur.environment.source.snapshot) arguments with
  | none => simp [read,Option.bind]
  | some got =>
    simpa [read,Option.bind] using legacy_application_cannot_read_original_declared_mode456 u mode got

theorem legacy_translation_stops_at_an_authored_declared_record_field456
    {cur : Current} {key arity params} (u : Use cur.environment key arity)
    (mode : u.mode = .declared params) (label : Nat) (args : List Pattern) (tail : Pattern) :
    translate (authoredRegistry cur).constructors
      (interpretation cur.environment.source.snapshot) (.record label (.app key args) tail) = none := by
  rw [translate.eq_def]
  simp [legacy_translation_cannot_read_the_same_declared_application456 u mode args,Option.bind]

end Yulang.GeneralDeclarativeI65.I72.RoutedNominalPoint456
