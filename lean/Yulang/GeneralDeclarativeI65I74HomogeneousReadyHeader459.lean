import Yulang.GeneralDeclarativeI65I74NestedIdenticalTagProjection459
import Yulang.GeneralDeclarativeI65I74ProjectedReadyHeader459

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.HomogeneousWrittenHeader459
open GeneralDeclarationPatterns
open GeneralDeclarations (Declaration Clause)
open NestedIdenticalTagProjection459

open GeneralDeclarativeWitnessDeclaredState357 (Current authoredRegistry)
open GeneralDeclarativeWitnessClassifyVariance357 (DeclarationReady)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open RecordTrail455 (localAuthorBits local_author_bits_exact455)
open RecordTree455

/-- Scope, evidence and DeclarationReady talk about the real unchanged
declaration. Projected spelling is a stable auxiliary witness only. -/
structure ExactHomogeneousHeader (cur : Current) (d : Declaration) (c : Clause) (empty : Nat) : Prop where
  original : d.requirements = [c]
  cover : DeclarationCovered cur.environment d
  sig : d.Signature (authoredRegistry cur).roles
  identified : d.Identified
  produced : d.Produced
  outputs : d.OutputOnly
  scope : d.Scoped
  head : WrittenArgs empty (projectedArgs d.head)
  body : WrittenArgs empty c.arguments
  small : Smaller d.head c.arguments

def checkHomogeneousHeader (cur : Current) (d : Declaration) (c : Clause) (key : Nat) : Bool :=
  localAuthorBits cur.environment d && checkTrees key (projectedArgs d.head) &&
    checkTrees key c.arguments && checkSmaller d.head c.arguments

theorem homogeneous_header_is_finite_exact459 {cur d c empty} (same : d.requirements = [c]) :
    checkHomogeneousHeader cur d c empty = true ↔ ExactHomogeneousHeader cur d c empty := by
  constructor
  · intro ok
    simp only [checkHomogeneousHeader,Bool.and_eq_true] at ok
    obtain ⟨⟨⟨source,head⟩,body⟩,small⟩ := ok
    obtain ⟨covered,sig,id,prod,only,scope⟩ := (local_author_bits_exact455 ..).mp source
    exact ⟨same,covered,sig,id,prod,only,scope,(checkTrees_exact ..).mp head,
      (checkTrees_exact ..).mp body,(checkSmaller_exact ..).mp small⟩
  · intro found
    simp only [checkHomogeneousHeader,Bool.and_eq_true]
    exact ⟨⟨⟨(local_author_bits_exact455 ..).mpr ⟨found.cover,found.sig,found.identified,found.produced,found.outputs,found.scope⟩,
      (checkTrees_exact ..).mpr found.head⟩,(checkTrees_exact ..).mpr found.body⟩,(checkSmaller_exact ..).mpr found.small⟩

theorem homogeneous_header_proves_actual_original_ready459 {cur d c empty}
    (found : ExactHomogeneousHeader cur d c empty) :
    DeclarationReady (authoredRegistry cur) d := by
  refine ⟨found.sig,found.identified,found.produced,found.outputs,found.scope,
    GeneralDeclarativeWitnessModeDeclaration357.scoped_decl found.cover,?_⟩
  intro k chosen
  rw [found.original] at chosen
  cases List.mem_singleton.mp chosen
  refine ⟨found.small,?_⟩
  have smaller : Smaller (projectedArgs d.head) c.arguments := by
    unfold Smaller
    rw [original_normal_counts_are_preserved459 d.head]
    exact found.small
  have stable := written_tree_paterson_stable_under_all_captures455 found.head found.body smaller
  intro capture
  have same := stable capture
  unfold Smaller at same ⊢
  rw [original_capture_counts_are_preserved459] at same
  exact same




end Yulang.GeneralDeclarativeI65.I72.HomogeneousWrittenHeader459

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.HomogeneousReadyHeader459
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



open IdenticalTagProjection459 (pruneRepeatedTagsArgs)
open NestedIdenticalTagProjection459 (projectedArgs)
open HomogeneousWrittenHeader459
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
  admissibleHead : WrittenArgs emptyKey (projectedArgs d.head)
  admissibleBody : WrittenArgs emptyKey clause.arguments
  authoredRole : ∃ row ∈ p.state.core.current.environment.source.roles.rows,
    row.role = p.root.demand.role
  rolesValid : GeneralSourceMetadataRoles291.Valid p.state.core.current.environment.source.roles
  preserved : ExactHomogeneousHeader p.state.core.current d clause emptyKey
  genuinelyRepeated : projectedArgs d.head ≠ d.head
  oldWrittenSpellingUnavailable : checkTrees emptyKey (pruneRepeatedTagsArgs d.head) = false
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

def verifyProjectedSyntax (p : Problem) (d : Declaration) (a : Capture) (c : Clause) (key : Nat) : Bool :=
  (decide (a.lower = a.center ∧ a.center = a.upper) &&
    (p.root.demand.outputs.isEmpty && c.outputs.isEmpty)) &&
  (checkTrees key (projectedArgs d.head) && checkTrees key c.arguments)

def readReadyHeader (p : Problem) (q : QueryDecoder p.state.core) (d : Declaration) (only : visible p.state.core p.root = [d])
    (key : Nat) : Option (AuthoredHeader p q d) :=
  let cur := p.state.core.current
  match h : d.head, req : d.requirements, args : p.root.demand.arguments with
  | [t],[c],[a] =>
    if shape : verifyProjectedSyntax p d a c key = true then
      if builtin : checkEmpty p ⟨key,0,[],[]⟩ = true then
        if role : (Checker408.originalRole p).isSome = true then
          if valid : GeneralSourceMetadataRoles291.check cur.environment.source.roles = true then
            if ready : checkHomogeneousHeader cur d c key = true then
              if changed : projectedArgs d.head ≠ d.head then
                if absentOld : checkTrees key (pruneRepeatedTagsArgs d.head) = false then
                  match translated : q.decode (normalize t) with
                  | none => none
                  | some expr => by
                    obtain ⟨arity,tree⟩ := splitAnd shape
                    obtain ⟨pt,none⟩ := splitAnd arity
                    obtain ⟨noQ,noC⟩ := splitAnd none
                    obtain ⟨hr,br⟩ := splitAnd tree
                    have core := (homogeneous_header_is_finite_exact459 req).mp ready
                    exact some ⟨key,t,c,a,expr,only,h,req,args,of_decide_eq_true pt,
                      List.isEmpty_iff.mp noQ,List.isEmpty_iff.mp noC,
                      (check_empty_reads_actual_primitive455 ..).mp builtin,
                      (checkTrees_exact ..).mp hr,(checkTrees_exact ..).mp br,(role_present_exact p).mp role,
                      (GeneralSourceMetadataRoles291.check_exact _).mp valid,core,changed,absentOld,(q.exact _ _).mp translated⟩
                else none
              else none
            else none
          else none
        else none
      else none
    else none
  | _,_,_ => none

theorem actual_original_homogeneous_header_replays459 {p q d} (a : AuthoredHeader p q d) :
    readReadyHeader p q d a.only a.emptyKey = some a := by
  have exactQuery := (q.exact _ _).mpr a.translated
  have shape : verifyProjectedSyntax p d a.arg a.clause a.emptyKey = true := by
    unfold verifyProjectedSyntax
    rw [decide_eq_true a.atCenter,List.isEmpty_iff.mpr a.noGoalOutputs,
      List.isEmpty_iff.mpr a.noWhereOutputs,(checkTrees_exact ..).mpr a.admissibleHead,
      (checkTrees_exact ..).mpr a.admissibleBody]
    rfl
  have builtin := (check_empty_reads_actual_primitive455 ..).mpr a.actualEmpty
  have role := (role_present_exact _).mpr a.authoredRole
  have valid := (GeneralSourceMetadataRoles291.check_exact _).mpr a.rolesValid
  have ready := (homogeneous_header_is_finite_exact459 a.requirement).mpr a.preserved
  unfold readReadyHeader
  split
  · rename_i t c input head req args
    have et := List.singleton_inj.mp (head.symm.trans a.head)
    have ec := List.singleton_inj.mp (req.symm.trans a.requirement)
    have eq := List.singleton_inj.mp (args.symm.trans a.argv)
    subst t; subst c; subst input
    simp only [shape,builtin,role,valid,ready,dite_true]
    rw [dite_eq_left a.genuinelyRepeated,dite_eq_left a.oldWrittenSpellingUnavailable]
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

theorem exact_homogeneous_header_supplies_original_ready459
    {p q d} (h : AuthoredHeader p q d) :
    GeneralDeclarativeWitnessClassifyVariance357.DeclarationReady
      (authoredRegistry p.state.core.current) d :=
  homogeneous_header_proves_actual_original_ready459 h.preserved




theorem original_homogeneous_head_has_independent_exact_projection459
    {p q d} (actual : AuthoredHeader p q d) :
    ∃ projected, NestedIdenticalTagProjection459.ProjectionArgs d.head projected ∧
      WrittenArgs actual.emptyKey projected ∧ projected ≠ d.head :=
  ⟨projectedArgs d.head,NestedIdenticalTagProjection459.projected_real_source_arguments_have_derivation459 d.head,
    actual.admissibleHead,actual.genuinelyRepeated⟩

theorem independent_original_projection_recovers_the_guarded_closed_head459
    {p q d} (actual : AuthoredHeader p q d) {projected}
    (chosen : NestedIdenticalTagProjection459.ProjectionArgs d.head projected) :
    WrittenArgs actual.emptyKey projected ∧ projected ≠ d.head := by
  have selected := NestedIdenticalTagProjection459.projection_args_preserve_their_exact_data_read459 chosen
  exact ⟨selected ▸ actual.admissibleHead,selected ▸ actual.genuinelyRepeated⟩

end Yulang.GeneralDeclarativeI65.I72.HomogeneousReadyHeader459
