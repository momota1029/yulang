import Yulang.GeneralDeclarativeI65I74RecordSpine455
import Yulang.GeneralDeclarativeI65I74RetainedLocalHeader446
import Yulang.GeneralDeclarativeI65I74OpaqueWholeEntry448

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RecordTrail455
open Yulang.GeneralDeclarativeI65
open GeneralDeclarationPatterns
open GeneralDeclarations (Declaration Clause DeclarationChecked)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCenteredHeadMatExpressions (Expr application)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered checkDecl declaration_exact)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralDeclarativeWitnessChecks349 (ids binds lexical names counts)
open GeneralDeclarativeWitnessProblem349 (splitAnd)
open RetainedSplit446.LocalHeader
open RecordK2412 (recordDescent412)
open Checker408 (Problem)

structure Form where
  empty : Nat
  binder : Nat
  writtenHead : List Nat
  writtenWhere : List Nat

def Form.head (f : Form) : List Pattern := [chain f.empty f.writtenHead (.var f.binder)]
def Form.condition (f : Form) : List Pattern := [chain f.empty f.writtenWhere (.var f.binder)]
def Form.query (f : Form) : Expr := queryChain f.writtenHead f.binder

def localAuthorBits (env : Environment) (d : Declaration) : Bool :=
  ((checkDecl env d && localSignature env.source.roles d) && ids d) &&
    ((binds d && lexical d) && names d)

theorem local_author_bits_exact455 (env : Environment) (d : Declaration) :
    localAuthorBits env d = true ↔ DeclarationCovered env d ∧
      d.Signature (GeneralSourceMetadataRoles291.roleTable env.source.roles) ∧
      d.Identified ∧ d.Produced ∧ d.OutputOnly ∧ d.Scoped := by
  simp [localAuthorBits,Bool.and_eq_true,declaration_exact,local_signature_exact446,
    identifiers_exact446,produced_exact446,lexical_only_exact446,named_scopes_exact446,and_assoc]

theorem all_declaration_checks_on_literal_chain455
    {p : Problem} {d : Declaration} {c : Clause} {f : Form}
    (only : d.requirements = [c]) (head : d.head = f.head) (cond : c.arguments = f.condition)
    (strict : f.writtenWhere.length < f.writtenHead.length)
    (body : localAuthorBits p.state.core.current.environment d = true)
    (desc : recordDescent412 d.head c.arguments = true) :
    DeclarationCovered p.state.core.current.environment d ∧
    DeclarationChecked (authoredRegistry p.state.core.current).constructors
      (authoredRegistry p.state.core.current).roles d := by
  obtain ⟨cov,sig,ident,emit,lex,lexscope⟩ := (local_author_bits_exact455 ..).mp body
  obtain ⟨front,conservative⟩ := splitAnd desc
  obtain ⟨cover,less⟩ := splitAnd front
  refine ⟨cov,⟨sig,ident,emit,lex,lexscope,
    GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cov,?_,?_,?_,?_⟩⟩
  all_goals intro clause present; rw [only] at present; cases List.mem_singleton.mp present
  · exact splitAnd cover
  · exact (checkSmaller_exact ..).mp less
  · exact conservative
  · rw [head,cond]
    exact actual_closed_chain_where_prefix_strict455 _ _ _ _ strict

def EmptyConstructor (p : Problem) (f : Form) : Prop :=
  application (authoredRegistry p.state.core.current).constructors
    (interpretation p.state.core.current.environment.source.snapshot) f.empty [] =
      some (.primitive .emptyRecord [])

structure HeaderData (p : Problem) (d : Declaration) where
  form : Form
  clause : Clause
  arg : Capture
  only : visible p.state.core p.root = [d]
  requirement : d.requirements = [clause]
  argv : p.root.demand.arguments = [arg]
  lower_eq_center : arg.lower = arg.center
  center_eq_upper : arg.center = arg.upper
  noGoalOutputs : p.root.demand.outputs = []
  noWhereOutputs : clause.outputs = []
  head : d.head = form.head
  body : clause.arguments = form.condition
  depth : 2 ≤ form.writtenHead.length
  desc : form.writtenWhere.length < form.writtenHead.length
  empty : EmptyConstructor p form
  authoredRole : ∃ row ∈ p.state.core.current.environment.source.roles.rows,
    row.role = p.root.demand.role
  rolesValid : GeneralSourceMetadataRoles291.Valid p.state.core.current.environment.source.roles
  covered : DeclarationCovered p.state.core.current.environment d
  checked : DeclarationChecked (authoredRegistry p.state.core.current).constructors
    (authoredRegistry p.state.core.current).roles d

theorem header_translates_the_actual_normalized_head455 {p d} (a : HeaderData p d) :
    GeneralNominalCenteredHeadMatExpressions.translateMany (authoredRegistry p.state.core.current).constructors
      (interpretation p.state.core.current.environment.source.snapshot)
      (normalizeArgs d.head) = some [a.form.query] := by
  rw [a.head]
  simp [Form.head,Form.query,normalizeArgs,GeneralNominalCenteredHeadMatExpressions.translateMany,
    actual_closed_chain_translates_without_depth_bound455 _ _ _ _ a.empty]

def checkShape (p : Problem) (d : Declaration) (c : Clause) (a : Capture) (f : Form) : Bool :=
  decide ((a.lower = a.center ∧ a.center = a.upper) ∧
    (d.head = f.head ∧ c.arguments = f.condition) ∧
    (2 ≤ f.writtenHead.length ∧ f.writtenWhere.length < f.writtenHead.length)) &&
    p.root.demand.outputs.isEmpty && c.outputs.isEmpty

def checkEmpty (p : Problem) (f : Form) : Bool :=
  match application (authoredRegistry p.state.core.current).constructors
      (interpretation p.state.core.current.environment.source.snapshot) f.empty [] with
  | some (.primitive .emptyRecord []) => true
  | _ => false

theorem check_empty_reads_actual_primitive455 (p : Problem) (f : Form) :
    checkEmpty p f = true ↔ EmptyConstructor p f := by
  unfold EmptyConstructor checkEmpty
  split <;> simp_all

private theorem actual_role_exact (p : Problem) :
    (Checker408.originalRole p).isSome = true ↔
      ∃ row ∈ p.state.core.current.environment.source.roles.rows, row.role = p.root.demand.role := by
  constructor
  · intro did
    cases known : Checker408.originalRole p with
    | none => simp [known] at did
    | some row =>
      have a := GeneralSourceMetadataRoles291.indexed known
      exact ⟨row,a.1,a.2⟩
  · exact Opaque448.original_role_is_read448 (p := p)

def readHeader (p : Problem) (d : Declaration) (only : visible p.state.core p.root = [d])
    (f : Form) : Option (HeaderData p d) :=
  match req : d.requirements, argv : p.root.demand.arguments with
  | [c],[a] =>
    if found : checkShape p d c a f = true then
      if empty : checkEmpty p f = true then
        if role : (Checker408.originalRole p).isSome = true then
          if valid : GeneralSourceMetadataRoles291.check p.state.core.current.environment.source.roles = true then
            if metadata : localAuthorBits p.state.core.current.environment d = true then
              if desc : recordDescent412 d.head c.arguments = true then by
                obtain ⟨pair,noC⟩ := splitAnd found
                obtain ⟨main,noQ⟩ := splitAnd pair
                have sym := of_decide_eq_true main
                have builtin := (check_empty_reads_actual_primitive455 _ _).mp empty
                have decl := all_declaration_checks_on_literal_chain455 req sym.2.1.1 sym.2.1.2 sym.2.2.2 metadata desc
                exact some ⟨f,c,a,only,req,argv,sym.1.1,sym.1.2,List.isEmpty_iff.mp noQ,List.isEmpty_iff.mp noC,
                  sym.2.1.1,sym.2.1.2,sym.2.2.1,sym.2.2.2,builtin,(actual_role_exact p).mp role,
                  (GeneralSourceMetadataRoles291.check_exact _).mp valid,decl.1,decl.2⟩
              else none
            else none
          else none
        else none
      else none
    else none
  | _,_ => none

theorem independent_actual_header_replays455 {p d} (a : HeaderData p d) :
    readHeader p d a.only a.form = some a := by
  have shape : checkShape p d a.clause a.arg a.form = true := by
    unfold checkShape
    rw [decide_eq_true ⟨⟨a.lower_eq_center,a.center_eq_upper⟩,⟨a.head,a.body⟩,a.depth,a.desc⟩,
      List.isEmpty_iff.mpr a.noGoalOutputs,List.isEmpty_iff.mpr a.noWhereOutputs]
    rfl
  have empty := (check_empty_reads_actual_primitive455 p a.form).mpr a.empty
  have role := (actual_role_exact p).mpr a.authoredRole
  have valid := (GeneralSourceMetadataRoles291.check_exact _).mpr a.rolesValid
  have checked := a.checked
  have metadata := (local_author_bits_exact455 ..).mpr
    ⟨a.covered,checked.signature,checked.identified,checked.produced,checked.outputOnly,checked.scope⟩
  have c : a.clause ∈ d.requirements := a.requirement ▸ List.mem_singleton.mpr rfl
  have desc : recordDescent412 d.head a.clause.arguments = true := by
    obtain ⟨front,back⟩ := checked.countsCovered a.clause c
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr ⟨front,back⟩,
        (checkSmaller_exact ..).mpr (checked.paterson a.clause c)⟩,checked.conservative a.clause c⟩
  unfold readHeader
  split
  · rename_i c q req argv
    have ec := List.singleton_inj.mp (req.symm.trans a.requirement)
    have eq := List.singleton_inj.mp (argv.symm.trans a.argv)
    subst c
    subst q
    simp only [shape,empty,role,valid,metadata,desc,dite_true]
  · rename_i no
    exact (no _ _ a.requirement a.argv).elim

end Yulang.GeneralDeclarativeI65.I72.RecordTrail455
