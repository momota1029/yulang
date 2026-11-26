import Yulang.GeneralDeclarativeI65I74ListFrameRule449
import Yulang.GeneralDeclarativeWitnessNestedDescent360

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.WhereSites450
open ListSites449 ListSites449.Frame
open GeneralDeclarationPatterns
open GeneralDeclarations (Clause)
open GeneralDeclarativeWitnessChecks349
open GeneralDeclarativeWitnessNestedDescent360 (fromChain actualOrigin origin descent descent_witness)
open GeneralDeclarativeWitnessModeCoverage357 (checkDecl declaration_exact)
open RetainedSplit446.LocalHeader (localSignature local_signature_exact446 identifiers_exact446 produced_exact446 lexical_only_exact446 named_scopes_exact446)
open Yulang.GeneralDeclarativeI65
open Checker408 (Problem Result)
open GeneralDeclarations (Declaration DeclarationChecked)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered)
open List410 (ExactEscapeWire)


def literalClause (c : Clause) : Bool :=
  match c.arguments with
  | [.var _] => c.outputs.isEmpty
  | _ => false

theorem literalClause_exact (c : Clause) :
    literalClause c = true ↔ ∃ b, c.arguments = [.var b] ∧ c.outputs = [] := by
  unfold literalClause
  split
  · rename_i b written
    simp [written,List.isEmpty_iff]
  · rename_i missing
    simp only [Bool.false_eq_true, false_iff,not_exists,not_and]
    intro b e _
    exact missing b e

theorem literal_written_binder_is_a_chain {s args heads} (a : AuthoredFrame s args heads)
    {b : Nat} (named : b ∈ variablesArgs (normalizeArgs heads)) :
    ∃ key, .app key [.var b] ∈ heads := by
  induction a with
  | nil => simp [normalizeArgs,variablesArgs] at named
  | cons first tail ih =>
    rw [first.headSyntax] at named
    simp only [normalizeArgs,normalize,variablesArgs,Pattern.variables,List.append_nil,
      List.singleton_append,List.mem_cons] at named
    rcases named with same|rest
    · exact ⟨first.key,List.mem_cons.mpr (.inl (by rw [same]; exact first.headSyntax.symm))⟩
    · obtain ⟨k,hk⟩ := ih rest
      exact ⟨k,List.mem_cons_of_mem _ hk⟩

def parentHeader450 (env : GeneralDeclarativeWitnessConstructorModes357.Environment) (d : Declaration) : Bool :=
  checkDecl env d &&
    ((localSignature env.source.roles d && ids d) && ((binds d && lexical d) && names d)) &&
    (d.requirements.all literalClause && d.requirements.all (fun c => descent d.head c.arguments))

theorem parent_header_exact450 {s : GeneralDeclarativeI65.State} {args} (d : Declaration)
    (roster : AuthoredFrame s args d.head) :
    parentHeader450 s.current.environment d = true ↔
      (∀ c ∈ d.requirements, ∃ b, c.arguments = [.var b] ∧ c.outputs = []) ∧
      DeclarationCovered s.current.environment d ∧
      DeclarationChecked (authoredRegistry s.current).constructors (authoredRegistry s.current).roles d := by
  unfold parentHeader450
  simp only [Bool.and_eq_true,List.all_eq_true,literalClause_exact,
    declaration_exact,local_signature_exact446,identifiers_exact446,produced_exact446,
    lexical_only_exact446,named_scopes_exact446]
  constructor
  · rintro ⟨⟨covered,⟨⟨sig,ids⟩,⟨⟨bound,lexical⟩,scope⟩⟩⟩,literal,valid⟩
    exact ⟨literal,covered,⟨sig,ids,bound,lexical,scope,
      GeneralDeclarativeWitnessModeDeclaration357.scoped_decl covered,
      fun c k => (descent_witness (valid c k)).1,
      fun c k => (descent_witness (valid c k)).2.1,
      fun c k => (descent_witness (valid c k)).2.2.1,
      fun c k => (descent_witness (valid c k)).2.2.2⟩⟩
  · rintro ⟨literal,covered,checked⟩
    refine ⟨⟨covered,⟨⟨checked.signature,checked.identified⟩,
      ⟨⟨checked.produced,checked.outputOnly⟩,checked.scope⟩⟩⟩,literal,?_⟩
    intro c here
    rcases literal c here with ⟨b,args,noOut⟩
    have inScope : b ∈ variablesArgs (normalizeArgs d.head) :=
      checked.scope.1 c here b (by simp [args,normalizeArgs,normalize,variablesArgs,Pattern.variables])
    obtain ⟨key,source⟩ := literal_written_binder_is_a_chain roster inScope
    have chain : fromChain d.head c.arguments = true := by
      rw [args]
      apply List.any_eq_true.mpr
      exact ⟨.app key [.var b],source,by simp [actualOrigin,origin,Pattern.encode,encodeArgs,Roles.Term.size,Roles.argsSize]⟩
    have count : GeneralDeclarativeWitnessChecks349.counts d.head c.arguments = true :=
      Bool.and_eq_true_iff.mpr (checked.countsCovered c here)
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
      ⟨count,(checkSmaller_exact ..).mpr (checked.paterson c here)⟩,
      Bool.and_eq_true_iff.mpr ⟨checked.conservative c here,Bool.or_eq_true_iff.mpr (.inl chain)⟩⟩

structure ParentChoice (p : Problem) (d : Declaration) where
  only : visible p.state.core p.root = [d]
  roster : AuthoredFrame p.state.core p.root.demand.arguments d.head
  someInput : p.root.demand.arguments ≠ []
  distinct : (roster.bindings.map Prod.fst).Nodup
  authoredRole : ∃ row ∈ p.state.core.current.environment.source.roles.rows,
    row.role = p.root.demand.role
  rolesValid : GeneralSourceMetadataRoles291.Valid p.state.core.current.environment.source.roles
  checked : DeclarationChecked (authoredRegistry p.state.core.current).constructors
    (authoredRegistry p.state.core.current).roles d
  covered : DeclarationCovered p.state.core.current.environment d
  literal : ∀ c ∈ d.requirements, ∃ binder, c.arguments = [.var binder] ∧ c.outputs = []
  noOutputs : p.root.demand.outputs = []
  safe : ¬RootCycle p.state p.root

structure ParentWire where
  origins : List Nat
  certificates : List ExactEscapeWire

def readParentChoice (p : Problem) (d : Declaration)
    (scope : visible p.state.core p.root = [d]) (w : ParentWire) : Option (ParentChoice p d) := do
  let core := p.state.core
  if role : (Checker408.originalRole p).isSome = true then
    if valid : GeneralSourceMetadataRoles291.check core.current.environment.source.roles = true then
      if header : parentHeader450 core.current.environment d = true then
        if out : p.root.demand.outputs.isEmpty = true then
          if hasArg : p.root.demand.arguments ≠ [] then
            let roster ← readAuthoredFrame core p.root.demand.arguments d.head w.origins
            if unique : (roster.bindings.map Prod.fst).Nodup then
              if clear : checkSiteTable core.current.ordinary
                  (p.root.demand.arguments.map Capture.lower) w.certificates = true then
                have roleBound : ∃ row ∈ core.current.environment.source.roles.rows,
                    row.role = p.root.demand.role := by
                  cases present : Checker408.originalRole p with
                  | none => simp [present] at role
                  | some row =>
                    have actual := GeneralSourceMetadataRoles291.indexed present
                    exact ⟨row,actual.1,actual.2⟩
                let checked := (parent_header_exact450 d roster).mp header
                let safe := (inspection_safety_is_original_root_safety449 (d := d) roster.visits).mp
                  (table_only_validates_actual_safe_sites449 clear)
                some ⟨scope,roster,hasArg,unique,roleBound,
                  (GeneralSourceMetadataRoles291.check_exact _).mp valid,checked.2.2,checked.2.1,
                  checked.1,List.isEmpty_iff.mp out,safe⟩
              else none
            else none
          else none
        else none
      else none
    else none
  else none

theorem independent_list_frame_replays_exactly450 {p : Problem} {d : Declaration}
    (a : ParentChoice p d) : ∃ w, readParentChoice p d a.only w = some a := by
  obtain ⟨indices,replayed⟩ := independent_frame_has_exact_origin_indices449 a.roster
  have safe := (inspection_safety_is_original_root_safety449 (d := d) a.roster.visits).mpr a.safe
  obtain ⟨cuts,pass⟩ := (exact_per_site_finite_witnesses449 p.state.core.current.ordinary
    (p.root.demand.arguments.map Capture.lower)).mp safe
  refine ⟨⟨indices,cuts⟩,?_⟩
  have role := Opaque448.original_role_is_read448 a.authoredRole (p := p)
  have header := (parent_header_exact450 d a.roster).mpr ⟨a.literal,a.covered,a.checked⟩
  have valid := (GeneralSourceMetadataRoles291.check_exact _).mpr a.rolesValid
  have out : p.root.demand.outputs.isEmpty = true := List.isEmpty_iff.mpr a.noOutputs
  unfold readParentChoice
  rw [dite_eq_left role,dite_eq_left valid,dite_eq_left header,dite_eq_left out,
    dite_eq_left a.someInput,replayed]
  simp only [Bind.bind,Option.bind,dite_eq_left a.distinct,dite_eq_left pass]

def ParentChoice.head {p d} (a : ParentChoice p d) : SourceHead p.state.core p.root d :=
  .ordered a.roster.capture (distinct_authored_bindings_have_exact_list_heads449 a.roster a.distinct)

def ParentChoice.candidate {p d} (a : ParentChoice p d) : AuthoredCandidate p.state.core p.root d :=
  ⟨by simp [a.only],a.covered,a.checked.signature,a.head⟩

def ParentChoice.tape {p d} (a : ParentChoice p d) :
    CandidateTape p.state.core p.root (visible p.state.core p.root) :=
  a.only.symm ▸ .next (.matched a.candidate) .nil

theorem actual_single_declaration_list_frame_is_settled450 {p d} (a : ParentChoice p d) :
    TapedMatch p.state.core p.root a.tape d := by
  have localShape : ∀ rows (h : rows = [d]),
      let t : CandidateTape p.state.core p.root rows := h.symm ▸ .next (.matched a.candidate) .nil
      t.waits = false ∧ t.live = [d] := by
    intro rows h
    cases h
    exact ⟨rfl,rfl⟩
  exact ⟨a.safe,(localShape _ a.only).1,(localShape _ a.only).2⟩

end Yulang.GeneralDeclarativeI65.I72.WhereSites450
