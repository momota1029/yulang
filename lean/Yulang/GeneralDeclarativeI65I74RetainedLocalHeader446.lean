import Yulang.GeneralDeclarativeI65I74RetainedSplitEntry446

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.RetainedSplit446.LocalHeader
open GeneralDeclarations
open GeneralDeclarationPatterns
open GeneralDeclarativeWitnessDeclaredState357 (Current authoredRegistry)
open GeneralDeclarativeWitnessConstructorModes357 (Environment)
open GeneralDeclarativeWitnessModeCoverage357 (DeclarationCovered checkDecl declaration_exact)
open GeneralSourceMetadataRoles291 (RoleSource roleTable index)
open GeneralSourceMetadataFiniteLookup291 (get some_sound)
open GeneralDeclarativeWitnessSignature349 (declaredEq declared_eq checksClause checkedEntry)
open GeneralDeclarativeWitnessChecks349 (ids identified binds produced lexical output_only names scope_sound rhsScope)

/-- Enumerate keys of the selected real role row, but read the
effective body through its actual lookup. A shadowed duplicate is not
presumed to be the effective declaration. -/
def localCovers (roles : RoleSource) (d : Declaration) : Bool :=
  match get d.role (index roles) with
  | none => true
  | some row => row.outputs.all (fun e =>
      ((get e.1 row.outputs).map (fun body => checkedEntry d (e.1,body))).getD true)

theorem actual_entry_test_exact446 (d : Declaration) (name : Nat) (body : Option Roles.Term) :
    checkedEntry d (name,body) = true ↔
      (∃ eq ∈ d.associated, eq.name = name) ∨ body.isSome = true := by
  constructor
  · intro test
    rcases Bool.or_eq_true_iff.mp test with fromBody|explicit
    · exact .inr fromBody
    · exact .inl (List.mem_map.mp (of_decide_eq_true explicit))
  · intro agrees
    apply Bool.or_eq_true_iff.mpr
    rcases agrees with explicit|fromBody
    · exact .inr (decide_eq_true (List.mem_map.mpr explicit))
    · exact .inl fromBody

theorem local_outputs_are_exact446 (roles : RoleSource) (d : Declaration) :
    localCovers roles d = true ↔
    ∀ name body, (roleTable roles d.role).assoc name = some body →
      (∃ eq ∈ d.associated, eq.name = name) ∨ body.isSome = true := by
  unfold localCovers
  cases found : get d.role (index roles) with
  | none =>
    constructor
    · intro _ name body h
      unfold roleTable at h
      rw [found] at h
      cases h
    · intro _; rfl
  | some row =>
    constructor
    · intro checked name body h
      unfold roleTable at h
      rw [found] at h
      have lookup : get name row.outputs = some body := h
      have verified := List.all_eq_true.mp checked (name,body) (some_sound lookup)
      apply (actual_entry_test_exact446 d name body).mp
      simpa only [lookup,Option.map_some,Option.getD_some] using verified
    · intro contains
      apply List.all_eq_true.mpr
      intro e atRow
      cases lookup : get e.1 row.outputs with
      | none => rfl
      | some body =>
        have linked : (roleTable roles d.role).assoc e.1 = some body := by
          unfold roleTable
          rw [found]
          exact lookup
        simpa only [lookup,Option.map_some,Option.getD_some] using
          (actual_entry_test_exact446 d e.1 body).mpr (contains e.1 body linked)

theorem clause_signature_exact446 (roles : Roles.RoleDecls) (c : Clause) :
    checksClause roles c = true ↔ c.Signature roles := by
  simp [checksClause,Clause.Signature,declared_eq]

def localSignature (roles : RoleSource) (d : Declaration) : Bool :=
  (decide (d.head.length = (roleTable roles d.role).arity) &&
    d.associated.all (declaredEq (roleTable roles) d.role)) &&
  (localCovers roles d && d.requirements.all (checksClause (roleTable roles)))

theorem local_signature_exact446 (roles : RoleSource) (d : Declaration) :
    localSignature roles d = true ↔ d.Signature (roleTable roles) := by
  simp [localSignature,Declaration.Signature,declared_eq,local_outputs_are_exact446,
    clause_signature_exact446, and_assoc]

theorem identifiers_exact446 (d : Declaration) : ids d = true ↔ d.Identified := by
  simp [ids,Declaration.Identified]

theorem produced_exact446 (d : Declaration) : binds d = true ↔ d.Produced := by
  constructor
  · exact produced
  · intro emit
    apply List.all_eq_true.mpr
    intro b inDecl
    obtain ⟨clause,found,clauseId,row,atClause,rhsId,rhs⟩ := emit b inDecl
    exact List.any_eq_true.mpr ⟨clause,found,Bool.and_eq_true_iff.mpr
      ⟨decide_eq_true clauseId,List.any_eq_true.mpr ⟨row,atClause,decide_eq_true ⟨rhsId,rhs⟩⟩⟩⟩

theorem lexical_only_exact446 (d : Declaration) : lexical d = true ↔ d.OutputOnly := by
  simp [lexical,Declaration.OutputOnly]

theorem named_scopes_exact446 (d : Declaration) : names d = true ↔ d.Scoped := by
  simp [names,Declaration.Scoped,rhsScope]

/-- This path checks one actual where-free candidate. Its condition
is exactly the C445 local evidence already demanded of that same
candidate, not the unrelated conservative checks on other roles. -/
def selectedHeader (env : Environment) (d : Declaration) : Bool :=
  (d.requirements.isEmpty && checkDecl env d) &&
    ((localSignature env.source.roles d && ids d) && ((binds d && lexical d) && names d))

theorem selected_header_exact446 (s : Current) (d : Declaration) :
    selectedHeader s.environment d = true ↔
      d.requirements = [] ∧ DeclarationCovered s.environment d ∧
      DeclarationChecked (authoredRegistry s).constructors (authoredRegistry s).roles d := by
  constructor
  · intro test
    unfold selectedHeader at test
    obtain ⟨first,rest⟩ := Bool.and_eq_true_iff.mp test
    obtain ⟨whereFree,covered⟩ := Bool.and_eq_true_iff.mp first
    obtain ⟨signAndIds,scopes⟩ := Bool.and_eq_true_iff.mp rest
    obtain ⟨sig,id⟩ := Bool.and_eq_true_iff.mp signAndIds
    obtain ⟨emissions,scope⟩ := Bool.and_eq_true_iff.mp scopes
    obtain ⟨br,lx⟩ := Bool.and_eq_true_iff.mp emissions
    have noWhere := List.isEmpty_iff.mp whereFree
    have cv := (declaration_exact s.environment d).mp covered
    refine ⟨noWhere,cv,⟨(local_signature_exact446 _ _).mp sig,identified id,produced br,
      output_only lx,scope_sound scope,GeneralDeclarativeWitnessModeDeclaration357.scoped_decl cv,
      ?_,?_,?_,?_⟩⟩
    all_goals intro c atDecl; rw [noWhere] at atDecl; cases atDecl
  · rintro ⟨noWhere,cv,h⟩
    unfold selectedHeader
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
      ⟨List.isEmpty_iff.mpr noWhere,(declaration_exact s.environment d).mpr cv⟩,
      Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
        ⟨(local_signature_exact446 _ _).mpr h.signature,(identifiers_exact446 _).mpr h.identified⟩,
        Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
          ⟨(produced_exact446 _).mpr h.produced,(lexical_only_exact446 _).mpr h.outputOnly⟩,
          (named_scopes_exact446 _).mpr h.scope⟩⟩⟩

end Yulang.GeneralDeclarativeI65.I72.RetainedSplit446.LocalHeader
