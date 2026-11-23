import Yulang.GeneralDeclarativeWitnessConstructorModes357
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessModeCoverage357
open GeneralDeclarativeWitnessConstructorModes357 (Environment Use Mode SourceMode readMode readUse)
open GeneralSourceMetadataBundle291 (registry)
open GeneralSourceMetadataRows291 (constructors primitives invariants)
open GeneralDeclarationPatterns (Pattern)
open GeneralDeclarations (Declaration)
open GeneralSourceMetadataRoles291 (roleTable index)
open GeneralSourceMetadataFiniteLookup291 (get some_sound)

theorem available {e : Environment} {name m} (supported : SourceMode e name m) :
    ∃ seen, readMode e name = some seen ∧ seen.val = m := by
  cases supported with
  | primitive actual absent =>
    unfold readMode
    split
    · simp_all
    · split
      · rename_i _ got
        have eq := Option.some.inj (got.symm.trans actual)
        subst_vars
        exact ⟨_,rfl,rfl⟩
      · simp_all
  | invariant actual absent =>
    have noPrimitive := GeneralSourceMetadataRows291.exclusive e.source.snapshot.rows name actual
    change primitives e.source.snapshot name = none at noPrimitive
    unfold readMode
    split
    · simp_all
    · split
      · simp_all
      · rw [dite_eq_left actual]
        exact ⟨_,rfl,rfl⟩
  | declared actual primitive invariant =>
    unfold readMode
    split
    · rename_i ps got
      have eq := Option.some.inj (got.symm.trans actual)
      subst ps
      split
      · exact ⟨_,rfl,rfl⟩
      · simp_all
    · simp_all

theorem readUse_exact {e : Environment} {name arity} :
    (readUse e name arity).isSome = true ↔ Nonempty (Use e name arity) := by
  constructor
  · intro h
    cases run : readUse e name arity with
    | none => simp [run] at h
    | some hit => exact ⟨hit⟩
  · rintro ⟨known⟩
    obtain ⟨mode,modeRead,eq⟩ := available known.sourced
    have values : known.declared.name = name ∧ known.current.name = name ∧
        known.current.parameters = known.declared.parameters ∧ known.declared.parameters.length = arity ∧
        GeneralDeclarativeWitnessConstructorModes357.Layout known.declared mode.val :=
      ⟨known.declaredName,known.currentName,known.sameLayout,known.exactArity,eq.symm ▸ known.kinded⟩
    unfold readUse
    rw [dite_eq_left known.noDefault]
    split
    · rename_i a b ha hb
      have ea := Option.some.inj (ha.symm.trans known.actual)
      have eb := Option.some.inj (hb.symm.trans known.snapshot)
      subst a
      subst b
      rw [modeRead]
      simp only [bind, Option.bind, dite_eq_left values, Option.isSome_some]
    · rename_i impossible
      exact False.elim ((impossible _ _ known.actual) known.snapshot)

mutual
def Covers (e : Environment) : Pattern → Prop
  | .var _ => True
  | .app key args => Nonempty (Use e key args.length) ∧ CoversList e args
  | .record _ first rest | .join first rest => Covers e first ∧ Covers e rest
  | .variant _ value => Covers e value

def CoversList (e : Environment) : List Pattern → Prop
  | [] => True
  | a::as => Covers e a ∧ CoversList e as
end

mutual
def pattern (e : Environment) : Pattern → Bool
  | .var _ => true
  | .app key args => (readUse e key args.length).isSome && patterns e args
  | .record _ a b | .join a b => pattern e a && pattern e b
  | .variant _ a => pattern e a

def patterns (e : Environment) : List Pattern → Bool
  | [] => true
  | a::as => pattern e a && patterns e as
end

mutual
theorem pattern_exact (e : Environment) (p : Pattern) : pattern e p = true ↔ Covers e p := by
  cases p with
  | var n => simp [pattern,Covers]
  | app key args => simp [pattern,Covers,readUse_exact,patterns_exact e args]
  | record label f r => simp [pattern,Covers,pattern_exact e f,pattern_exact e r]
  | variant tag f => simp [pattern,Covers,pattern_exact e f]
  | join f r => simp [pattern,Covers,pattern_exact e f,pattern_exact e r]
termination_by sizeOf p

theorem patterns_exact (e : Environment) (ps : List Pattern) : patterns e ps = true ↔ CoversList e ps := by
  cases ps with
  | nil => simp [patterns,CoversList]
  | cons a as => simp [patterns,CoversList,pattern_exact e a,patterns_exact e as]
termination_by sizeOf ps
end

def DeclarationCovered (e : Environment) (d : Declaration) : Prop :=
  CoversList e d.head ∧
  (∀ c ∈ d.requirements,CoversList e c.arguments ∧ ∀ o ∈ c.outputs,Covers e o.rhs) ∧
  ∀ o ∈ d.associated,Covers e o.rhs

def checkDecl (e : Environment) (d : Declaration) : Bool :=
  patterns e d.head &&
    d.requirements.all (fun c => patterns e c.arguments && c.outputs.all (fun o => pattern e o.rhs)) &&
    d.associated.all (fun o => pattern e o.rhs)

theorem declaration_exact (e : Environment) (d : Declaration) :
    checkDecl e d = true ↔ DeclarationCovered e d := by
  simp [checkDecl,DeclarationCovered,List.all_eq_true,pattern_exact,patterns_exact,and_assoc]

mutual
def TermCovered (e : Environment) : Roles.Term → Prop
  | .var _ => True
  | .app key values => Nonempty (Use e key values.length) ∧ TermsCovered e values

def TermsCovered (e : Environment) : List Roles.Term → Prop
  | [] => True
  | f::r => TermCovered e f ∧ TermsCovered e r
end

mutual
def term (e : Environment) : Roles.Term → Bool
  | .var _ => true
  | .app key values => (readUse e key values.length).isSome && terms e values

def terms (e : Environment) : List Roles.Term → Bool
  | [] => true
  | f::r => term e f && terms e r
end

mutual
theorem term_exact (e : Environment) (t : Roles.Term) : term e t = true ↔ TermCovered e t := by
  cases t with
  | var => simp [term,TermCovered]
  | app _ values => simp [term,TermCovered,readUse_exact,terms_exact e values]
termination_by sizeOf t

theorem terms_exact (e : Environment) (ts : List Roles.Term) : terms e ts = true ↔ TermsCovered e ts := by
  cases ts with
  | nil => simp [terms,TermsCovered]
  | cons f r => simp [terms,TermsCovered,term_exact e f,terms_exact e r]
termination_by sizeOf ts
end

def DefaultsCovered (e : Environment) : Prop :=
  ∀ r name body, (roleTable e.source.roles r).assoc name = some (some body) → TermCovered e body

def actualOutputs (e : Environment) : Prop :=
  ∀ row ∈ e.source.roles.rows,∀ name body,(name,some body) ∈ row.outputs → TermCovered e body

theorem every_actual_default {e : Environment} (written : actualOutputs e) : DefaultsCovered e := by
  intro r name body active
  unfold roleTable at active
  cases found : get r (index e.source.roles) with
  | none => simp [found,GeneralSourceMetadataRoles291.fallback] at active
  | some row =>
    simp only [found,Option.map_some,Option.getD_some,GeneralSourceMetadataRoles291.RoleRow.interpret] at active
    exact written row (GeneralSourceMetadataRoles291.indexed found).1 name body (some_sound active)

theorem all_written_defaults {e : Environment} (well : GeneralSourceMetadataRoles291.Valid e.source.roles)
    (haveDefault : DefaultsCovered e) : actualOutputs e := by
  intro row visible name body member
  apply haveDefault row.role name body
  unfold roleTable
  rw [GeneralSourceMetadataRoles291.lookup_row well visible]
  change get name row.outputs = some (some body)
  exact GeneralSourceMetadataFiniteLookup291.some_complete (well.2 row visible) member

def Coverage (e : Environment) : Prop :=
  (∀ decl ∈ e.source.declarations, DeclarationCovered e decl) ∧ DefaultsCovered e

def check (e : Environment) : Bool :=
  e.source.declarations.all (checkDecl e) && e.source.roles.rows.all
    (fun row => row.outputs.all fun n => (n.2.map (term e)).getD true)

theorem check_exact {e : Environment} (well : GeneralSourceMetadataRoles291.Valid e.source.roles) :
    check e = true ↔ Coverage e := by
  simp only [check,Coverage,Bool.and_eq_true,List.all_eq_true,declaration_exact]
  apply and_congr_right
  intro _
  constructor
  · intro all
    apply every_actual_default
    intro row visible name body inRow
    simpa only [Option.map_some,Option.getD_some,term_exact] using all row visible (name,some body) inRow
  · intro all row visible entry hit
    cases entry with
    | mk name rhs =>
      cases rhs with
      | none => rfl
      | some body => exact (term_exact e body).mpr (all_written_defaults well all row visible name body hit)

end Yulang.GeneralDeclarativeWitnessModeCoverage357
