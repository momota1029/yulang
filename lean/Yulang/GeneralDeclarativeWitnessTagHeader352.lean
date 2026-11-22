import Yulang.GeneralDeclarativeWitnessRecordHeader350
import Yulang.GeneralDeclarativeWitnessHeader349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessTagHeader352
open GeneralDeclarations (Checked Declaration DeclarationChecked)
open GeneralDeclarationPatterns (Pattern StableSmaller counted substArgs normalizeArgs normalize hide encodeArgs)
open GeneralSourceMetadataBareBundle291 (forget)
open GeneralSourceMetadataBundle291 (SourceBundle registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralNominalCenteredHeadWFSource (Coverage DeclarationCovered declaration_scoped)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeWitnessProblem349 (Problem first first_sound splitAnd)
open GeneralDeclarativeWitnessHeader349 (Header)
open GeneralDeclarativeWitnessChecks349 (ids identified binds produced lexical output_only names scope_sound descent_parts counts)
open GeneralDeclarationPatterns (lowerArgs checkSmaller checkSmaller_exact)
open GeneralDeclarativeWitnessTargets349 (same_requests exact_targets)

/-- Substitution/normalization can remove occurrences in the *tail*,
but not the distinguished outer payload. No descent certificate may
count a binder merely because it used to occur in a hidden tail. -/
theorem payload_descent (label binder : Nat) (rest : Pattern) :
    StableSmaller [.record label (.var binder) rest] [.var binder] := by
  intro capture
  constructor
  · simp only [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,
      Roles.argsSize,Roles.Term.size]
    omega
  · intro q
    simp only [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,
      Roles.argsOccurrences,Roles.Term.occurrences]
    omega

theorem variant_payload_descent (tag binder : Nat) :
    StableSmaller [.variant tag (.var binder)] [.var binder] := by
  intro capture
  constructor
  · simp [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,
      Roles.argsSize,Roles.Term.size] <;> omega
  · intro q
    simp [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,
      Roles.argsOccurrences,Roles.Term.occurrences]

theorem wrapped_payload_descent (tag constructor binder : Nat) :
    StableSmaller [.variant tag (.app constructor [.var binder])] [.var binder] := by
  intro capture
  constructor
  · simp [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,
      Roles.argsSize,Roles.Term.size] <;> omega
  · intro q
    simp [counted,substArgs,Pattern.subst,normalizeArgs,normalize,encodeArgs,Pattern.encode,
      Roles.argsOccurrences,Roles.Term.occurrences]

def tagDescent (head child : List Pattern) : Bool :=
  match head, child with
  | [.variant _ (.var k)], [.var v] => decide (k = v)
  | [.variant _ (.app _ [.var k])], [.var v] => decide (k = v)
  | _,_ => false

theorem tag_descent_sound {head child : List Pattern} (ok : tagDescent head child = true) :
    StableSmaller head child := by
  unfold tagDescent at ok
  split at ok
  · rename_i tag k v
    cases of_decide_eq_true ok
    exact variant_payload_descent tag k
  · rename_i tag box k v
    cases of_decide_eq_true ok
    exact wrapped_payload_descent tag box k
  · cases ok

def extraDescent (head child : List Pattern) : Bool :=
  GeneralDeclarativeWitnessRecordHeader350.extraDescent head child || tagDescent head child

theorem extra_sound {head child : List Pattern} (ok : extraDescent head child = true) :
    StableSmaller head child :=
  (GeneralDeclarativeWitnessProblem349.splitOr ok).elim
    GeneralDeclarativeWitnessRecordHeader350.extra_sound tag_descent_sound

def checkDescent (head child : List Pattern) : Bool :=
  (counts head child && checkSmaller head child) &&
  (CheckedRoles.checkCondition (lowerArgs (normalizeArgs head)) ⟨0,counted child⟩ &&
    (GeneralDeclarativeWitnessChecks349.stableSchema head child || extraDescent head child))

theorem descent {head child : List Pattern} (ok : checkDescent head child = true) :
    GeneralDeclarationPatterns.CountsCovered head child ∧ GeneralDeclarationPatterns.Smaller head child ∧
      GeneralDeclarationPatterns.ConservativeSmaller head child ∧ StableSmaller head child := by
  obtain ⟨a,b⟩ := splitAnd ok
  exact ⟨splitAnd (splitAnd a).1,(checkSmaller_exact ..).mp (splitAnd a).2,(splitAnd b).1,
    (GeneralDeclarativeWitnessProblem349.splitOr (splitAnd b).2).elim
      GeneralDeclarativeWitnessChecks349.stable_sound extra_sound⟩

def checksDecl (s : SourceBundle) (d : Declaration) : Bool :=
  (GeneralDeclarativeWitnessSignature349.checks s.roles d && ids d) &&
  ((binds d && lexical d) &&
   (names d && d.requirements.all (fun c => checkDescent d.head c.arguments)))

theorem decl_checked {s : SourceBundle} {d : Declaration}
    (cov : DeclarationCovered (registry s).constructors (interpretation s.snapshot) d)
    (ok : checksDecl s d = true) :
    DeclarationChecked (registry s).constructors (registry s).roles d := by
  obtain ⟨top,tail⟩ := splitAnd ok
  obtain ⟨sg,ix⟩ := splitAnd top
  obtain ⟨a,b⟩ := splitAnd tail
  obtain ⟨pc,lx⟩ := splitAnd a
  obtain ⟨ns,cs⟩ := splitAnd b
  have forClause (c) (h : c ∈ d.requirements) := descent (List.all_eq_true.mp cs c h)
  exact ⟨GeneralDeclarativeWitnessSignature349.checked_signature sg,identified ix,produced pc,
    output_only lx,scope_sound ns,declaration_scoped cov,
    fun c h => (forClause c h).1,fun c h => (forClause c h).2.1,
    fun c h => (forClause c h).2.2.1,fun c h => (forClause c h).2.2.2⟩

def checkedRegistry (s : SourceBundle) : Bool :=
  decide (s.declarations.map Declaration.id).Nodup && s.declarations.all (checksDecl s)

theorem registry_checked {s : SourceBundle} (cov : Coverage (registry s) (interpretation s.snapshot))
    (ok : checkedRegistry s = true) : Checked (registry s) :=
  ⟨of_decide_eq_true (splitAnd ok).1,fun d h => decl_checked (cov.1 d h) (List.all_eq_true.mp (splitAnd ok).2 d h)⟩

def replay (p : Problem) (w : Header) : Option SourceBundle := do
  let s ← first p
  if checkedRegistry s && same_requests p w.outputs then some s else none

theorem replay_first {p : Problem} {w : Header} {s : SourceBundle}
    (ok : replay p w = some s) :
    first p = some s ∧ checkedRegistry s = true ∧ same_requests p w.outputs = true := by
  unfold replay at ok
  cases found : first p with
  | none => simp [found] at ok
  | some current =>
    rw [found] at ok
    change (if _ then some current else none) = some s at ok
    split at ok
    · rename_i verified
      cases Option.some.inj ok
      exact ⟨rfl,(splitAnd verified).1,(splitAnd verified).2⟩
    · cases ok

theorem replay_sound {p : Problem} {w : Header} {s : SourceBundle}
    (ok : replay p w = some s) :
    forget s = p.source ∧ Checked (registry s) ∧ Coverage (registry s) (interpretation s.snapshot) ∧
      Declared (registry s) p.demand ∧ w.outputs = p.demand.outputs := by
  obtain ⟨base,valid,outputs⟩ := replay_first ok
  obtain ⟨matchSource,_,_,coverage,declared⟩ := first_sound base
  exact ⟨matchSource,registry_checked coverage valid,coverage,declared,(exact_targets _ _).mp outputs⟩

end Yulang.GeneralDeclarativeWitnessTagHeader352
