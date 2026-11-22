import Yulang.GeneralDeclarativeWitnessChecks349
import Yulang.GeneralDeclarativeWitnessTargets349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessHeader349
open GeneralDeclarations (Checked Declaration DeclarationChecked)
open GeneralSourceMetadataBareBundle291 (forget)
open GeneralSourceMetadataBundle291 (SourceBundle registry)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralNominalCenteredHeadWFSource (Coverage DeclarationCovered declaration_scoped)
open GeneralDeclarativeOutputSource323 (Declared)
open GeneralDeclarativeWitnessProblem349 (Problem first first_sound)
open GeneralDeclarativeWitnessChecks349 (ids identified binds produced lexical output_only names scope_sound checkedDescent descent_parts)

def checksDecl (s : SourceBundle) (d : Declaration) : Bool :=
  (GeneralDeclarativeWitnessSignature349.checks s.roles d && ids d) &&
  ((binds d && lexical d) &&
   (names d && d.requirements.all (fun c => checkedDescent d.head c.arguments)))

theorem decl_checked {s : SourceBundle} {d : Declaration}
    (cov : DeclarationCovered (registry s).constructors (interpretation s.snapshot) d)
    (ok : checksDecl s d = true) :
    DeclarationChecked (registry s).constructors (registry s).roles d := by
  obtain ⟨top,tail⟩ := GeneralDeclarativeWitnessProblem349.splitAnd ok
  obtain ⟨sg,ix⟩ := GeneralDeclarativeWitnessProblem349.splitAnd top
  obtain ⟨a,b⟩ := GeneralDeclarativeWitnessProblem349.splitAnd tail
  obtain ⟨pc,lx⟩ := GeneralDeclarativeWitnessProblem349.splitAnd a
  obtain ⟨ns,cs⟩ := GeneralDeclarativeWitnessProblem349.splitAnd b
  have forClause (c) (h : c ∈ d.requirements) := descent_parts (List.all_eq_true.mp cs c h)
  exact ⟨GeneralDeclarativeWitnessSignature349.checked_signature sg,identified ix,produced pc,
    output_only lx,scope_sound ns,declaration_scoped cov,
    fun c h => (forClause c h).1,fun c h => (forClause c h).2.1,
    fun c h => (forClause c h).2.2.1,fun c h => (forClause c h).2.2.2⟩

def checkedRegistry (s : SourceBundle) : Bool :=
  decide (s.declarations.map Declaration.id).Nodup && s.declarations.all (checksDecl s)

theorem registry_checked {s : SourceBundle}
    (cov : Coverage (registry s) (interpretation s.snapshot)) (ok : checkedRegistry s = true) :
    Checked (registry s) := by
  obtain ⟨keys,checked⟩ := GeneralDeclarativeWitnessProblem349.splitAnd ok
  exact ⟨of_decide_eq_true keys,fun d h => decl_checked (cov.1 d h) (List.all_eq_true.mp checked d h)⟩

/-- The proof-free first slice of a witness, containing only the
reported request list. The independent input bundle is never supplied
by this witness. No checker outcome at this layer is a diagnosis. -/
structure Header where
  outputs : List GeneralSourceState.Output

def replay (p : Problem) (w : Header) : Option SourceBundle := do
  let s ← first p
  if checkedRegistry s && GeneralDeclarativeWitnessTargets349.same_requests p w.outputs
    then some s else none

def check (p : Problem) (w : Header) : Bool := (replay p w).isSome

theorem replay_sound {p : Problem} {w : Header} {s : SourceBundle} (success : replay p w = some s) :
    forget s = p.source ∧ Checked (registry s) ∧ Coverage (registry s) (interpretation s.snapshot) ∧
      Declared (registry s) p.demand ∧ w.outputs = p.demand.outputs := by
  unfold replay at success
  cases started : first p with
  | none => simp [started] at success
  | some data =>
    rw [started] at success
    change (if checkedRegistry data && GeneralDeclarativeWitnessTargets349.same_requests p w.outputs then some data else none) =
      some s at success
    split at success
    · rename_i accepted
      cases Option.some.inj success
      obtain ⟨same,_,_,cover,named⟩ := first_sound started
      obtain ⟨checks,targets⟩ := GeneralDeclarativeWitnessProblem349.splitAnd accepted
      exact ⟨same,registry_checked cover checks,cover,named,
        (GeneralDeclarativeWitnessTargets349.exact_targets _ _).mp targets⟩
    · cases success

theorem sound {p : Problem} {w : Header} (success : check p w = true) :
    ∃ s, forget s = p.source ∧ Checked (registry s) ∧
      Coverage (registry s) (interpretation s.snapshot) ∧ Declared (registry s) p.demand ∧
      w.outputs = p.demand.outputs := by
  unfold check at success
  cases built : replay p w with
  | none => simp [built] at success
  | some s => exact ⟨s,replay_sound built⟩

end Yulang.GeneralDeclarativeWitnessHeader349
